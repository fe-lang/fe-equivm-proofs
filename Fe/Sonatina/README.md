# Sonatina IR in Lean

A semantics of Sonatina IR, the backend IR of the Fe compiler, tested against the bytecode compiled
from it, and a design for splitting a bytecode certificate at that IR. Nothing here is trusted: the
interpreter is a contract model like any other, so an error in it makes a proof or a comparison
fail, not pass.

| Module | Contents |
| --- | --- |
| `Syntax.lean` | IR modules, functions, blocks, instructions; `Sidecar` (IR and compiled sections) |
| `Parse.lean` | the reader of Sonatina's text form and of sidecar JSON; `sonatina_sidecar` |
| `Interp.lean` | the interpreter in `FeM`; `Sidecar.model : ContractModel` |
| `Refine.lean` | `Implements`, and the composition `RefinesOn.of_implements` |
| `Diff.lean` | IR against bytecode, with `Fe/EVM/Diff.lean` and `Generate.lean` |
| `Fixtures/` | sidecars of FeConstant, FeScalarStore, FeERC20 and the deposit contract |

`scripts/SonatinaDiff.lean` runs the fixtures and the committed `.sona` files against the pinned
bytecode; `scripts/audit_sonatina.sh <fe checkout>` runs every contract of Fe's test fixtures and of
this repository, on its Fe tests and on generated calls. EVMLean has no `CLZ` (Osaka's opcode 0x1e, which
Sonatina emits for `clz`), so on a contract that counts leading zeros the bytecode halts with an
invalid instruction where the IR returns the count.

## What the IR is, as Fe uses it

Fe lowers MIR to a Sonatina `Module` (`crates/codegen/src/sonatina/lower_runtime`): struct and enum
types, globals, functions, and objects. A function is SSA: blocks of instructions over typed values
(`i1` to `i256`, pointers, structs, arrays, enums), phis at block heads, one terminator per block.
An object has sections (`init`, `runtime`), each naming an entry function, included functions, data
globals and embedded sections (`embed .runtime as &C_runtime`). The instruction set
(`crates/ir/src/inst`, Sonatina `bd20fac`) has the generic arithmetic, comparison, cast and
memory instructions (`mload`, `mstore`, `gep`, `alloca`, `insert_value`, `obj.*`, `enum.*`,
`sym_addr`, `sym_size`), control flow (`jump`, `br`, `br_table`, `call`, `return`,
`unreachable`), and about 60 EVM instructions (`evm_sload`, `evm_calldata_load`, `evm_malloc`,
`evm_call`, `evm_log3`, `evm_return`, `evm_revert`, the EVM's own division and `exp`, …).

The text form is what `ModuleWriter` prints (`crates/ir/src/ir_writer.rs`), and Sonatina's
parser (`crates/parser/src/sonatina.pest`) reads it back. Sonatina has no structured
serialization (no serde).

The committed `.sona` files (`FeProofs/{ERC20,Deposit,WETH9}`) are the output of
`fe build --emit ir` at the listed Fe commits: rebuilding with Fe `22b156fff` (ERC20) and
`aa5244d43` (Deposit, WETH9) reproduces both them and the pinned `creation.hex`/`runtime.hex`
byte for byte. That IR is not, strictly, the IR the bytecode came from: `--emit ir` compiles the
whole runtime package as one module (`emit_runtime_package_sonatina_ir_optimized`), the bytecode
compiles each object in its own module (`IsolatedObjectCompiler`). For these single-contract
files the two are the same text. FeConstant and FeScalarStore have no committed `.sona`.

`fe build --emit sidecar` (Fe branch `sidecar`) closes the gap: it captures the module from the
`EvmCompile` that produces the bytecode, right before `compile()`, and writes it with the bytes and
symbol table of each section of the result (`<Contract>.sidecar.json`). The fixtures here are such
files, from the `sidecar` branch, whose Sonatina pin is `aa5244d43`'s: FeConstant, FeScalarStore
and the deposit contract compile to the pinned bytecode, FeERC20 does not (it is pinned at an older
Fe).

## The subset and its semantics

`Syntax.lean` covers what the certified contracts use: integer arithmetic, comparisons, overflow
reporting arithmetic (`uaddo`), `clz`, `ctz`, casts, `select`, word `mload`/`mstore`, `memzero`,
`evm_malloc`, structs and arrays by `insert_value`/`extract_value`, `sym_addr`/`sym_size`,
`evm_keccak256_words`, calls, and every EVM instruction the model library has a primitive for:
storage, transient storage, calldata, code, logs, the environment, `gas`, message calls and
creations. Other instructions (`gep`, `alloca`, `obj.*`, `enum.*`, narrow memory accesses), object
reference types, and any use of a global or an enum are parse errors; enum and global
declarations are skipped.

`Interp.lean` runs it in `FeM`, the monad of exported models, over EVMLean's state; every EVM
instruction is the model library's primitive (`sload`, `call`, `logData`, …). Values are typed
integers held unsigned below `2 ^ bits`, or lists of struct fields. Each call and each block
entered takes fuel; a run out of fuel, or one that reaches something undefined (`unreachable`, an
ill-typed operand, an entry function that returns), does not terminate, which agrees with no EVM
result. Where Sonatina leaves a choice: `undef` reads as zero, division by zero gives zero,
`evm_malloc` gives fresh zeroed memory at the end of memory and above every constant-address range
the module accesses, and `sym_addr`/`sym_size` read the compiled section's symbol table, which the
IR does not determine. The second rule is Sonatina's: compiler-managed memory is kept out of every
fixed range a section accesses (`scan_fixed_reservations`, `isa/evm/prepare.rs`), which rejects a
fixed-address access of dynamic length unless it is the payload of the `evm_return` or
`evm_revert` that follows. The IR's documentation does not say so; the first corpus run, with
allocation from address zero, disagreed on four contracts that store a pointer at address 0 while
the allocation there is live.

`Sidecar.model` is the contract model of the IR: `runtime` runs the `runtime` section's entry,
`init` the `init` section's, which reads its arguments from the running code and returns the
whole deployed code.

## How the backend turns IR into bytecode

From `crates/codegen/src` of Sonatina `bd20fac`, after `EvmCompile::optimize()`:

- **More IR passes, per section.** `prepare_section` (`isa/evm/prepare.rs`) runs `EvmPipeline`
  (`isa/evm/pipeline.rs`) on a copy of the module for each section: constant lowering with
  specialization of functions into new ones and dead-argument elimination, SCCP, aggregate ABI and
  type legalization, aggregate cleanup, memory legalization and pointer escape analysis, a round
  of GVN, LICM, load-store and checked-arithmetic elimination, keccak-words lowering, and promotion
  of small non-escaping `evm_malloc`s. The printed post-optimization IR is therefore not literally
  what is lowered: arities, function sets and memory instructions change.
- **Machine IR.** `lower_section_to_machine` builds a new module of `i256` machine instructions
  with fresh ids (`FuncMachineMap` maps the section IR to it, then is dropped); allocas and mallocs
  become addresses there. Machine passes (SCCP, GVN, ADCE, CFG cleanup), switch lowering into
  comparison trees, copy coalescing, and stackify edge splitting follow.
- **Stack.** `StackifyBuilder` (`stackalloc/stackify`) gives each block an entry template
  `params ++ transfer` (phi results, then live-in values); a single-predecessor block inherits its
  predecessor's stack. Values beyond `DUP16` reach spill to scratch words at 0x00/0x20 or to arena
  objects. Only the per-instruction actions survive; the entry stacks are private.
- **Memory.** `memory_plan.rs`: free-memory pointer at 0x40, dynamic stack pointer at 0x80, static
  arena from 0xa0 or lower (`choose_arena_base`, from the fixed addresses the IR touches). Each
  malloc is placed `Fixed` or on the heap (`MallocPlacement`); the section entry stores the initial
  free pointer when heap mallocs exist. Recursive functions get dynamic frames. The plan
  (`EvmPreparedSection`) is dropped after linking.
- **Calls.** Internal calls jump with `[args…, continuation]` on the stack; returns swap the results
  under the return address and jump. No inlining after `optimize()`.
- **Layout.** Functions in a call-graph order with the section entry at offset 0; blocks in reverse
  post-order with trampolines aliased away and fallthroughs rearranged; `JUMPDEST` only where a jump
  lands. After emission, identical blocks are merged, shared tails outlined into section units, and
  identical private functions merged. A section is `[code][units][data][embeds]`; `sym_addr` and
  `sym_size` are push fixups resolved from the section's symbol table.
- **Observability.** `with_observability` records a pc map (pc range, function, machine block,
  machine instruction, post-optimization provenance where stamped); `with_symbol_table` the
  offsets and sizes of functions, globals, embeds and the section. Neither records stacks, memory
  locations or IR block pcs.

## What Fe emits already

`fe dev trace emit` writes trace facts (`crates/trace-facts`): MIR, pre- and post-optimization
Sonatina functions, blocks, CFG edges and loops, opcode names of instructions without operands,
origin edges to HIR, and per bytecode pc an edge chain to the post-optimization instruction. Its
schema has variable locations, stack samples and storage facts, which nothing produces.
`fe test --report` writes the observability pc map. `*.metadata.json` is `fe build --emit
metadata`; `*.build.json` is not written by Fe or by the scripts here (EquiVM's scaffold reads it).
No output gives the dispatch table, stack or memory contents at block entry, or the memory plan.

## How the certificates use bytecode facts

`FeProofs/ScalarStore`: `Bytecode.lean` holds the bytes and their `JUMPDEST` set; each
`RuntimeBlocks_*` theorem steps one bytecode block from an `RD` state, with its stack as an
explicit expression of the entry stack and hypotheses for the branch condition and jump target;
`Dispatch.lean` chains them along the dispatcher's path to each arm's pc under selector facts;
`Get.lean` steps the arm and rewrites memory writes and read-backs; `ModelCorrect.lean` restates
each path as a terminal (`RDret`, `RDrev`) and evaluates the model. The pcs, the per-block stack
expressions, the branch hints (`using […]`) and the memory lemmas are what the split removes from
the agent's proof.

## The split

**Bytecode implements IR.** For a sidecar `s` and hints `h`, a decision procedure
`check s h : Bool`, proved once:

```lean
theorem check_sound (hc : check s h = true) :
    RefinesOn p (s.code "runtime") s.model CalldataFits
      ∧ RefinesDeploy p (s.code "init") .empty s.model (fun _ => True)
```

**IR implements model.** Proved per contract, over SSA values and explicit loads and stores:

```lean
def Implements (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, admits I → ∃ feed', EndsAs (model.runtime.exec I (World.init σ A feed'))
    (ir.runtime.exec I (World.init σ A feed))
```

`RefinesOn.of_implements` and `RefinesDeploy.of_implements` (`Refine.lean`, proved) compose them
into the existing `RefinesOn`/`Refines` and `RefinesDeploy`. Memory may differ between the two runs
(`EndsAs`), so the IR's allocation addresses never enter the model-to-IR proof.

## The sidecar

JSON per object, from one compilation. Present now (`sidecar.rs` in Fe's codegen):

| Field | Where the compiler has it |
| --- | --- |
| `ir`: the module after `optimize()` | `EvmCompile::optimize()` in Fe's isolated object compile |
| `sections[].bytecode` | `SectionArtifact.bytes` |
| `sections[].symbols`: offset and size of `%f`, `$g`, `&embed`, `.` | `SectionArtifact.symtab` |

Proposed, each needing Sonatina to keep what it computes and drops today:

| Field | Where it is computed |
| --- | --- |
| `prepared`: the section's IR after `EvmPipeline` | the work module in `prepare_section` |
| `blocks`: per machine block its pc and the IR block it comes from | `FuncLayout.block_offsets` after `link_section`; `FuncMachineMap.blocks` |
| `stack`: per machine block the entry stack, top first, as IR values, immediates, return address or continuation | `FunctionPlanner::resolve_entry` (`stackify/driver.rs`), last stackify iteration; `FuncMachineMap.values` |
| `spills`: per value its scratch word, arena address or frame offset | `StackifyAlloc.spill_storage`, `MachineFuncPlan.obj_loc`, `spill_obj` |
| `memory`: arena base, dynamic base, initial free pointer, per malloc its placement, per alloca its address, per function frame size and free-pointer restore | `EvmSectionPlan`, `EvmFuncPlacementPlan.malloc_placements`, `MachineFuncPlan`, `EvmFunctionPlan.entry_free_ptr` |
| `merges`: blocks and functions merged or outlined after emission | `late_block_merge`, `late_section_merge`, `exact_func_merge` |

The dispatch table needs no field of its own: it is the runtime entry's `br_table` (or the
comparison tree switch lowering makes of it), located by `blocks`. The normalized statement each
block implements is its IR block.

## What is hard, and what to do first

The split point. The checker must cover everything from its input IR to bytes. From the
post-optimization IR that is the whole `EvmPipeline` (specialization, legalization, several
optimization rounds, malloc promotion) as well as stack scheduling and layout, which is far more
than "stack scheduling, layout and the memory plan". Splitting at the prepared section IR instead
leaves the checker machine lowering, stackify and layout, with the memory plan as the
allocation-to-address step; the model-to-IR proof would then be against IR the agent has not seen
in Fe's output, specialized per section. Which IR to target is the first decision; it needs
Sonatina to expose the prepared section IR and the hints above.

The memory plan: the checker must show that live objects never overlap, from placements that come
from escape analysis and liveness, and that scratch and spill words do not alias program memory.

First: expose the prepared IR, block pcs and entry stacks from Sonatina, and write the checker for
functions without planned memory (FeConstant's and FeScalarStore's runtime: their one `evm_malloc`
becomes a fixed address 0), block by block against EVMLean's `Xstep`.

## Not looked into

Enum, object and array instructions; globals and data sections; contracts that create others
(external embeds); the native and wasm backends; gas; how fast the kernel evaluates the
interpreter beyond small runs (`decide +kernel` decides a call of FeConstant's `answer()` and
FeScalarStore's `get()` in seconds).
