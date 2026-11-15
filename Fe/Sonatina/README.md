# Sonatina IR in Lean

A semantics of Sonatina IR, the backend IR of the Fe compiler, tested against the bytecode compiled
from it, and a design for splitting a bytecode certificate at that IR. Nothing here is trusted: the
interpreter is a contract model like any other, so an error in it makes a proof or a comparison
fail, not pass.

| Module | Contents |
| --- | --- |
| `Syntax.lean` | IR modules, functions, blocks, instructions; `Sidecar` (IR, sections, lowering) |
| `Parse.lean` | the reader of Sonatina's text form and of sidecar JSON; `sonatina_sidecar` |
| `Interp.lean` | the interpreter in `FeM`, under a guard of protected words; `Sidecar.model level : ContractModel` at each IR level |
| `Hints.lean` | cheap checks of the lowering record against the bytes |
| `Refine.lean` | `Implements`, and the composition `RefinesOn.of_implements` |
| `Diff.lean` | IR against bytecode, with `Fe/EVM/Diff.lean` and `Generate.lean` |
| `Plan.lean` | spill plans, the instrumented machine IR (`Func.instrument`), reload-liveness, the guard |
| `Spill.lean` | the machine IR with its memory spills (`Sidecar.spilledModel`), `machine_not_panic`, `protected_kept` |
| `FrameSafe.lean` | the spill plan of a sidecar (`Sidecar.spillPlan`, untrusted), `FrameSafe`, `frameSafe_of_noSpills`, `checkSpills`, `check`, `fixedSlotsSafe` |
| `Check*.lean` | the checker and its soundness: `check_sound`, `checkSpills_sound` (`CheckCert.lean`) |
| `SpillDiff.lean` | `FrameSafe` tested: the two models side by side (`scripts/frame_safe_diff.sh`) |
| `Fixtures/` | sidecars of FeConstant, FeScalarStore, FeERC20, the deposit contract, WETH9, a factory and others |

`scripts/SonatinaDiff.lean` runs the fixtures and the committed `.sona` files against the pinned
bytecode; `scripts/audit_sonatina.sh <fe checkout>` runs every contract of Fe's test fixtures and of
this repository, on its Fe tests and on generated calls. They run in an Osaka block, where EVMLean
has `CLZ` (opcode 0x1e, which Sonatina emits for `clz`).

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
`fe build --emit ir` at the listed Fe commits: rebuilding with Fe `51f4eee504` (ERC20) and
`aa5244d43` (Deposit, WETH9) reproduces both them and the pinned `creation.hex`/`runtime.hex`
byte for byte. That IR is not, strictly, the IR the bytecode came from: `--emit ir` compiles the
whole runtime package as one module (`emit_runtime_package_sonatina_ir_optimized`), the bytecode
compiles each object in its own module (`IsolatedObjectCompiler`). For these single-contract
files the two are the same text. FeConstant and FeScalarStore have no committed `.sona`.

`fe build --emit sidecar` (Fe branch `sidecar`) closes the gap: it captures the module from the
`EvmCompile` that produces the bytecode, right before `compile()`, and writes it with the bytes and
symbol table of each section of the result (`<Contract>.sidecar.json`). The fixtures here are such
files, from the `sidecar` branch, whose Sonatina pin is `aa5244d43`'s: FeConstant, FeScalarStore
and the deposit contract compile to the pinned bytecode, and FeERC20 to its pinned bytecode at the
commit `fe.pin` names.

## The subset and its semantics

`Syntax.lean` covers what the certified contracts use: integer arithmetic, comparisons, overflow
reporting arithmetic (`uaddo`), `clz`, `ctz`, casts, `select`, word `mload`/`mstore`, `memzero`,
`evm_malloc`, `alloca`, structs and arrays by `insert_value`/`extract_value`,
`sym_addr`/`sym_size`, `evm_keccak256_words`, calls, the machine IR's `evm_mload`/`evm_mstore`, and
every EVM instruction the model library has a primitive for: storage, transient storage, calldata,
code, logs, the environment, `gas`, message calls and creations. The same subset covers the IR
after optimization, a section's IR after the backend's pipeline and its machine IR; a value takes
the width its definition declares, so the machine IR's `i256` comparison results are words. Other
instructions (`gep`, `obj.*`, `enum.*`, narrow memory accesses) and any use of a global or an
enum are parse errors; enum and global declarations are skipped. Object reference types
(`objref<T>`, `constref<T>`) are read, with no instruction on them: a machine IR keeps the struct
types of its section IR, some with such fields. A sidecar
is read if what the checker reads is: the object declarations, and per section the bytes, symbols,
machine IR and hints. The module after optimization (`Sidecar.module`) and a section's IR after
the pipeline (`Lowering.source`) are `none` where they are outside the subset, and the model of
that level is then stuck; the differential tests report such a sidecar as not read at that
level. Of the fevm precompile contracts, the module uses `obj.*`, `const.*`, `enum.*`, `bswap`
and `freeze`, and the section IR `gep`, none of which the interpreter has a meaning for.

`Interp.lean` runs it in `FeM`, the monad of exported models, over EVMLean's state; every EVM
instruction is the model library's primitive (`sload`, `call`, `logData`, …). Values are typed
integers held unsigned below `2 ^ bits`, or lists of struct fields. The runner is a least
fixpoint (`partial_fixpoint`, the same as exported loops): a run that loops for ever, or reaches
something undefined (`unreachable`, an ill-typed operand, an entry function that returns), does
not terminate, which agrees with no EVM result. (It was fuel-bounded before, which made the
checker's theorem false for a bytecode run, given enough gas, of more blocks than the fuel; the
fixpoint has no such bound, and the kernel no longer evaluates the runner.) Where Sonatina leaves a choice: `undef` reads as zero, division by zero gives zero,
`evm_malloc` gives fresh zeroed memory at the end of memory and above every constant-address range
the module accesses, and `sym_addr`/`sym_size` read the compiled section's symbol table, which the
IR does not determine. The second rule is Sonatina's: compiler-managed memory is kept out of every
fixed range a section accesses (`scan_fixed_reservations`, `isa/evm/prepare.rs`), which rejects a
fixed-address access of dynamic length unless it is the payload of the `evm_return` or
`evm_revert` that follows. The IR's documentation does not say so; the first corpus run, with
allocation from address zero, disagreed on four contracts that store a pointer at address 0 while
the allocation there is live.
`clz` is the EVM's `CLZ`, an Osaka opcode: in a block of an earlier fork the run traps there, as
the bytes halt with an invalid instruction.

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

The bytes of a section are emitted from its **machine IR**: the module `lower_section_to_machine`
builds from the section IR after the backend's pipeline, optimized again on its own. It is still
Sonatina IR, of a smaller instruction set (`EvmMachineInstSet`): each instruction is one EVM
opcode, allocations are constant addresses or free-pointer arithmetic, and every type is `i256`.
What the bytes add to it is stack scheduling, block layout and jumps, spills, internal calls, and a
few things the section entry and calls do that no instruction says: the initial free pointer,
the dynamic stack pointer and frames of recursive functions, and saving scratch objects around
calls. The certificate splits there.

Why not at the section IR before machine lowering, the IR machine lowering reads: between it and
the machine IR run the memory placement (allocations become addresses), the lowering of casts,
comparisons and aggregates, and eight optimization passes (SCCP, GVN, ADCE, known-bits, CFG
cleanup, switch lowering, copy coalescing). A checker from it would have to validate those
optimizations; one from the machine IR checks a translation that is one-to-one in instructions.
The section IR stays in the sidecar, with the map from machine blocks to its blocks, as a reading
aid and as the place to state the memory plan's intent.

The differential tests are the evidence that the machine IR, with the section entry's initial free
pointer, is what the bytes implement: it agrees with the bytecode on every comparison the IR after
optimization agrees on (see the results below).

**Bytecode implements machine IR.** A decision procedure over a sidecar `s`, proved once:

```lean
/-- Each section's bytes implement its machine IR under the section's lowering hints. -/
def check (s : Sidecar) : Bool

theorem check_sound {s : Sidecar} (hc : check s = true) :
    RefinesOn .P1 (s.code "runtime") (s.model .machine) CalldataFits
      ∧ RefinesDeploy .P1 (s.code "init") .empty (s.model .machine) (fun _ => True)
```

`s.code name` is the section's bytes, `s.model .machine` the contract model `Interp.lean` gives
the machine IR (the init section returns the whole deployed code, hence `.empty`). `true` implies
that on every message call the runtime bytes run out of gas or stack, or end as the machine IR's
run ends under some feed, at profile `P1`: same outcome, return data, accounts, logs and revert
payload. The hints are inputs to `check`, never hypotheses of `check_sound`.

**Machine IR implements model.** Proved per contract, over SSA values, explicit `evm_mload` and
`evm_mstore` at constant or free-pointer addresses, storage, calls and logs:

```lean
def Implements (model ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed, OwnerExists σ I → admits I → ∃ feed',
    EndsAs (model.runtime.exec I (World.init σ A feed')) (ir.runtime.exec I (World.init σ A feed))
```

Like `RefinesOn`, it speaks only of frames whose account exists (`OwnerExists`), as in every
frame the EVM runs: without the account a store is dropped, so a load after it reads 0, and the
compiler's forwarding of a stored value to a later load would not be sound.

`ImplementsDeploy` is the constructor's counterpart, on deployments whose code is the creation
code followed by the arguments, which the init IR reads from its own code.
`RefinesOn.of_implements` and `RefinesDeploy.of_implements` (`Refine.lean`, proved) compose the
two into `RefinesOn`/`Refines` and `RefinesDeploy` of the hand-written or exported model. The stack,
pcs and jump destinations never appear in the second half; memory addresses do, as constants.

## Test results

`SONATINA_LEVELS="post-opt source machine" scripts/audit_sonatina.sh <fe>` over Fe's test fixtures
and this repository's contracts (Fe `sonatina-hints`, Sonatina `sidecar`), one run, each level the
same 180 files, 751 Fe tests and 214 contracts with generated calls:

| IR run as the model | calls of Fe tests: agree, disagree | generated calls: agree, disagree | contracts not read |
| --- | --- | --- | --- |
| after optimization | 2697, 1 | 28197, 102 | 66 |
| section IR after the pipeline | 2689, 1 | 28065, 102 | 68 |
| machine IR | 2697, 1 | 28197, 102 | 66 |

Every disagreement is the `leading_zeros` fixture, whose bytecode uses `CLZ`, which EVMLean lacked
at the time; the export audit of the same fixture agrees since EVMLean has it.
The machine IR agrees once its run starts as the section entry's code does, with the initial free
pointer at `0x40`; without it the deposit contract's machine IR read a zero free pointer, and its
run exhausted the interpreter's memory. The 66 contracts not read use object or constant
references, enums or nested arrays. One more, `abi_bounded_input_len_untrusted`'s `Decoder`, has a
`gep` in its section IR alone, which the subset does not read: at that level its 8 test calls and
132 generated calls are not run. (The first run of this table read a sidecar only when all three of
its IRs were, which lost that contract at every level.)

`Hints.check` finds no failure in the 7914 machine blocks of the 428 sections of the corpus's
sidecars (the 34 sidecars the reader then stopped at aside). It refutes what it can see: on the six
sections of FeScalarStore, FeERC20 and the deposit contract, removing one slot from every entry
stack fails five (FeScalarStore's runtime starts every block empty), and moving every offset by a
byte fails all six. An extra slot passes, since the check is
a lower bound on what each block reads. The first corpus check found 21 machine blocks with no
place: a fallthrough block that the late section merge moves into an outlined unit is named by no
label, so `rewrite_labels` saw no redirect; Sonatina now records that redirect explicitly.

Recording the lowering changes no byte: Sonatina's `tests/lowering_record.rs` compiles its 31
fixtures at O0, O1 and Os with and without it, and the corpus test `sonatina_corpus` of Fe compares
the sidecar's sections with an ordinary compile for all 248 contracts of the corpus.

## The sidecar

JSON per object (version 2), from one compilation: `fe build --emit sidecar`, written by
`crates/codegen/src/sonatina/sidecar.rs` of Fe from Sonatina's `SectionLowering`
(`EvmCompile::with_lowering_record`, `crates/codegen/src/object/lowering.rs` and
`isa/evm/lowering_record.rs` of Sonatina). Values are `v<n>` and blocks `block<n>` of the module
named; immediates are decimal strings.

| Field | What it is | Where Sonatina has it |
| --- | --- | --- |
| `version`, `object` | format version, object name | |
| `ir` | the module after `optimize()`, shared by the sections | `EvmCompile::optimize()` |
| `sections[].bytecode`, `symbols` | the bytes; offset and size of `%f`, `$g`, `&embed`, `.` | `SectionArtifact` |
| `lowering.source_ir` | the section's IR after the backend's pipeline | `prepare_section`, before `lower_section_to_machine` |
| `lowering.machine_ir` | the machine IR the bytes are emitted from | `EvmPreparedSection`'s module |
| `lowering.code_size`, `arena_base`, `dyn_base`, `entry_free_ptr` | where code ends; the memory plan's bases; the free pointer the section entry stores | `layout.code_end()`, `EvmSectionPlan`, `EvmMemoryPlacementPlan` |
| `funcs[].offset` | where the function's code starts, null if merged into another | `ObjectLayout::func_offset` |
| `funcs[].blocks[]` | per machine block: its source blocks, offset (null if not laid out), the block it is emitted as (jump-only blocks), entry stack top first (`value`, `imm`, `func_return`, `call_return`) | `FuncMachineMap`, `FuncLayout::block_offset`, `block_aliases`, `StackifyAlloc::entry_stacks` (recorded in `plan_block`) |
| `funcs[].spills[]` | per value: memory address, frame slot or rematerialized | `StackifyAlloc::spill_storage`, `MachineFuncPlan::{obj_loc, spill_obj}` via `FinalAlloc` |
| `funcs[].frame`, `mallocs[]` | stable objects (none, at a base, dynamic frame) and word counts; each source-IR malloc's placement | `MachineFuncPlan`, `EvmFuncPlacementPlan::malloc_placements` |
| `units[]`, `redirects[]` | outlined code units; every label the late merges redirected (block to block, block to unit, function to function) | `ObjectLayout::section_units`, `VCode::redirects` (recorded in `rewrite_labels` and for fallthrough blocks moved into units) |

Not recorded yet: the save and restore of scratch objects around calls (`call_preserve`), the
dynamic stack pointer's initial value and frame layouts, and the entry stack's dead values below
the planned items (the hint says nothing about the stack below them, which the planned code never
reads). The dispatch table is the runtime entry's `br_table` or its comparison tree in the
machine IR; the blocks' offsets locate it.

## The first checker

**Class.** Sections whose functions have no spills to memory, no dynamic frames and no call
preserves: what the bytes add to the machine IR is the stack, the layout, internal calls and the
initial free pointer. Scratch and stable objects at fixed words are constant addresses in the
machine IR already. FeConstant, FeScalarStore and FeERC20 qualify in both sections (no spills, no
frames, one function a section); the deposit contract's runtime has stable objects at fixed words
and an internal call, and qualifies if its call preserves are empty, which the record does not yet
say.

**Per block.** For machine block `B` of function `F` with offset `pc_B` and entry stack `S_B`:
for every EVMLean state at `pc_B` whose stack begins with the words `S_B` names in an environment
`env` of machine values (immediates as themselves, `func_return` and `call_return` as code
addresses), with memory, storage and the rest of the stack arbitrary, running `Xstep` from it
either runs out of gas or stack, or reaches one of:
- the offset of the successor `S` that `B`'s terminator selects under `env`, with the stack
  beginning with `S_S` under `env` extended by `B`'s definitions and `S`'s phis, the same stack
  below, and the world `B`'s instructions make;
- the halt `B`'s terminator makes (`evm_return`, `evm_revert`, `evm_stop`, `evm_invalid`);
- for `return`, the continuation address with the results on top of the caller's stack.

The checker decides it by one symbolic pass over the block's bytes: an abstract stack of machine
values and constants, DUP, SWAP, POP and PUSH as bookkeeping, every other opcode matched to the next
machine instruction with the operands the abstract stack holds, jumps matched to successors by
offset (following `aliases` and `redirects`, and into outlined units). Its soundness is one lemma
per opcode class relating the abstract step to `Xstep`, proved once against EVMLean, plus the
induction over the block. Valid jump destinations come from `D_J` of the code, decided by the
kernel or `native_decide` as the existing certificates do.

**Calls.** An internal call is `PUSH cont; …; PUSH f; JUMP` with the arguments above the
continuation. The obligation of `F` is that from `pc_F` with `args ++ [ret]` above any stack it
reaches `ret` with the results above the same stack, or halts as `F`'s IR does; the call site uses
it as a summary. Recursion is by induction on the call depth, the EVM's 1024-item stack bounding
it (`Exhausted` excuses overflow). Merged functions are checked at the canonical function's
offset.

**Dispatcher.** Nothing special: the runtime entry's `br_table` is a chain of `EQ`/`JUMPI` or a
comparison tree in the machine IR, checked as any other blocks.

**Paths.** EquiVM's `RD` trace predicate states that a cursor state ends as the start state ends,
not that the frame reaches it. The checker is proved against `X`/`Xstep` directly, so its block
lemmas state reachability, and the path is cheap to keep: the list of blocks entered and the
states at `CALL`/`STATICCALL`/`DELEGATECALL`/`CREATE` boundaries, which later work on the calls a
frame makes needs.

**Composition.** `check_sound` gives `RefinesOn p runtime (s.model .machine) CalldataFits`; an
agent's `Implements model (s.model .machine) CalldataFits` and `RefinesOn.of_implements` give
`Refines` of the model. The runtime's immutables are none for these contracts
(`model.immutables = 0`).

## The checker as built

**Internal calls.** Each function of a section is checked block by block (`checkFunc`). A
function returns if its entry block reaches a `ret` (`returning`, closed under predecessors and
checked so). Its return address is a value no value of the function is (`Func.fresh`); its entry
block is entered with its arguments on top of the return address if it returns, and the section's
entry with nothing. A call is a `JUMP` to the callee's entry block with the arguments on top and,
if the callee returns, below them the address of a `JUMPDEST` at which the block's bytes go on
with the callee's results on top of what was below the arguments; a call to a function that does
not return ends the block, which ends in `unreachable`. A `ret` is a `JUMP` to the return address
with exactly the results below it.

Where the function may return from a block, the block's entry stack is the whole of its frame:
the lowering record lists the return address last, and every arrival there hands over exactly the
planned entry stack (`Frame.exact`), so the words below the frame are the caller's, untouched.
Where it cannot (a block that only halts, as a panic block), the record still lists
`func_return`, as the bottom slot of the frame, but the bytes hold more of the frame above it than
the record lists: in `Case44Bank`'s `credit`, the panic block's entry stack is `[func_return]`
while the bytes arrive there with two of the function's values above the return address. The
checker leaves `func_return` out of the planned entry stack of such a block (`Frame.slots`) and
arrives there as anywhere else, with the planned slots on top. That is sound because nothing
there reads the return address: no block the function cannot return from reaches one it can
(`returningClosed`), so none of them returns, and the proof states such a block's ending without
the return address and with any words below its stack (`func_run`, whose return disjunct needs
`Frame.exact`).

The proof (`CheckCalls.lean`) runs the IR first: `body_calls` gives, under any valuation of the
values a block defines, its events segment by segment and each callee's run on its arguments'
words (`Segs`). `segs_ends` steps the bytes segment by segment with `run_ends`, at each call
handing the callee's entry state to the function theorem at lower gas; `block_run` is one block;
`func_run` is the function theorem, by strong induction on gas and on `zeroRank`, its conclusion
`Final'`: the bytes end as the IR's run of the function does, or return to the return address
with the results' words on top of the caller's stack.

`Check.lean` is the checker. `check s` covers sections of any number of functions, each with
no memory spill (`checkSpills` admits them, below), dynamic frame, dynamic stack pointer or call
preserve, whose machine IR uses only
the pure, read, write and halting instructions `Check.lean` translates (message calls, creations
and transient storage among them), and internal calls. It accepts both sections of FeConstant, FeScalarStore and
FeERC20. On the corpus (`corpus-v3`) it accepted 387 of 430 sections without the environment and
state reads below, 31 of them with internal calls, and 391 with them; with message calls,
`blockhash` and transient storage it accepted 425, and with creations it accepts 428 and rejects
one for an instruction outside the class (`clz`, in `leading_zeros.BitsProbe`) and one for a
dynamic frame (`storage_map_recursive_views.C`, a recursive function). It matches
the bytes of every section in its class: the
mismatches were all patterns it lacked, none a wrong hint. Operands of commutative operations
are ordered by a total order on expressions (ordering only constants and values left nested
operations as the IR wrote them, which the bytes often swap); three `ISZERO`s are one, as the
bytes compute the IR's `is_zero` of a boolean; and `INVALID` halts with no operands. With the
constant branches, these raised the count from 282. `scripts/SonatinaCheck.lean` runs the
fixtures, mutations of their hints (a dropped, added or swapped entry slot, offsets moved by a
byte, a moved free pointer, dropped redirects: all rejected; moved symbols are accepted where the
section's IR reads none), mutations of WETH9's message call (a wrong gas operand, the value and
the address swapped, the return or the arguments' window off by a word: all rejected), of a
reentrancy guard's transient storage, of a factory's `create2` (a wrong value operand, the init
code without its argument words, the init code's offset and size swapped, a wrong salt, `create`
for `create2`: all rejected) and a corpus directory, a line per section and per sidecar it does
not read.

Those counts left out the 33 of the 248 sidecars of `corpus-v3` that the reader then rejected, all
on the module after optimization (enums, object references, nested arrays), which the checker
does not read. Read as now, all 248 are read, and of their 496 sections it accepts 487: the 66
sections of those 33 add 59, and 7 rejections, 5 for memory spills (`erc4337.Account`,
`erc4337.EntryPoint`, `mem_replace_take.C`, `msg_nested_array_arg.Caller`, `signature.Wallet`)
and 2 for a `br_table` without a default (`msg_enum_field.Paymaster`, `mul_div.MulDivProbe`).
`corpus-v4` is the corpus emitted again after a fix to the sidecar emitter (it named a section's
symbols against the wrong module, Fe `sonatina-hints` `50b0be4131`), with the ingot
`FeProofs/Ecrecover` and nine more sidecars: fevm's precompile contracts (ECRECOVER twice, BN254
addition and multiplication, BLAKE2 F, RIPEMD-160, modular exponentiation, identity) and
`Case44Bank`. Its 248 sidecars of `corpus-v3` are the same, byte for byte, so no verdict changed.
Of its 258 sidecars, all read, it accepts 500 of 516 sections and rejects 16: 13 for memory spills
(the runtimes of seven precompile contracts and of the ingot's ECRECOVER among them), 2 for a
`br_table` without a default and 1 for a dynamic frame (before `CLZ`, below, 499 and 17, with
`leading_zeros.BitsProbe` rejected for `clz`). The precompiles' init
sections and the identity contract's runtime are accepted. Of the 109 functions of their nine
runtimes, 26 have memory spills; of the others, 8 use `clz`, and 8 hold straight-line blocks of
hundreds of pure instructions (four-limb multiplication) whose expressions, expanded without
sharing, have millions of nodes and depths above 64. The checker did not finish them until it
numbered values (below); it now accepts all eight, in 0.2 to 0.4 s each as `lake env lean`
interprets it. The 8 that use `clz` (Modexp's four `r2`, the four `invert_256` of the ECRECOVER
contracts) are accepted since `CLZ`, in 0.6 to 1.5 s each. Until `run` took the code's search
tree and jump destinations, built once for a block (`opAt`, `validJump`), each step rebuilt the
tree, about 10 ms for 9 KB of code: the 392-instruction multiplication block took 14 s, now
0.13 s, and the corpus-v4 run of `scripts/SonatinaCheck.lean` 135 s, now 56 s. The kernel's
check of FeERC20 and WETH9 is unchanged (2.6 s and 6.2 to 6.6 s either way), presumably since
the kernel evaluated the tree once before too.

**`CLZ`.** The machine IR's `clz` is an event, its result a value as a read's is (`readOps`):
from Osaka on it is the count of leading zeros, before it a trap, as the bytes' `CLZ` is an
invalid instruction there (`clzRun`, `clz_evMoves` from EVMLean's `step_clz`). The fork is the
frame's block header's, over which the theorems quantify as over the rest of the environment,
so their statements do not change; a contract whose model counts leading zeros in every block
refines its machine IR only in Osaka blocks, which its `Implements` proof has to admit.
`scripts/SonatinaCheck.lean` checks `leading_zeros.BitsProbe` (`Fixtures/BitsProbe`), and
rejects it with `NOT` or `ISZERO` for `CLZ` in the bytes or `not` or `is_zero` for `clz` in the
IR.

**Value numbering.** The checker expanded each pure value of a block into a tree of its
definitions, at most 64 deep, without sharing: a value read twice was two copies. It now numbers
the block's values (`Canon`, `Canon.ofDefs`). Each pure value is the first value of the block
with the same operation on the same expressions (its node), or the constant the operation
folds to. Every other value is itself. The bytes' pure opcodes give the value with that node if
there is one (`Canon.intern`), so an expression is one operation on values and constants however
long the chain it stands for, and no depth bound is needed. `ISZERO` is not numbered, so that
three of them stay one (`unary`). An operation the bytes compute that no value of the block
names stays nested, its depth bounded by the run's fuel: requiring every pure opcode to give a
value, a constant or an `ISZERO` of one would reject 239 of the 499 sections of corpus-v4
accepted, the dispatchers' first comparison among them. On corpus-v4 and the fixtures every
verdict is the same as with expansion.

**The environment, balances, return data and gas.** The block header's and the chain's words
(`chainid`, `timestamp`, `number`, `gaslimit`, `basefee`, `coinbase`, `prevrandao`,
`blockhash`) are pure opcodes of the frame, as `callvalue` is. `selfbalance`, `balance` and `extcodesize` read the
accounts, `returndatasize` and `returndatacopy` the return data (a copy past its end is the model's
`.oob`, the bytes' invalid memory access), and `gas` the gas left: each is an event, its result a
fresh value. The model's `gas` reads its feed, so the proof builds the feed from the bytes' run:
`Fut s f m` says `f` is what the run from `s` supplies, at each `GAS` the word it pushes, and `m`
the calls and creations it makes, each as `XstepOk` reads it (`madeOf`); `Agree M` holds the
first of the world's feed and says the world's recorded calls followed by `m` are `M`. A run's
feed exists because each step that goes on spends gas (`fut_exists`). A `gas` on an empty feed is stuck (`Trace.stuck`), which the bytes match
only by running out of gas or stack there. These raised the corpus count from 387 to 391:
`eip712_domain.Signer` (both sections, `chainid`), `time_units.Vesting` (`timestamp`) and
`payable.PayableBox` (`selfbalance`).

**Message calls.** `call`, `staticcall` and `delegatecall` are events on their seven or six
operands, their result the success word (`call_evMoves`, `staticcall_evMoves`,
`delegatecall_evMoves`): the bytes' step runs out of gas or stack, fails under a static call
with value (`CALL` only) where the model's `call` fails `.static`, or is the model's call on the
feed's next entry, the gas cap, the substate with the callee accessed and the original account
map, which `supplyOf` gives. A call made is `Θ` on the inputs `callArgs` reads (`messageCall` equals them), the logs
the callee appended by `theta_logs_extract`; one not made, for want of funds or at depth 1024,
returns zero with empty return data. A section whose machine IR makes message calls is checked
with `K` set, so its steps need not be calm; `check_xiOk` asks that neither section make one, nor a creation.
`CALL` raised the corpus count from 391 to 399, WETH9's runtime among them; `STATICCALL` and
`DELEGATECALL` to 405, both sections of the deposit contract among them. `blockhash`, a pure
read of the frame's header and recent blocks as the model's `blockhash` is, added
`ctx.CtxBox`'s runtime (406). `tload` and `tstore` are a read and a write event as `sload` and
`sstore` are (`tload_evMoves`, `tstore_evMoves`): transient storage lives in the account map,
which `Agree` already equates, and a call's `Θ` keeps or restores it on both sides alike. They
added 19 sections (425), the three reentrancy guards that call out among them.

**Creations.** `create` and `create2` are events on their three or four operands (the value, the
init code's offset and size, and the salt), their result the new contract's address or zero
(`create_evMoves`, `create2_evMoves`): the bytes' step runs out of gas or stack (init code over
49152 bytes among it, where the model diverges), fails under a static call where the model's `createWith` fails `.static`, or is the
model's creation on the feed's next entry: all but one 64th of the gas left once the creation is
paid for (`chargedState`, the state `madeAt` builds), the substate and the original account map,
which `supplyOf` gives. A creation made, with this contract's nonce below its limit, the funds,
depth below 1024 and the init code at most 49152 bytes, is `Lambda` on the inputs `createMade`
reads, which `createWith_made` (`Fe/EVM/Calls.lean`) equates with the model's; the word is the
address if the init code succeeded and zero otherwise, the return data empty or the init code's
output, the logs it appended by `lambda_logs_extract`. One not made returns zero with empty return
data and changes nothing else (`createWith_notMade`): no nonce bump, no account, no log, no
record. A section whose machine IR creates is checked with `K` set as one that calls is
(`Inst.messages` covers both), so `check_xiOk` excludes it too. Creations added the runtimes of
`factory.Factory`, `evm_init_code_hash.Factory` and `storage_bytes_to_memory.Blob` (428); the
init code they run, an embedded section of another contract, is data to the checker, as a
callee's code is.

The verdict evaluates by the kernel (`decide +kernel`): 0.34 s of type checking for both
FeScalarStore sections and 2.6 s for FeERC20's (from 1.8 s and 259 s; 2.4 s before internal
calls), and 11.3 s for the largest section with calls, lane_pattern_writes.Store's runtime
(2,151 bytes, five functions, 33 calls). Nearly all of the old time
was the kernel reading the code: `ByteArray.get?` walks the byte list to the offset, about
14 ms at FeERC20's sizes, and EVMLean's `parseInstr` compares the byte with each pattern, about
13 ms; `validJump` ran `D_J` over the whole code (13 s), and `decode` ran at every step of every
path. `Decode.lean` decodes the code once, in one pass over its bytes with a table for the
opcodes (`instrs`, `parseByte`), into a search tree by offset (`codeTree`), which `opAt` and the
jump destinations (`jumpdests`) read; `codeTree_find` and `jumpdests_D_J` prove it agrees with
`decode` and `D_J`. Kernel evaluation needs the expressions non-nested and the checker
structurally recursive, which is why `Expr` has fixed arities.

What `check s = true` implies is stated in `CheckSound.lean` as `Sound s`, at `P1`, and proved
in `CheckCert.lean`. On the statement:

- `P1` costs little over `P0`. The proof steps the bytes by `Xstep` through EVMLean's `step_*`
  lemmas, whose states hold the substate (logs) and the output, so `P1` adds to the state
  relation only the log series against the IR world's `logs` (`step_log0`..`step_log4` against
  `logData`, which builds the same entry and fails the same way under a static call) and the
  revert payload, read from memory as the return data is. EquiVM's `RD` hides both, so a proof
  built on its cursor lemmas would conclude `P0` only.
- Running out of gas or stack is `Exhausted`, which `RefinesFor` excuses: every per-opcode step is
  an `if gas < cost then OutOfGass` or overflows to `StackOverflow`, and either error ends `Ξ`.
  The bytes' gas never meets the model's steps: the runner is a least fixpoint, so the theorem
  needs no relation between the two. With the fuel-bounded runner of stages B and C it was false
  for a run of more blocks than the fuel.
- `XstepN` is a path: the block lemmas can state that the bytes reach the successor's offset in
  `n` steps, `XstepN_X_continue` turns that into `X`, and `XOk` holds of a frame whose steps the
  class makes call-free (`stepOk` is `True` for every opcode but calls and creations).

Proved so far:

1. Operand normalization and the reading of jumps (`CheckSound.lean`): `mkOp_eval` (constant
   folding, commuted operands, `GT` as swapped `LT`, three `ISZERO`s as one) and `way_sound`,
   that the way `Exit.way` reads a conditional jump is where the exit goes (`Exit.next`) when the
   condition's value says the jump is taken, the constant-branch rule and `br_table` cases among
   it; `selected_sound` for a `br_table` with every case ruled out.
2. Per-opcode steps (`CheckStep.lean`): one `Xstep` from any code `Moves` (runs out of gas or
   stack, or moves to the next pc and stack, the frame otherwise unchanged but for gas) for every
   opcode `run` moves the stack over: `pure_moves` for all of `pureOps` at once by `opEval`,
   `dup_moves`/`swap_moves` for every `DUPn`/`SWAPn`, and `PUSHn`, `PUSH0`, `POP`, `JUMPDEST`,
   `JUMP`, `JUMPI`. The opcodes on state and the halts use EVMLean's `step_*` lemmas as they are.

3. Steps on state (`CheckEvent.lean`): `Agree` (memory, accounts, logs, return data of an EVM
   state and the
   model's world), `evRun` (an event's operation on the world) and `EvMoves`, proved for every
   read and write opcode the checker matches (`event_evMoves`), the logs included.
4. The block lemma (`CheckBlock.lean`): `run_ends`, by induction on `run`'s fuel, says a path of
   a block's bytes that `run` accepts, from a state where it is (`PathRel`) with the world
   agreeing, ends as `Ends` says for the world the block's events leave (`Trace`): out of gas or
   stack, failing under a static call where an event does, at the successor's code with its entry
   stack on top (`Reach`, 0 or more steps by `XstepN`), or halting as the block's exit does.
   `decode_append`/`D_J_append` cover the constructor's arguments after the code.
5. The IR's arithmetic (`CheckArith.lean`): `bin_word`/`cmp_word`, `BinOp.eval`/`CmpOp.eval`
   at 256 bits against `opEval`, the signed comparisons included.
6. The IR's run of a block's statements (`CheckIR.lean`, `CheckBody.lean`): `body_run` says the
   interpreter runs a checked block's statements without diverging, returning or failing at an
   event, and under any valuation of the values it defined the events trace the world (`Trace`)
   and the checker's expressions have their words (`Cons`, `expand_eval`). Numbering keeps
   every expression's word (`Canon.Valid.step`, `expand_new`); a block's run takes the valuation
   in which each value the IR does not reach before it stops has the word its instruction
   computes (`complete`), so every node of the block names a value with its word.

7. The section (`CheckSection.lean`): `block_step` joins `run_ends` and `body_run` with the IR's
   `enter` and terminator for one block; `section_run`, by induction on `X`'s fuel and
   `zeroRank`, gives the P1 agreement (`XAgrees`) of the bytes' iterator with the IR's run of the
   function from any block's start (`AtBlock`), the prologue first for the entry block, and
   `XOk` of the iterator for every condition on calls: `run_ends` gathers its steps as `Steps`,
   through states whose instruction is no call nor creation (`Calm`), or, in a section whose
   machine IR makes message calls (`Module.hasCalls`, the `K` of `Steps`), any state.
8. The checker is sound (`CheckCert.lean`): `check_sound : check s = true → Sound s`, the
   runtime and the constructor (its arguments after the code) at `P1`, and `check_xiOk`, `XiOk`
   of both frames when neither section's machine IR makes a message call or a creation
   (`Sidecar.hasCalls`). `check_xiOk_callsAt` states the frames' calls without asking that there be
   none: a frame that succeeds makes only calls satisfying `Q` when every successful run of the
   machine IR from its account map and substate records only such calls
   (`ContractModel.callsAt`), as `Fut.xOk` gives from the calls the bytes' run makes, which
   `Agree` equates with the IR's. They depend on `propext`, `Classical.choice` and `Quot.sound`
   only.

The model half for FeScalarStore (`FeProofs/ScalarStore/SonatinaRun.lean`,
`SonatinaCorrect.lean`): the interpreter's runs of the machine IR's runtime and init functions by
`ir_step` (`Run.lean`), `Implements` and `ImplementsDeploy` of the exported contract against the
machine IR through the hand-written model, and `RefinesOn.of_implements` and
`RefinesDeploy.of_implements` for the pinned runtime and creation bytecode at `P1`
(`feScalarStoreRefinesExportedP1`, `feScalarStoreDeployRefinesExportedP1`), with no
`native_decide`.

FeERC20's (`FeProofs/ERC20/Sonatina*.lean`) is the same for the pinned bytecode of `FeProofs/ERC20`
(`feERC20RefinesExportedP1`, `feERC20DeployRefinesExportedP1`). `ir_dispatch` takes the runtime
from its entry to the block of the selector's arm, one lemma per arm runs that block to its end
against the arm of the exported contract from any environment, and `runtime_endsAs` composes them.

WETH9's (`FeProofs/WETH9/Sonatina*.lean`, in progress) is of the pinned `FeProofs/WETH9/runtime.hex`
and `creation.hex` themselves: Fe `8a33d20257` (Sonatina `bd20fac3`, `-O 1`) compiles
`FeProofs/WETH9` to the same bytes as the commit `FeWETH9.build.json` names, which was checked by
rebuilding it, so the P0 and P1 certificates are of one bytecode.  Its machine IR has internal
calls (`%deposit`, `%transfer_from`, `%load` with `%stored_len` and `%revert_error`, and
`%return_value__g7f54`), each run by one callee lemma used at every call site, and keeps map keys
in its arena at 160 and 192, above the memory a call starts with (`pair_slot_gap`).  `withdraw`'s
message call is `Fe.EVM.call` on both sides; with no input and no output both are the call on
empty memory (`call_noData`, `call_noData0`), so both runs go on from one result.

Checker changes the proof needed, none changing a verdict except the third:
- `opEval` gives `SDIV`, `SMOD`, `SIGNEXTEND`, `ADDMOD`, `MULMOD` and `EXP` their values;
- the machine IR must be word-typed (the interpreter computes `add` at the operands' width);
- `sar`, `evm_sdiv` and `evm_smod` were out of the class (356 to 351 accepted sections) until
  `sar_word`, `sdiv_word` and `smod_word` proved their signed arithmetic;
- the machine IR must run where the bytes do (it is the specification; where its run is stuck the
  model diverges): each value defined once, read only after its definition in the block or from
  the entry stack and phis, a block's statements defining nothing they read at entry, successor
  phis with an operand from the block, an event's operand count its opcode's, a read defining its
  word, the entry function without parameters and its entry block without phis or predecessors;
- each pure value of a block has an expression in that block only (another block's is the word
  the run holds), and a block whose successor's code starts at its own offset is reached in no step only
  down a chain that ends (`zeroRank`);
- decoded instructions lie in the code, jump targets are in the code, and the code fits a word.

## Memory spills

Sonatina keeps some values in memory as well as on the stack (`funcs[].spills[]`, `memory`
locations): it stores such a value at its word after defining it and reloads it later. The machine
IR does not say so, and `Sound s` is about the machine IR. The spill-aware checker checks the bytes
against the machine IR with its spill stores, and its theorem asks, besides, that the stores change
nothing the contract shows:

```lean
def checkSpills (s : Sidecar) : Bool :=
  Check.checkWith s.spillPlan s && fixedSlotsSafe s s.spillPlan

def check (s : Sidecar) : Bool := Check.checkWith (fun _ => []) s && s.noSpills

theorem check_eq (s : Sidecar) : check s = (checkSpills s && s.noSpills)

theorem checkSpills_sound {s : Sidecar} (h : checkSpills s = true) (hf : FrameSafe s) : Sound s
```

`check_sound`, `check_xiOk` and `check_xiOk_callsAt` keep their statements; `check_sound` is
`checkSpills_sound` with `frameSafe_of_noSpills`. `checkSpills_xiOk` and `checkSpills_xiOk_callsAt`
are `check_xiOk` and `check_xiOk_callsAt` with `FrameSafe s` and, for each frame, the account's
existence and fitting calldata (deployments: `I.perm`) besides, as `FrameSafe` speaks only of those
frames. The certificates evaluate `check`, which reads no spill plan; its kernel time is unchanged
(FeERC20 2.5 s, WETH9 6.0 to 6.4 s, the checker before and after alternating in one process).

**The class.** Functions may spill to memory words; frame spills, dynamic and lazy frames, the
dynamic stack pointer and call preserves stay outside. `undef` operands are rejected as before (the
instrumented model never takes `undef` for a word).

**The instrumented model** (`Spill.lean`, `Plan.lean`). A `SpillPlan` gives per function each
spilled value, its word and its reload points; `Func.instrument` adds the stores the bytes make as
`evm_mstore` statements (after a definition, of parameters at entry, of a successor's phis at the
end of a jumping block, unless the operand is the phi itself or `undef`). A value is reload-live
at a point if one of its reloads is reachable before it is defined or stored again; a phi whose
operand from a predecessor is the phi itself stays live across that edge, its word holding it from
the last iteration (both ECRECOVER runtimes reload such a loop phi after the back edge). The guard
of each statement is the words of the values reload-live after it that it does not kill, and the
callers'; the runner (`runFuncG`) panics with `spillClobbered` where a statement changed one.
`Sidecar.spillPlan` (`FrameSafe.lean`, untrusted, the only place the plan's source appears) finds
the reload points by walking the bytes.

**The checker** (`Check.lean`). Each function is checked against its instrumented machine IR
(`checkSection code entry plan`, on `Module.instrument plan`), under the guard the model runs it
under:
- the spill stores are ordinary `MSTORE` events; each event and call carries the words its
  statement's guard keeps (`keep`), its position and the spilled value it stores, if any;
- the path knows words of memory (`Path.held`: word, expression, value). An `MSTORE` at a constant
  address below `2 ^ 32` adds its word and keeps the known words its guard protects or it does not
  meet; any other event or call keeps the words its guard protects (`Event.held`, `keepHeld`);
- a bytes `MLOAD` of a constant word that is not the IR's next event is a reload: the path must
  know the word, holding a value reload-live there (`Path.gap`), and the reload pushes its
  expression;
- a block starts knowing the words of its spilled values reload-live at its entry (none at the
  function's entry), which count as defined for its statements (`FuncSpill.spillIn`, `defined`);
  every arrival must know them, with the expression of the phi's operand from the block or of the
  value (`arrivesHeld`), and a successor's such value that is no phi must be defined by the block;
- the plan's values are values of the function and its sets satisfy the liveness equations
  (`liveClosed`).

**The proof.** The checker's lemmas run the guarded runner throughout (`runBodyG`, `runBlocksG`,
`runFuncG`), carrying that the run does not panic (`NoPanicAt`): then each statement runs as
itself and leaves its guard's words as they were (`guarded_exec`, `guarded_kept`), which
`Trace.ok` and `Segs.callOk` record. `PathRel` holds that each known word holds its expression's
word (`HeldRel`), kept by events (`HeldRel.event`: the read-back of a word store, and a store
leaves a word it does not meet as it was, `mstore_read_disjoint`) and by calls (`HeldRel.keep`);
`AtBlock` holds the words a block starts with. At the top, `FrameSafe` excludes the panic: a run
that ends as the machine IR's never panics, as the machine IR never does (`machine_not_panic`), so
the section's instrumented run never panics under any feed (`FrameSafe.runtime_noPanic`,
`FrameSafe.init_noPanic`); `section_sound` gives the bytes' agreement with the instrumented run,
and `FrameSafe`'s `EndsAs` takes it to the machine IR's. Soundness does not rest on the plan: a
wrong plan makes the checker reject or `FrameSafe` false.

**Relying on `FrameSafe`.** `FrameSafe s` is a statement about the machine IR and the plan alone:
on every message call `CalldataFits` admits and every deployment, the instrumented model ends as
the machine IR does. It fails where a statement writes a word whose value the bytes still reload
(a clobber, the instrumented run's panic) or where a spill store overwrites IR data that the IR
reads later (the fixed-slot miscompile). A certificate through `checkSpills_sound` owes a proof of
it; until then, the dynamic test below is the evidence. The reload-liveness change above protects
more words than the rule the dynamic test ran under (a loop phi whose operand is itself, across the
latch), so for the ECRECOVER runtimes the test covered a weaker guard.

**Fixed slots** (`fixedSlotsSafe`, a convenience). From a spill store at `0x00` or `0x20`, no
constant-address read of the IR may meet a byte of that word before the IR writes the byte, along
the function's blocks (calls not followed). It rejects Sonatina's fixed-slot spill over IR data
cheaply; soundness does not rest on it: `FrameSafe` is false for such a section. No section of
corpus-v5 with spills trips it (the 13 sidecars with a spill plan, the precompiles among them).

**Figures.** `corpus-v5` is the corpus emitted again at the current pin (Fe `bdbe390ce9`, 257
sidecars, 514 sections; corpus-v4's separate `FeProofs/Ecrecover` ingot is gone, its contract now
among `FeProofs/Precompiles`). `check` accepts 499 sections, as before the spill-aware checker,
section for section, and rejects 15; `checkSpills` accepts those 499 and the 8 runtimes with memory
spills (Blake2F, Bn254Add, Bn254Mul, Ecrecover, EcrecoverPrecompile, Ripemd160,
`erc4337.EntryPoint`, `msg_nested_array_arg.Caller`), 507, and rejects 7: Modexp,
`erc4337.Account`, `mem_replace_take.C` and `signature.Wallet`, whose lowering record spills
values the machine IR does not define (the values it gives `undef` operands, which the machine IR
keeps as `undef`), 2 `br_table`s without a default and 1 dynamic frame. Of the 27 functions with
memory spills of the precompile runtimes, 17 are accepted; the other 10 are Modexp's with `undef`
operands. The corpus run of `scripts/SonatinaCheck.lean`, plans and fixed-slot check included,
takes 2 min 14 s. The fixtures' verdicts are unchanged; `NestedArrayCaller`
(`msg_nested_array_arg.Caller`) is a fixture with spills, accepted by `checkSpills` only, and its
runtime takes the spill mutations, each rejected: two reload words swapped in the bytes, a spill
store dropped from the bytes, a store to the wrong word, a spill word changed in the record only,
a value reloaded after its word was reused (another value stored there, in the record and the
bytes), and a value reloaded where the plan does not have it live (its reload points dropped).

`scripts/frame_safe_diff.sh <sidecars>` tests `FrameSafe` where it is not proved: the two models on
the inputs of the precompile generators (`scripts/<P>Diff.lean`) and on corpus drivers. Final
counts (stopped 2026-11-15; the three slowest take minutes a run): Bn254Add 416 runs (all),
Ripemd160 208 (all), Ecrecover 35, EcrecoverPrecompile 21, Bn254Mul 4, Blake2F 4, and the corpus
drivers of `erc4337.EntryPoint` and `msg_nested_array_arg.Caller` (their Fe tests and generated
calls): no clobber panic and no disagreement in any.

Reading a failure: a `CLOBBER` line means a statement changed a word whose value the bytes reload
later, on code that is correct by every other test; the plan (a reload point missing or at the
wrong place) or the protection rule is wrong, or the bytes reuse a word too early. A `DIFFER` line
(or a harness `DISAGREE` whose model reverts with the bytes of `SPILL DIFFER`) means the spill
stores change what the machine IR shows: if the bytes match the instrumented model, they differ
from the machine IR, a Sonatina miscompile, as the fixed-slot spill over IR data at 0x00/0x20 is.

## What is hard

- Memory, beyond the first class: spill and scratch words must not alias memory the machine IR
  uses while the spilled value is live, frames of recursive functions, and the call preserves that
  are not yet recorded. The first two are checkable from the record; the third needs Sonatina to
  record `call_preserve` (keyed by call position) and dynamic-frame layouts.
- The model-to-IR proof sees the memory plan's addresses: static arenas as constants, heap
  allocations as free-pointer arithmetic. Lemmas over `evm_mload`/`evm_mstore` at distinct
  constant words keep it short; whether agents find it as cheap as the IR after optimization is
  untested.
- The interpreter's memory writes are unbounded: a wrong semantics that writes at a huge address
  exhausts memory instead of diverging (seen once, before the initial free pointer was modelled).

## Not looked into

Enum, object and array instructions; globals and data sections; contracts that create others
(external embeds); the native and wasm backends; gas.
