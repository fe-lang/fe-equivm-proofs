# Sonatina IR in Lean

A semantics of Sonatina IR, the backend IR of the Fe compiler, tested against the bytecode compiled
from it, and a design for splitting a bytecode certificate at that IR. Nothing here is trusted: the
interpreter is a contract model like any other, so an error in it makes a proof or a comparison
fail, not pass.

| Module | Contents |
| --- | --- |
| `Syntax.lean` | IR modules, functions, blocks, instructions; `Sidecar` (IR, sections, lowering) |
| `Parse.lean` | the reader of Sonatina's text form and of sidecar JSON; `sonatina_sidecar` |
| `Interp.lean` | the interpreter in `FeM`; `Sidecar.model level : ContractModel` at each IR level |
| `Hints.lean` | cheap checks of the lowering record against the bytes |
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
`evm_malloc`, `alloca`, structs and arrays by `insert_value`/`extract_value`,
`sym_addr`/`sym_size`, `evm_keccak256_words`, calls, the machine IR's `evm_mload`/`evm_mstore`, and
every EVM instruction the model library has a primitive for: storage, transient storage, calldata,
code, logs, the environment, `gas`, message calls and creations. The same subset covers the IR
after optimization, a section's IR after the backend's pipeline and its machine IR; a value takes
the width its definition declares, so the machine IR's `i256` comparison results are words. Other
instructions (`gep`, `obj.*`, `enum.*`, narrow memory accesses), object reference types, and any
use of a global or an enum are parse errors; enum and global declarations are skipped.

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
  ∀ I σ A feed, admits I → ∃ feed', EndsAs (model.runtime.exec I (World.init σ A feed'))
    (ir.runtime.exec I (World.init σ A feed))
```

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

Every disagreement is the `leading_zeros` fixture, whose bytecode uses `CLZ`, which EVMLean lacks.
The machine IR agrees once its run starts as the section entry's code does, with the initial free
pointer at `0x40`; without it the deposit contract's machine IR read a zero free pointer, and its
run exhausted the interpreter's memory. The 66 contracts not read use object or constant
references, enums or nested arrays. One more, `abi_bounded_input_len_untrusted`'s `Decoder`, has a
`gep` in its section IR alone, which the subset does not read: at that level its 8 test calls and
132 generated calls are not run. (The first run of this table read a sidecar only when all three of
its IRs were, which lost that contract at every level.)

`Hints.check` finds no failure in the 7914 machine blocks of the 428 sections of the corpus's
sidecars (the 34 sidecars the reader stops at aside). It refutes what it can see: on the six
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

`Check.lean` is the first checker. `check s` covers sections of one function (no internal call)
with no memory spill, dynamic frame, dynamic stack pointer or call preserve, whose machine IR uses
only the pure, read, write and halting instructions `Check.lean` translates (no external call, no
`gas`, no `create`). It accepts both sections of FeConstant, FeScalarStore and FeERC20. On the
corpus it accepts 332 of 430 sections; it rejects 40 as more than one function, 33 for an
instruction outside the class, and 25 whose bytes it does not match. Those 25 are unclassified:
they may be patterns the matcher does not know (as the commuted operands and constant branches
were, which raised the count from 282) or wrong hints. `scripts/SonatinaCheck.lean` runs the
fixtures, mutations of their hints (a dropped, added or swapped entry slot, offsets moved by a
byte, a moved free pointer, dropped redirects: all rejected; moved symbols are accepted where the
section's IR reads none) and a corpus directory.

The verdict evaluates by the kernel (`decide +kernel`, 3.1 s for both FeScalarStore sections) and
by `native_decide` (0.12 s). Kernel evaluation needs the expressions non-nested and the checker
structurally recursive, which is why `Expr` has fixed arities.

What `check s = true` is to imply is stated in `CheckSound.lean` as `Sound s`, at `P0`; it is not
proved. On the statement:

- `P1` is provable from EVMLean's `X` and `Xstep`: `XstepN_X_halt_success` gives the final state,
  whose substate holds the logs, and `XstepN_X_halt_revert` the revert output. EquiVM's `RD`
  hides both, so a proof built on its cursor lemmas concludes `P0` only; one built on its per-opcode
  `*_xstep` lemmas and `XstepN` reaches `P1`.
- Running out of gas or stack is `Exhausted`, which `RefinesFor` excuses: every per-opcode step is
  an `if gas < cost then OutOfGass` or overflows to `StackOverflow`, and either error ends `Ξ`.
  The bytes' gas never meets the model's steps: the runner is a least fixpoint, so the theorem
  needs no relation between the two. With the fuel-bounded runner of stages B and C it was false
  for a run of more blocks than the fuel.
- `XstepN` is a path: the block lemmas can state that the bytes reach the successor's offset in
  `n` steps, `XstepN_X_continue` turns that into `X`, and `XOk` holds of a frame whose steps the
  class makes call-free (`stepOk` is `True` for every opcode but calls and creations).

Proved so far: that constant folding is sound (`foldConst_eval`). Left, in order: the soundness
of operand normalization (commutativity of the six operations, `GT` as swapped `LT`); per-opcode
lemmas relating one symbolic step to `Xstep` for each opcode `run` accepts, from EquiVM's
`*_xstep`; the block lemma by induction on `run`'s fuel; the IR side, `runBlocks` unfolded on
the block's events (needs per-instruction lemmas: the interpreter's arithmetic on 256-bit values
is EVMLean's); the section, from the entry block at offset 0 with an empty stack and the free
pointer prologue, by induction on the bytecode's steps; deployment (`CODECOPY` of the runtime and
`RETURN`, the constructor arguments read from the code); then the model half for FeScalarStore.

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
