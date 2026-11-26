# The version-5 dialect: notes

What changed in the Sonatina model and the byte checker for the compiler output of sidecar
version 5 (Sonatina `machine-steps` `0585e54f`, without `undef` and `freeze`), and how the checker
fares on it.  The measurements are on mb16 under
`~/code/fe-correctness-scratch/provable-pipeline/dialect/`: `base-*.txt` with the code at
`2d14d7f`, `final-*.txt` at `66504ea`, `flag-*.txt` at `ec97dd5`, each run on a snapshot of that
commit's build; `tally.py` summarizes one, `inst_census.py` and `spillshape.py` count what the
machine IR and the spill records hold.  `scripts/DialectSweep.lean` is the sweep (interpreted,
no kernel evaluation).  The corpus: the 265 contracts at `-O1` (`dialect/corpus-v5-full`, checked
against the export tarball) and the 20 FeProofs sidecars at each of `-O0`, `-O1`, `-Os`
(`m1-lean/corpus-v5b`).

## Measurements

Sections accepted by `check` / by `checkSpills` (each section, `check` under the empty plan and
only without memory spills, `checkSpills` under the walked plan).  Every sidecar of every set is
read: no machine IR has an instruction or type line the reader lacks.  The module after
optimization and the section IR, which the checker does not read, are often outside the subset
(`evm_return_code`, `agg.make`, `obj.*`, `gep`, `evm_mload_bytes`).

| Set (sections) | `2d14d7f` | `66504ea` | `ec97dd5` |
| --- | --- | --- | --- |
| FeProofs `-O0` (40) | 1 / 1 | 34 / 40 | 34 / 40 |
| FeProofs `-O1` (40) | 32 / 39 | 32 / 39 | 33 / 40 |
| FeProofs `-Os` (40) | 32 / 39 | 32 / 39 | 33 / 40 |
| corpus `-O1` (530) | 512 / 521 | 512 / 521 | 520 / 529 |

The rejections, by `checkSpills`:
- `2d14d7f`, FeProofs `-O0`: 39, each "block at pc does not match its bytes" at a function's
  first branch (`PUSH0 EQ` as `ISZERO`, and `ISZERO ISZERO` dropped before the `JUMPI`).
- `2d14d7f` and `66504ea`, FeProofs `-O1` and `-Os`: Holder's runtime, block 11.
- `2d14d7f` and `66504ea`, corpus: 8 byte mismatches (the runtimes of `WETH9.Holder`,
  `eip712_domain.Proxy`, `escrow.ArbiterProxy`, `reentrancy_mutex.A`,
  `reentrancy_mutex_storage_map.A`, `reentrancy_tstor_ptr.A`, `typed_call_returns.Probe`,
  `vault.VaultUser`), each accepted once `ec97dd5` matches the backend's dropped pair of `ISZERO`s
  after a flag or a comparison (Holder's block 11, for one, passes the `CALL`'s flag where the IR
  has `is_zero(is_zero(flag))`); and 1
  "`default_recursive` is outside the class" (`storage_map_recursive_views.C`).
- `ec97dd5`: only `storage_map_recursive_views.C`'s runtime.

The sections `check` rejects and `checkSpills` accepts are those with memory spills (6, 7, 7 at
the three FeProofs levels, 9 in the corpus).  No section's record disagrees with its walked spill
plan.

## What changed

**`undef`** is gone from `Operand`, the reader (an `undef.T` operand is a read error), the
interpreter, the checker and the proofs.  No version-5 machine IR has one.  The committed
fixtures' module after optimization (`Case44Bank`, `DepositContract`, `NestedArrayCaller`,
`WETH9`, of the old compiler) has `undef` operands, so their `Sidecar.module` is `none` now; the
checker and the certificates do not read it.

**`unreachable` traps**, as `evm_invalid` does (`docs/memory.md`; the backend emits `INVALID`,
`isa/evm/emit/insn.rs`).  The checker reads it as `.halt .INVALID []`; after a call to a function
that does not return the bytes never reach it, as before, and `Exit.unreach` is gone.  No
top-level statement changed: `check_sound`, `checkSpills_sound` and the `*_xiOk*` theorems read
as before, but the `s.model .machine` they speak of now ends in a trap where it diverged.
Internally `exitOf_halt` has `(t = .evmInvalid ∨ t = .unreachable) ∧ op = .INVALID ∧ args = []`
for `t = .evmInvalid ∧ op = .INVALID ∧ args = []`.

**New instructions**, in the syntax, the reader and the interpreter:

| Instruction | Semantics | Source |
| --- | --- | --- |
| `evm_uaddsat a b T` … `evm_smulsat` (`Inst.sat`) | `SatOp.eval`: both operands truncated to the width of `T`, the operation saturated at it, the result zero-extended (unsigned) or sign-extended (signed) to a word | Sonatina's interpreter, `crates/ir/src/interpret/evm/mod.rs` (`EvmUaddsat` … `EvmSmulsat`, `narrow_sat_args`); the bytes, `emit_narrow_{un,}signed_saturating_binary` in `isa/evm/emit/stack.rs`, compute the same with a branch inside the instruction.  Checked against Sonatina's own examples |
| `get_function_ptr %f` (`Inst.funcPtr`) | the offset of `%f` in the section's symbol table | the backend pushes the function's label (`insn.rs`); that the two agree for a merged function is not checked |
| `black_box v` (`Inst.blackBox`) | `v` | `insn.rs`: the operand stays on the stack |
| `evm_call_code` | `callcode`: `Fe.EVM.message` with this contract as source and recipient, the code at the address, the value as value and apparent value, no static-call failure | `CALLCODE` (`insn.rs`); `Fe.EVM.message?` reads EVMLean's `CALLCODE` so |
| `evm_self_destruct a` (terminator) | `Fe.EVM.selfdestruct` | `SELFDESTRUCT` (`insn.rs`) |
| `evm_msize` | stuck | `docs/memory.md` E4: it observes the backend's placement and spills, outside the certified subset |

The checker rejects every one of them (`evm_msize` with its own error).  None occurs in any
machine IR of the corpus, so none is in the checker's class.

**The backend's stack peepholes** (`isa/evm/emit/stack.rs`, `prune_redundant_opcode_sequences`,
which runs after the machine IR is recorded) at `0585e54f`:
- `PUSH0 EQ` becomes `ISZERO`;
- `ISZERO ISZERO PUSH label JUMPI` drops both `ISZERO`s;
- after a boolean producer (`is_bool_producer_opcode`: `LT`, `GT`, `SLT`, `SGT`, `EQ`, `ISZERO`,
  `CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`) a run of two or more `ISZERO`s shrinks to its
  parity, and `PUSH 1 AND` is dropped.

Each is valid on the EVM: `ISZERO` of `ISZERO` keeps a word's truth, and every listed producer
pushes 0 or 1 (a message call its success flag).  The checker matches them:
- `normalize` reads `EQ` with zero as `ISZERO`, `Expr.caseOf` reads `ISZERO` of a `br_table`
  scrutinee as its case 0, and `Exit.way` compares a conditional jump's condition with the
  branch's up to pairs of `ISZERO`s (`Expr.peel`) — `66504ea`;
- value numbering names two `ISZERO`s of a message call's flag or of a comparison by the value
  itself (`Canon.flagNodes`), so `is_zero(is_zero(v))` is `v` on both sides — `ec97dd5`.  That a
  flag is 0 or 1 is a fact of the IR's semantics, not a hypothesis: `Eqn` carries it for each
  `evm_call`, `evm_static_call` and `evm_delegate_call` value, proved from `Fe.EVM.message`
  (`message_flag`, `evRun_flag`); `complete` gives an unreached flag the word 0.
`AND 1` after a producer occurs nowhere in the corpus's rejections and is not matched.
`scripts/DialectMutants.lean` checks the flag rule: on Holder, `typed_call_returns.Probe` and
`reentrancy_mutex.A`, turning the inner `is_zero` into `not`, or reading the outer one of the
flag itself, is rejected at the block; two `is_zero`s of an `evm_sload` stay two.  The fixtures'
verdicts and every mutant of `scripts/SonatinaCheck.lean` are unchanged.

## Spills

Version 5 can record a spill with stores and no reloads (a reload stored straight back to its
word is dropped, Sonatina `0fa60e43`), and a phi without a store on an edge whose operand already
sits in the phi's word (`final_spills.rs`, `skip_same_word`).  Neither occurs in the corpus:
of 2,532 memory spills in 112 functions (`spillshape.py`, all 325 sidecars) none has stores
without reloads or neither; of 259 spilled-phi edges, 18 take the phi itself and 241 an operand
at another word, each with its store.  So `checkSpills` and `FrameSafe` are unchanged.  Were such
a record to appear, the checker would reject it: `Func.instrument` stores a phi's operand on every
edge, and the bytes would lack the store.  Supporting it would mean skipping the edge store when
the operand is spilled at the phi's word, and carrying the operand's reload-liveness across that
edge (`blockLive`, `Func.liveClosed`, `Func.LiveStep`).

Whether a spill store pops its value or keeps a copy does not matter to the checker, which walks
the bytes' `DUP`s.  A plan read from the record instead of the walk would need each store point
to say which.

## The dynamic frame of `storage_map_recursive_views.C`

The runtime's seven functions (`default_recursive`, `direct_dynamic`, `direct_static`,
`effect_recursive`, `mutual_a`, `mutual_b`, `receiver_recursive`) are recorded with
`stable: dynamic_frame`, no stable words, no lazy frame, no dynamic stack pointer
initialization and no call preserves.  Their bytes have no frame code: no access of the dynamic
stack pointer at `0x80`, no frame entry or exit (`enter_frame_initialized`, `leave_frame`), as
Sonatina skips the setup in frameless recursion.  Their scratch objects are the fixed words
`0x00`/`0x20` the machine IR writes itself.  The checker rejects the section only for the
record's flag (`inClass`), to which no proof refers: an access to frame memory the machine
IR lacks would fail the byte match.  To accept it the record would have to say that the frame is
empty and no frame code is emitted (the frame's byte size, or whether entry and exit are
emitted), or the checker could drop `!dynamicFrame` from `inClass` and leave the frame code, if
any, to the byte match.
