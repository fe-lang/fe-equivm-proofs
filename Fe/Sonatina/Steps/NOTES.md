# M1, Lean phases 1 and 2: notes and deviations

Design: `fe-correctness-scratch/provable-pipeline/m1/design.md` (with section 10, review 1).

## Modules

| Module | Contents |
| --- | --- |
| `Refine.lean` (existing) | `EndsAsP`, `ImplementsP`, `ImplementsDeployP`, transitivity, `RefinesOn.of_implementsP`, `RefinesDeploy.of_implementsP` |
| `Mem.lean` | `write_getD`, `MemEq`, `MemEq.write` (Mem0), `WRel`, `ExitRel`, `ResRel`, `Approx` (the order `⊑`), Mem0 for every model-library primitive |
| `Prim.lean` | `Inst.machine`/`Func.machine` (no `undef`, `evm_malloc`, `alloca`, aggregates), `EnvSub`, operand evaluation as `lift`, `Approx.runInst`, `approx_auto`; integer values (`IntVals`, `EnvInt`, `Returns`, `Total`, `Approx.strengthen`, `returns_runInst`, `returns_bind`, `returns_enter`) |
| `Oracle.lean` | `runStmtO`/`runBodyO`/`stepBlock`/`runBlocksO`/`runFuncO`, `runBlocks_iter`, `runFunc_approx`, `runFunc_intRet`, `runFunc_ctx` (C0 and reflexivity), `runFuncO_approx`, `Ctx.Has`, `ModRefines syms`, `FuncRef`, C1 `modRefines_of_funcs`; `Oracle.IntRet` |
| `Wf.lean` | `Func.wf`, `Module.wf`, `FuncSnap.wf` (review C-6), `VFunc`, `defsOf`, `ssa` (review H-1, M-1), `DomAt`, `useOk_sound`, `phiUseOk_sound` |
| `Defined.lean` | the definedness invariant: `BlockInv`, `PointInv`, `stepBlock_inv`, `Reaches`, `reaches_inv`, `defined`, `term_defined`, `phis_defined` |
| `Sim.lean` | `Sim`, `Sim.approx`, `Sim.of_steps` |
| `NatMap.lean` | bit trie, `find?_insert`, `find?_ofList`, `find?_ofListBy` |
| `Eq.lean` | `DecidableEq` for the IR |
| `EdgeSplit.lean` | `checkEdgeSplit` (with `br c a a → jump a` and all-identical `br_table` → `jump`), `edgeSplit_sound` |
| `Record.lean`, `Read.lean` | `MachineSteps` and its reader (`machine_steps`, `machine_steps_file`) |
| `Validate.lean` | `checkStep`, `StepSound`, `stepOut_wf`, `validateWith`, `validate`, `validate_sound`, `edgeSplit_stepSound` |
| `Machine.lean` | `Sidecar.lowered`, `Sidecar.symbolsOf`, `machine_implementsP`, `machine_sound`, `machine_sound_edgeSplit` |
| `Dom.lean` | `domTree`, `DomTree.valid` (review H-1, review 6 F-8), D1 `DomTree.dominates`, `valid_root` |
| `Tests.lean`, `Tests/` | hand-written records, accepted and mutated |
| `scripts/MachineSteps.lean` | verdict and first failing step per section of version-5 sidecars |

The `Steps` modules are not in the default `lake build` target (neither is `Fe.lean`); build
them with `lake build Fe.Sonatina.Steps.Tests`, which imports all of them.

## C1: how it went

C1 went through without re-layering the semantics (review C-7 proposes `runModule` as an outer
fixpoint and `runModule = runFuncG`).  The route taken: one generic theorem,
`runFunc_approx`, by `runFuncG.fixpoint_induct` over the module `N` whose run is on the left,
with the motives

- body: the approximant `H` of `N`'s statements approximates `runBodyO o c` of the same
  statements;
- function: the approximant `F` approximates the oracle `o`;
- blocks: the approximant `G` of a function's blocks approximates `TB` of the same function,
  for a parameter `TB` that is the iteration of `stepBlock o c`.

The motives compare `N` with itself, block for block, so differing CFGs never meet the mutual
induction; the CFG change is a hypothesis at the function step: `x ⊑ runFuncT TB (N.func? f)
→ x ⊑ o f`.  Instances: reflexivity/C0 (`N = M`, `o = ⟦M⟧`, `TB = runBlocks M`, the hypothesis
by `runFunc_eq`), and C1 (`N = M'`, `o = ⟦M⟧`, `TB = runBlocksO ⟦M⟧`, the hypothesis by the
per-function lemma and `runFuncO_approx`, itself by `runBlocksO.fixpoint_induct`).  Each step
kind proves its per-function lemma by `runBlocksO.fixpoint_induct` (`Sim.approx`) under a fixed
oracle.  So the review's diagnosis of the design's sketch is right, but its cure is not needed;
`runModule` was not built.  The rest of C-7 was adopted from the start: `⊑` quantifies over
related input worlds, `WRel` includes `returnData`, `ResRel` relates the worlds inside
`Exit.stop`.

Within a pass every step uses the pass input's semantics as the oracle (`validatePass_sound`);
`StepSound` is stated for any self-approximating oracle, so the two kinds of this phase do not
need the pass-level discipline, but later kinds that read `func_behavior` will.

## Integers: what the oracle framework assumes (phase 2)

`FuncRef`, `ModRefines`, `Oracle.Le` and `Oracle.Mono` compare runs on integer arguments only
(`IntVals`), and `StepSound` assumes an oracle that returns integers on integers
(`Oracle.IntRet`).  Without that, `edge_split`'s `br c a a → jump a` is unsound: `bind` keeps an
aggregate argument an aggregate even under an `i256` parameter (`Val.as`), so with `c` a
parameter (or a call's result) bound to an aggregate the input is stuck at `evalInt` and the
output goes on.  A machine function is called with integers by a section entry (no arguments)
and by its callers, and returns integers: `runFunc_intRet` (by fixpoint induction over the
module's runner, `Func.machine` giving no `undef` operand and no aggregate instruction); C1
and C0 (`runFunc_approx`) carry `EnvInt` through the run.

`ModRefines syms` and `StepSound` also take the section's symbol names: only contexts that give
each of them a place (`Ctx.Has syms`, review C-6 and review 6 F-5), which `runSection_approx`
discharges from `code.symbols` (`lookup_has`).  No proof of this phase needs `Ctx.Has`; a
deleting kind (a dead `sym_addr`) will.  `StepSound` is a plain `∀ … → …` statement, so the
summary-table hypothesis (`SummariesOk`, review 6 F-5) is one more premise beside `c.Has syms`.

## The definedness invariant

`Defined.lean`.  For a well-formed function (`Func.wf`, which gives the `i256` types, distinct
block ids and `Func.machine`) and a tree `DomTree.valid` accepts, along any run from the entry
with integer parameters and an integer-returning oracle, every reached block state satisfies
`BlockInv`, and every point `(b, k)` of its block `PointInv`: each value whose definition
dominates the point (`DomAt`: a parameter, a phi of `b`, a result of a statement of `b` before
`k`, a definition in a strict tree ancestor of `b`) is bound, to an `i256`.  This needs neither
`ssa`'s use check nor unique definitions: the run binds phis on entry and results after each
statement and never unbinds; at an edge `p → b` from a reachable `p`, a strict ancestor of `b`
is an ancestor-or-self of `p` (the edge condition, `anc_of_edge`); `idom` acyclicity is not used.
`ssa` then says every use is such a value or an immediate (`useOk_sound`, `phiUseOk_sound`), so
it evaluates to an `i256` (`defined`, `term_defined`, `phis_defined`).  L2 (values, not only
definedness) is not built; it needs the uniqueness `ssa` checks and per-point reasoning on top
of `PointInv`.

## Deviations from the design

1. **`StepSound` has no `summariesOK` hypothesis.** No checker of this phase reads
   `func_behavior`; when one does, `StepSound` gains the hypothesis that the table holds of the
   oracle's module.
2. **`edge_split` restriction lifted (phase 2).**  `br c a a → jump a` for any `c`, and
   `br_table s (some d) cases → jump d'` when every case goes to `d` (`ESCtx.termOk`).  The
   checker computes the input's dominator tree, `DomTree.valid` and `ssa` (`checkEdgeSplit`);
   with `Func.wf` of the input (from `Module.wf` of the step input, a `StepSound` premise) the
   invariant gives that the input's terminator reads words, so it is not stuck where the output
   goes on (`approx_runTerm`, `term_defined`).  A defaultless table is still rejected (review
   C-6; also by `wf`).
3. **Noreturn trims, `cfg_cleanup`, `branch_canonicalize`: no checker.** `checkFunc` rejects every
   kind but `edge_split`.  See "Not done".
4. **Final comparison by name.** The machine IR prints a section's functions in another order
   than `lowered` lists them; `validate` compares function by function (`sameFuncs`).
5. **The record reader** follows `sidecar-v5.md` of the export, not design §3.1 (no version
   key; `Pass.kind`; a function step named by `out.func`; every fact key present, empty ones
   dropped by the reader).  `Parse.lean` accepts sidecar versions 4 and 5.
6. **`wf` and `ssa` (phase 2).**  `validateWith` checks `Module.wf syms` of the lowered module and
   the instruction ids of its snapshots; `checkStep` checks every output function well formed
   in the input module, with its instruction ids, and the input's signature (parameters and
   results, `sameSig`), so every module of the replay is well formed (`stepOut_wf`) and
   `validate_sound` returns `Module.wf` of both ends.  `ssa` is checked where a kind needs it:
   `edge_split` on its input.  Deviations from §4.1: `wf` does not check that phis lead their
   block (the parser makes it so, and now rejects a phi after a statement: review 6 F-1), nor
   that a block has exactly one terminator (the parser), nor the text against `insts` beyond
   their shape and distinct ids (the parser pairs them); `ssa` checks uses only in blocks the
   tree claims reachable, and phi operands only from such predecessors (review H-1).  `Func.wf`
   does not check result counts of instructions other than `call` (a wrong count is stuck in
   `bind`, on both sides alike).
7. **D1 needs no acyclicity.**  `DomTree.dominates` is proved for the inductive ancestry `Anc`
   with `idom entry = none`, the closed reachable set and the edge condition.  Pre/post
   numbering is not used; `anc` climbs, which is O(depth).  Phase 2 adds review 6 F-8's check
   (`anc entry b` for every block of the reachable set, `valid_root`), which excludes cycles of
   `idom` on the reachable set; no proof assumes antisymmetry.
8. **`Inst.machine` excludes `undef` operands, `insert_value` and `extract_value` (phase 2)**,
   beside `evm_malloc` and `alloca`: C1 needs runs to stay integer-valued.

## Review 6 (phase 1) findings taken up in phase 2

- F-1: adopted.  `Parse.statement` rejects a `phi` line after a statement (phase 2's one change
  to `Parse.lean`); a scan of the repository's 58 JSON fixtures (1785 blocks) found no such line.
  `wf` checks the `insts` shape and distinct ids kernel side (`FuncSnap.idsOk`).
- F-2: adopted.  `ESCtx.predOf` takes the distinct blocks whose slots target the block.
- F-3: adopted.  `domTree` walks successors without repeats (`succMapOnce`); `valid` reads
  `succMap`.
- F-5: adopted for the symbols (above); the summary table is left to the next worker.
- F-8: adopted (deviation 7).
- Not taken up here (out of item 1): F-4, F-6, F-7, F-9, F-10.

## Phase-1 history

Commits 7e6f2c1, 9dbd430 and 04f9f01 do not build alone (each needs a later commit); they were
left as they are.

## Memory past 2^256 (ruling 3 as changed by review C-1)

Only `evm_mcopy` with `len > 0` and `src + len > 2^256` or `dst + len > 2^256` is to diverge in
the IR semantics; no semantics was changed in this phase.  What the byte side (`check_sound`)
then needs: wherever the IR's `mcopy` diverges, the bytes' `MCOPY` step must end in `OutOfGass`,
which `RefinesFor`'s `Exhausted` disjunct excuses.

What EVMLean gives (`.lake/packages/evmlean`, `Ethereum/Gas.lean`, `memoryExpansionCost`, case
`.MCOPY`; `Ethereum/MachineStateOps.lean`, `MachineState.M`; `Gas.Cₘ`):
- the new size in words is `M activeWords (max dst src) len`, computed in `ℕ` (no wraparound:
  "the addition is not subject to 2^256 division"), `max activeWords ((a + len + 31) / 32)`
  with `a = max dst src`; with `a + len > 2^256` that is at least `2^251`, below `2^256`, so
  the `UInt256.ofNat` around it does not wrap;
- the charge is `Cₘ new - Cₘ activeWords` with `Cₘ x = 3x + x²/512`, so at least
  `Cₘ 2^251 - Cₘ activeWords ≥ 2^493 - Cₘ activeWords`;
- the gas left is a `UInt256`, below `2^256`.

So `OutOfGass` follows if `Cₘ activeWords` is small, for instance `activeWords < 2^240`.  That
is the lemma's missing hypothesis: EVMLean's state does not bound `activeWords` by itself; a
frame only reaches large memory by paying for it, so the bound is an invariant of reachable
states (`Cₘ activeWords ≤` the gas spent so far `< 2^256`), which `check_sound`'s state relation
(`Agree`/`PathRel`, `CheckEvent.lean`, `CheckBlock.lean`) would have to carry from the frame's
start (`activeWords = 0`) through every step that expands memory.  Proofs that change: the
`.mcopy` case of `evRun` and its `EvMoves` (`event_evMoves`, `CheckEvent.lean`), which would
gain the divergence case, and `run_ends`/`section_run` for the invariant.  The lemma itself,
`mcopy_oog : len > 0 → max dst src + len > 2^256 → activeWords < 2^240 → step MCOPY = .error
.OutOfGass`, is unproved; whether EVMLean's `X` checks the memory charge before any other
failure of `MCOPY` (stack underflow is excluded at a matched step) is to be read in
`Semantics.lean` around line 674.

## Measured

- Kernel: `domTree` + `DomTree.valid` on the deposit contract's runtime root (fixture, 120
  blocks, 461 lines), 1.14 s (15 s before the fixpoint stop).  `validateWith [.edgeSplit]` on
  the real record of WETH9's `init` section at `-O0` (458 lines, one `edge_split` step), 3.91 s.
- `scripts/MachineSteps.lean` with `edge_split,cfg_cleanup,branch_canonicalize` (interpreted),
  on `corpus-v5/feproofs-O0` and `feproofs-O1` (copies on mb16; some precompile files were
  truncated by the copy and are not read: 4 at `-O0`, 7 at `-O1`):
  - `-O0`: 32 sections read; 15 accepted (every `init` but FeERC20's; 3 of them with real
    `edge_split` steps: FeCodeScalar, FeScalarStore, WETH9), 17 rejected, all at their first
    `coalesce_copies` step (no checker).  Counting with `coalesce_copies` as a hypothesis needs
    its checker; not done.
  - `-O1`: 26 sections read; 1 accepted (WETH9's Holder `init`, no steps), 25 rejected: 15 at
    the first `cfg_cleanup` step, 10 at the first `branch_canonicalize` step (no checker for
    either).

- Phase 2, the same runs with `wf` and `ssa` in place: the same verdicts at `-O0` (15
  accepted, 17 rejected at their first `coalesce_copies`) and at `-O1` (1 accepted, 15 at
  `cfg_cleanup`, 10 at `branch_canonicalize`).  Every lowered module read is well formed (the
  diagnosis checks it first), and so is every step output before the first rejected step.

## Not done

- `cfg_cleanup` and `branch_canonicalize`: no checker, no soundness (enter as `StepSound`
  hypotheses; `checkFunc` rejects them).  `cfg_cleanup` needs the definedness invariant and the
  trivial-phi invariant (`TreeAnc B b → env[v] = env[x]`, preserved by steps given D1's edge
  condition and `ssa`'s use-dominance); `branch_canonicalize` needs L2 at program points.
- Noreturn trims (rejected: no new instruction ids are accepted by any checker).
- The `mcopy` gas lemma and semantics change (above).
