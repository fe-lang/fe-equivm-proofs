# M1, first Lean phase: notes and deviations

Design: `fe-correctness-scratch/provable-pipeline/m1/design.md` (with section 10, review 1).

## Modules

| Module | Contents |
| --- | --- |
| `Refine.lean` (existing) | `EndsAsP`, `ImplementsP`, `ImplementsDeployP`, transitivity, `RefinesOn.of_implementsP`, `RefinesDeploy.of_implementsP` |
| `Mem.lean` | `write_getD`, `MemEq`, `MemEq.write` (Mem0), `WRel`, `ExitRel`, `ResRel`, `Approx` (the order `⊑`), Mem0 for every model-library primitive |
| `Prim.lean` | `EnvSub`, operand evaluation as `lift`, `Approx.runInst` (an instruction approximates itself in a smaller environment and a related world), `approx_auto` |
| `Oracle.lean` | `runStmtO`/`runBodyO`/`stepBlock`/`runBlocksO`/`runFuncO`, `runBlocks_iter`, `runFunc_approx`, `runFunc_ctx` (C0 and reflexivity), `runFuncO_approx`, `ModRefines`, `FuncRef`, C1 `modRefines_of_funcs` |
| `Sim.lean` | `Sim`, `Sim.approx`, `Sim.of_steps` |
| `NatMap.lean` | bit trie, `find?_insert`, `find?_ofList`, `find?_ofListBy` |
| `Eq.lean` | `DecidableEq` for the IR |
| `EdgeSplit.lean` | `checkEdgeSplit`, `edgeSplit_sound` |
| `Record.lean`, `Read.lean` | `MachineSteps` and its reader (`machine_steps`, `machine_steps_file`) |
| `Validate.lean` | `checkStep`, `StepSound`, `validateWith`, `validate`, `validate_sound`, `edgeSplit_stepSound` |
| `Machine.lean` | `Sidecar.lowered`, `machine_implementsP`, `machine_sound`, `machine_sound_edgeSplit` |
| `Dom.lean` | `domTree`, `DomTree.valid` (review H-1), D1 `DomTree.dominates` |
| `Tests.lean`, `Tests/` | hand-written records, accepted and mutated |
| `scripts/MachineSteps.lean` | verdict and first failing step per section of version-5 sidecars |

The `Steps` modules are not in the default `lake build` target (neither is `Fe.lean`); build
them with `lake build Fe.Sonatina.Steps.Tests` (it imports all of them but `Dom`) and
`lake build Fe.Sonatina.Steps.Dom`.

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

## Deviations from the design

1. **`StepSound` has no `summariesOK` hypothesis.** No checker of this phase reads
   `func_behavior`; when one does, `StepSound` gains the hypothesis that the table holds of the
   oracle's module.
2. **`edge_split`: `br c a a → jump a` only when `c` is an immediate.**  Under partial
   correctness the input evaluates `c` and may be stuck (unbound, or an aggregate) where the
   output, which no longer evaluates it, goes on.  Accepting it in general needs the
   definedness invariant that `ssa` would give (not built).  `br_table → jump` is rejected for
   the same reason (and for a defaultless table, review C-6).
3. **Noreturn trims, `cfg_cleanup`, `branch_canonicalize`: no checker.** `checkFunc` rejects every
   kind but `edge_split`.  See "Not done".
4. **Final comparison by name.** The machine IR prints a section's functions in another order
   than `lowered` lists them; `validate` compares function by function (`sameFuncs`).
5. **The record reader** follows `sidecar-v5.md` of the export, not design §3.1 (no version
   key; `Pass.kind`; a function step named by `out.func`; every fact key present, empty ones
   dropped by the reader).  `Parse.lean` accepts sidecar versions 4 and 5.
6. **`wf` and `ssa` (design §4.1, review C-6, H-1) are not built.**  `validate` checks that every
   snapshot is machine IR (`Inst.machine`: no `evm_malloc`, no `alloca`; `evm_msize` is not in
   `Syntax.lean`), not the rest of `wf`.  `edge_split` deletes nothing, so its soundness needs
   none of C-6; `cfg_cleanup` and every deleting kind will.  `validate` does not take the
   symbol names yet (C-6).
7. **D1 needs no acyclicity.**  `DomTree.dominates` is proved for the inductive ancestry `Anc`
   with `idom entry = none`, the closed reachable set and the edge condition; a cycle in `idom`
   only makes the checker's climbing (`anc`, at most `size` steps) fail.  Pre/post numbering is
   not used; `anc` climbs, which is O(depth).

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
