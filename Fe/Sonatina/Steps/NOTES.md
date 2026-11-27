# M1, Lean phases 1 and 2: notes and deviations

Design: `fe-correctness-scratch/provable-pipeline/m1/design.md` (with section 10, review 1).

## Modules

| Module | Contents |
| --- | --- |
| `Refine.lean` (existing) | `EndsAsP`, `ImplementsP`, `ImplementsDeployP`, transitivity, `RefinesOn.of_implementsP`, `RefinesDeploy.of_implementsP` |
| `Mem.lean` | `write_getD`, `MemEq`, `MemEq.write` (Mem0), `WRel`, `ExitRel`, `ResRel`, `Approx` (the order `⊑`), Mem0 for every model-library primitive |
| `Prim.lean` | `Inst.machine`/`Func.machine` (no `evm_malloc`, `alloca`, aggregates), `EnvSub`, operand evaluation as `lift`, `Approx.runInst`, `approx_auto`; integer values (`IntVals`, `EnvInt`, `Returns`, `Total`, `Approx.strengthen`, `returns_runInst`, `returns_bind`, `returns_enter`) |
| `Oracle.lean` | `runStmtO`/`runBodyO`/`stepBlock`/`runBlocksO`/`runFuncO`, `runBlocks_iter`, `runFunc_approx`, `runFunc_intRet`, `runFunc_ctx` (C0 and reflexivity), `runFuncO_approx`, `Ctx.Has`, `ModRefines syms`, `FuncRef`, C1 `modRefines_of_funcs`; `Oracle.IntRet` |
| `Wf.lean` | `Func.wf`, `Module.wf`, `FuncSnap.wf` (review C-6), `VFunc`, `defsOf`, `ssa` (review H-1, M-1), `DomAt`, `useOk_sound`, `phiUseOk_sound` |
| `Defined.lean` | the definedness invariant: `BlockInv`, `PointInv`, `stepBlock_inv`, `Reaches`, `reaches_inv`, `defined`, `term_defined`, `phis_defined` |
| `Sim.lean` | `Sim`, `Sim.approx`, `Sim.of_steps_env` (a stutter step may bind), `Sim.of_steps` |
| `NatMap.lean` | bit trie, `find?_insert`, `find?_ofList`, `find?_ofListBy` |
| `Eq.lean` | `DecidableEq` for the IR |
| `EdgeSplit.lean` | `termRel` (terminators slot by slot, shared with `cfg_cleanup`), `approx_runTerm`, `checkEdgeSplit`, `edgeSplit_sound` |
| `Summary.lean` | `noRet`, `trimIdx`, `cut`, `liveSet`, `noRetOk`, `SummariesOk`, `NoRetHolds`, `summariesOk_sound` |
| `CfgCleanup.lean` | `Inst.mapOps`/`Term.mapOps`, `CCtx` (the check's context), `sigmaOf`, `walk`, `slotOk`, `linkOk`, `chainFrom`, `blockOk`, `blockIdsOk`, `checkCfgCleanup` |
| `Run.lean` | lemmas the simulations share: `Inst.mapOps`/`Term.mapOps`, `inc`, `Fol`, `enterOpt`, binding lemmas, `UniqueDefs`, `DomTree.anc_antisymm`, `phi_has_pred`, `blockInv_of_point`, `enter_total`, `DomSub` |
| `L2.lean` | `Inst.pure`, `pureVals`, `runInst_pure`, `Before`, `PureInv`, `BlockPure`, `pureInv_enter`, `pureInv_stmt`, `pureInv_take`, `pureInv_step`, `l2` |
| `CfgCleanupSound.lean` | `PointTPI`, `tpi_enter`, `tpi_stmt`, `walk_run`, `stmts_fol`, `chain_fol`, `term_fol`, `enter_rel`, `block_fol`, `CR`, `cfg_sim`, `cfgCleanup_sound`, `cfgCleanup_stepSound` |
| `Coalesce.lean` | `addrNorm`, `useCount`, `loadsFirst`, `fresh`, `KCtx.runOk`, `keptOk`, `cbodyOk`, `unusedOk'`, `checkCoalesce` |
| `CoalesceSound.lean` | `toByteArray_uInt256`, `CopyMem`, `copyMem_store`, `copyMem_read`, `copyMem_end`, `memEq_write_mod`, `writes`, `writes_read`, `writes_copyMem`, `addrNorm_sound`, `baseVal`, `addrNorm_base_sound`, `exec_mcopy`, `exec_mcopy_big`, `KFacts`, `WinFacts`, `runOk_spec`, `WInv`, `WInv.env`, `keep_operand`, `store_load_before`, `in_step`, `win_walk`, `win_fol`, `kc_stmts`, `kc_term`, `kc_sim`, `coalesce_sound`, `coalesceCopies_stepSound` |
| `BranchCanon.lean` | `isZeroArg`, `peelOk`, `deletable`, `bodyOk`, `unusedOk`, `bcIdsOk`, `checkBranchCanon` |
| `LowerSwitches.lean` | `funcVars`, `look`, `subtree`, `leafOk`, `LSCtx` (`lab`, `pivot?`, `nodeOk`, `rootOk`, `expected`, `phiOk`, `blockOk`, `shapeOk`, `idsOk`), `checkLowerSwitches` |
| `LowerSwitchesSound.lean` | `LSCtx.Agree`, `runInst_congr`, `runStmtO_congr`, `runTerm_congr`, `approx_runTerm_agree`, `LSCtx.approx_runBodyO`, `LSCtx.approx_enter`, `leafOk_sel`, `runTerm_table`, `lt_br_run`, `stepBlock_leaf`, `stepBlock_node`, `LSCtx.R`, `lowerSwitches_sound`, `lowerSwitches_stepSound` |
| `BranchCanonSound.lean` | `peel_sound`, `bc_stmts`, `bc_term`, `bc_block_fol`, `BR`, `bc_sim`, `branchCanon_sound`, `branchCanon_stepSound`, `branchConditions_stepSound` |
| `SchemasPair.lean`, `SchemasEval.lean`, `SchemasInv.lean`, `SchemasStepSound.lean` | `sccpFold_stepSound`, `knownBitsSimplify_stepSound` and what they rest on (`SCHEMAS-NOTES.md`) |
| `Record.lean`, `Read.lean` | `MachineSteps` and its reader (`machine_steps`, `machine_steps_file`) |
| `Validate.lean` | `IdTab`, `checkFunc`, `checkStep`, `StepSound`, `stepOut_wf`, `validateStep`, `validatePass` (checks `SummariesOk`), `validateWith`, `StepKind.proved`, `validate` (the proved kinds only), `validate_sound`, `edgeSplit_stepSound` |
| `Machine.lean` | `Sidecar.lowered`, `Sidecar.symbolsOf`, `machine_implementsP`, `machine_sound_of_sound` (from `Sound s`), `machine_sound`, `machine_sound_edgeSplit`, `StepKind.proved_sound`, `machine_sound_proved_of_sound`, `machine_sound_proved` (on `validate` and `check`), `machine_sound_spills_proved` (on `validate`, `checkSpills` and `FrameSafe`) |
| `Dom.lean` | `domTree`, `DomTree.valid` (review H-1, review 6 F-8), D1 `DomTree.dominates`, `valid_root` |
| `Tests.lean`, `Tests/` | hand-written records, accepted and mutated |
| `scripts/MachineSteps.lean` | verdict and first failing step per section of version-5 sidecars |

The `Steps` modules belong to the model library `FeModel` (its globs take every module under
`Fe/Sonatina`), which the default `lake build` builds; `FeModel.lean` imports `Machine`, `Read`
and `KnownBitsInv`.  `lake build Fe.Sonatina.Steps.Tests` builds the modules of this file's
table.

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
`StepSound` is stated for any self-approximating oracle that never returns from a function the
pass's table claims does not return (`NoRetHolds`); `validatePass` checks the table against the
pass input (`SummariesOk`), whose semantics is that oracle (`summariesOk_sound`).

## Integers: what the oracle framework assumes (phase 2)

`FuncRef`, `ModRefines`, `Oracle.Le` and `Oracle.Mono` compare runs on integer arguments only
(`IntVals`), and `StepSound` assumes an oracle that returns integers on integers
(`Oracle.IntRet`).  Without that, `edge_split`'s `br c a a → jump a` is unsound: `bind` keeps an
aggregate argument an aggregate even under an `i256` parameter (`Val.as`), so with `c` a
parameter (or a call's result) bound to an aggregate the input is stuck at `evalInt` and the
output goes on.  A machine function is called with integers by a section entry (no arguments)
and by its callers, and returns integers: `runFunc_intRet` (by fixpoint induction over the
module's runner, `Func.machine` giving no aggregate instruction); C1
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

1. **Summary table (phase 2, review 6 F-5).**  Only the `noreturn` claims are checked
   (`SummariesOk`: from the entry, cutting paths at calls to claimed-noreturn functions, no
   reached block ends in `return`, on a reachable set checked closed); the effect claims and
   `will_return` have no consumer yet and are not read.  `validatePass` checks the table against
   the pass input and rejects the pass if a claim fails (`sidecar-v5.md`: the table may describe
   an earlier module; the measurement counts such passes).  `StepSound` takes `NoRetHolds O o`.
   `unreachable` traps (ruling 7, from the dialect line), so `cfg_cleanup`'s proof uses it: after
   a trimmed call the output ends in `unreachable`, which the run never reaches, as the call does
   not return (`noRet_runBodyO`, `Fol.strengthen`).
2. **`edge_split` restriction lifted (phase 2).**  `br c a a → jump a` for any `c`, and
   `br_table s (some d) cases → jump d'` when every case goes to `d` (`ESCtx.termOk`).  The
   checker computes the input's dominator tree, `DomTree.valid` and `ssa` (`checkEdgeSplit`);
   with `Func.wf` of the input (from `Module.wf` of the step input, a `StepSound` premise) the
   invariant gives that the input's terminator reads words, so it is not stuck where the output
   goes on (`approx_runTerm`, `term_defined`).  A defaultless table is still rejected (review
   C-6; also by `wf`).
3. **`checkFunc` accepts `edge_split`, `cfg_cleanup`, `branch_canonicalize`,
   `branch_conditions`, `coalesce_copies`, `known_bits_simplify`, `sccp_fold` and
   `lower_switches`** (phase 2; all eight are proved and in `StepKind.proved`, the kinds `validate` accepts and
   `machine_sound_proved` covers; `known_bits_simplify`'s demand rounds are switched off,
   `SchemasStep.lean`, `SCHEMAS-NOTES.md`); every other kind is rejected.  Facts (ruling R-11.3): `FuncStep.facts` is the `Schemas.StepFacts` that
   `Schemas.readFacts` reads at read time; `checkFunc` takes them; each kind but the two schema ones
   requires `noFacts` (no known bits, no demand round, no SCCP facts, no unread key), the two
   schema kinds check the facts they read; `StepSound.of_func` quantifies over them.
   `Read.parseFacts` keeps `"demanded_bits": []`, a demand round with no demanded value.  `checkFunc` takes the pass's table, the input's instruction ids and the output
   snapshot; the replay carries each function's ids (`IdTab`, the latest first), which the module
   does not hold.
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
8. **`Inst.machine` excludes `insert_value` and `extract_value` (phase 2)**, beside
   `evm_malloc` and `alloca`: C1 needs runs to stay integer-valued.  The IR has no `undef` (the
   dialect line removed it).  `Inst.wf` also rejects `evm_msize`, which the semantics leaves
   stuck, and checks the symbol of `get_function_ptr` as it does `sym_addr`'s.

## `cfg_cleanup` (phase 2, item 2)

Checker `checkCfgCleanup` (`CfgCleanup.lean`), per design §4.3 as corrected by review 1 C-4 and
M-4.  What it checks:

- the entry keeps its id, the parameters are the input's, the output is machine IR; the input's
  dominator tree is valid and the input in strict SSA on it;
- surviving blocks: reachable from the entry once each block is cut after its first call to a
  claimed-noreturn function (`liveSet`, `cut`);
- each output block is the merge chain of surviving input blocks from the input block of its id
  (`chainFrom`, checked by `linksOk`).  A link from `c` to `n`: `c` is uncut, its terminator goes
  to `n` by every slot (`termRel` against `jump n`), each slot through tunnel blocks; `n` is no
  output block; `n`'s surviving predecessors are the ends of those paths.  This covers Sonatina's
  `merge_linear_successor` after `fold_trampoline_block` and a branch collapsed to `jump`;
- the output body is the chain's statements, each operand through `σ`, in order, with the same
  results (`chainBody`); the last block cut by a noreturn call keeps its statements up to the
  call and the output ends `unreachable`;
- the terminator: `termRel` slot by slot against the last block's, through `σ`; a slot reaches
  its output target through tunnel blocks (no statements, a `jump`, surviving, no output block;
  `walk`), and each phi the target keeps takes, from the output block, the input phi's operand
  from the path's last block composed back through the tunnel blocks' phis (Sonatina's
  `forward_bridge_block`) and through `σ`; the composed operand is a use that dominates the
  chain's end (`useOk`), and the path's last block survives uncut (`arrive`);
- `σ`: inferred by rounds of trivial-phi resolution (`sigmaOf`, chains `v₁ ↦ v₂ ↦ x` resolved to
  their end), then checked: for a phi `v` of surviving block `B` whose value the output does not
  define, every operand from a surviving, uncut predecessor is `v` or, through `σ`, `x`, and some
  is `x`; `x` is a word immediate or a value `σ` does not map, defined strictly above `B` in the
  tree (`sigOk`);
- a phi of a surviving block is a value of the output only if the output block of its id keeps
  it (`phisDefOk`): the input binds the phis of merged and tunnel blocks, the output does not;
- instruction ids (`blockIdsOk`): output phis keep their ids, the output body has the chain's
  body ids in order, the terminator keeps its id (a `br`/`br_table` collapsed to `jump` too),
  and a trimmed block's `unreachable` is a new id, unless the input block already ended
  `call; unreachable`.

Proof (`CfgCleanupSound.lean`, `cfgCleanup_sound`, `cfgCleanup_stepSound`): the simulation `CR`
relates the output at `b` entered from `p'` to the input at `b` entered from the last block of
the input's path; the output's environment binds less (`EnvSub`) and only output values
(`DomSub`); the input carries `BlockInv` and the trivial-phi invariant at its predecessor
(`PointTPI`: each `v ↦ x` holds wherever `v`'s block is a tree ancestor-or-self); the phis kept
take related values (`PhiRel`).  One output block (`block_fol`) runs its chain against the
input's blocks, the input stepping alone through link terminators, tunnel blocks and merged
blocks' phis (`Fol`, `walk_run`, `chain_fol`), each step total by the definedness invariant.
`tpi_enter` keeps the invariant entering a block from a surviving, uncut predecessor: by `σ`'s
check, `ssa`'s phi uses, D1's edge condition, unique definitions, and the tree's antisymmetry
(`DomTree.anc_antisymm`, from `valid_root`, which the phase-1 notes said no proof needed; this
one does).  `tpi_stmt`: a statement binds no phi and no value above a phi's block.

Deviations and choices:
- The link condition is broader than "ends `jump n`" (a collapsed branch, tunnels); "`n` has the
  link as its only surviving predecessor" becomes "`n`'s surviving predecessors are the ends of
  the link's paths".  Soundness needs neither; they are kept as checks.
- Strict dominance of `x` is checked on the dominator tree of the uncut input: a trim that changes
  dominance makes the check reject (incomplete, not unsound).  The surviving set is not checked
  closed: the proof needs only that each chain, tunnel and arrival block is in it, which the
  check tests.
- `σ` also requires `x` among the operands (C-4's `x ∈ S`), which the proof does not use.
- Output `ssa` is not checked: the proof does not need it (an output use of an unbound value is
  stuck).
- `EnvW` (`Defined.lean`) now records that a bound word is below `2 ^ 256`, so `Val.as` of a
  phi's type is the identity on it.
- `edge_split`'s terminator check is `termRel (X.tgt b)`: its `br`/`br_table` → `jump` rule is
  "every slot relates to the target", which for `edge_split` accepts exactly what the old rule
  did.

## L2 (phase 2, ruling R-11.2)

(`evm_add_mod` and `evm_mul_mod` count as pure since `e4c6694`, cherry-picked from
`m1-schemas` `7c6254b`, so that there is one notion of purity.)

`L2.lean`, the equational lemma of design §5.3 and review M-1, general: for a well-formed
function in strict SSA on a valid tree, on a run from the entry (`l2`), at every point `(b, k)`
each statement of a reachable block that comes before the point (`Before`: in a strict tree
ancestor of `b`, or earlier in `b`) whose instruction is pure (`Inst.pure`: `bin`, `cmp`,
`is_zero`, `not`, `neg`, `ctz`, `ovf`, `cast`, `select`, `evm_add_mod`, `evm_mul_mod`) has its
results bound to the
instruction's values on the current environment, as their types (`PureInv`, `pureVals`, with
`runInst_pure`: such an instruction runs to `pureVals` or is stuck).  The proof: unique
definitions, `ssa`'s uses (an operand's definition comes before the statement), D1's edge
condition and the tree's antisymmetry; the preservation lemmas (`pureInv_enter`,
`pureInv_stmt`, `pureInv_take`, `pureInv_step`) serve simulations that walk the input
themselves, as `branch_canonicalize`'s does.  `clz` is not pure here (it traps before Osaka),
nor `keccak_words` or `sym_addr`/`sym_size`; adding one is a case of
`pureVals`, `runInst_pure` and `pureVals_congr`.

## `branch_canonicalize` and `branch_conditions` (phase 2)

What Sonatina does (`crates/codegen/src/optim/branch_canonicalize.rs` at `664cd128`; design
§4.4 and review M-3 describe less):
- `:70-88`: peel the condition through `is_zero` (and through `not` only when the argument is
  `i1`, which machine IR never has: on `i256` only `is_zero` is peeled), swapping the targets
  each time;
- `:91-97`: on the peeled value, a zero compare (`zero_compare_branch_rewrite`, `:210-259`:
  `eq x 0`, `eq 0 x`, `ne`, `gt x 0`, `lt 0 x`, `le x 0`, `ge 0 x` at `:244-252`) becomes a new
  `is_zero x` inserted before the terminator (`:257`), swapping as the compare says;
- `:98-109`: else a compare whose inverse is cheaper (`le`, `ge`, `sle`, `sge`, `ne`) becomes the
  inverse, a new compare inserted before the terminator (`insert_compare_before`, `:274`), the
  targets swapped;
- the peeled `is_zero`s and the replaced compare are deleted if dead.

The checker (`checkBranchCanon`, peel-only, by the coordinator's ruling): the output has the
input's blocks in order, with their ids and phis; each block's statements are the input's in
order less deleted `is_zero`s, each with one result that the output neither defines nor uses
(`bodyOk`, `deletable`, `unusedOk`); each terminator is the input's (`termRel` with equal
targets), or `br c' a' b'` for `br c a b` where `c` is `is_zero^k c'`, `k ≥ 1`, each `is_zero` a
statement of a reachable block, the targets swapped iff `k` is odd (`peelOk`); the input's tree
is valid and the input in SSA; instruction ids are kept (phis, terminators) or a subsequence
(statements).  `branch_conditions` (`machine/branch.rs`) is the case `k = 1` and uses the same
checker.  The proof (`branchCanon_sound`): block-for-block simulation (`BR`), the deleted
`is_zero`s input-only steps (total by the definedness invariant), the peeled branch's condition
read through L2 (`peel_sound`).

**OPEN:** the zero-compare → new `is_zero` rewrite (`:91-97`, `:244-257`) and the inverted-compare
rewrite (`:98-109`) are rejected and counted: 0 of 767 `branch_canonicalize` steps in the four
corpora (FeProofs `-O0` 0, `-O1` 73, `-Os` 73, the 265 sidecars of `corpus-v5-full` 621) use
them.  They come after
`coalesce_copies`; the fresh condition instruction is then a new output value, its term unfolded
through output definitions (ruling R-11.1).

## `coalesce_copies` (phase 2, ruling R-11.4, stages 1 and 2)

What Sonatina does (`crates/codegen/src/isa/evm/machine/copy.rs` at `machine-steps` `0585e54f`,
called last in `machine/pipeline.rs:76-79`; design §4.10 and review H-6 describe less):
- `copy_run` (`:109-172`), from each start position of a block, greedily, the longest valid
  prefix: `evm_mload` of the source address plus `32 i`, `evm_mstore` of load `i`'s result at the
  destination address plus `32 i`, with only `evm_mload`, `evm_mstore`, `add`, `sub` in the
  window (`:167`: any `add`/`sub`), `n ≥ 2` words, each load's result used once (`:131`);
- addresses as affine forms (`address`, `:69-107`): `add x imm`, `add imm x`, `sub x imm` chains
  of any length, to an immediate or a base value, offsets modulo `2 ^ 256`;
- all loads before the first store (snapshot), or both ranges constant (`u32`) and disjoint
  (`:149-155`); a constant address must have a `u32` range (`:152`); wrapping is left to EVM gas
  (`:156-158`);
- the last store is replaced in place (its instruction id) by `evm_mcopy dest src len`, `dest`
  and `src` the first store's and the first load's address operands as written, `len` a new
  immediate; the window's other instructions are erased if they have no result or an unused one
  (`:27-38`): the loads, the other stores, unused `add`/`sub`; used ones stay in place.

`coalesce_machine_copies` walks every block of the layout (`copy.rs:16-18` at `e39b70c4d`),
reachable or not, and
`address` follows `add`/`sub` definitions wherever they are; at `-O0` no `cfg_cleanup` runs before
it, so unreachable blocks of the lowered code reach it.  (At `-O1`/`-Os` the machine pipeline's
last `cfg_cleanup` comes before it, with only `lower_switches` and `branch_conditions` between.)

In the four corpora (FeProofs `-O0`/`-O1`/`-Os` and the 265 sidecars of `corpus-v5-full`): 229
steps, 819 copies; every change is a store replaced by `evm_mcopy` or a deleted `evm_mload`,
`evm_mstore` or `add`; source and destination normalize to constants in 676 copies (278 snapshot,
398 interleaved, none overlapping, none past `u32`), to a base value in 143 (all snapshot).

The checker (`checkCoalesce`, as of stage 2 and the unreachable blocks below): the output
has the input's blocks in order with their ids, phis and terminators; each output block the
input's tree reaches has the input block's statements in order, where
a window may become its kept `add`/`sub` statements, in order, then the copy (`cbodyOk`,
`keptOk`); a window (`runOk`) holds only loads with one result, stores, and `add`/`sub` with one
result, ends in a store, has `n ≥ 2` loads `l_i` at `s + 32 i` and `n` stores `t_i` of `l_i`'s
result at `d + 32 i` (`addrNorm` over the input's definitions in reachable blocks, a bounded
walk whose early stop only leaves a larger base), each load used once in the input function
(`useCount`), the copy `evm_mcopy d s (32 n)` with `d`, `s` the first store's and first load's
address operands and `32 n < 2 ^ 256`; snapshot (`loadsFirst`: no load after the window's first
store), or both ranges constant, each ending at or below `2 ^ 256` in `Nat` (the checker's own
bound, not the compiler's `u32`), and disjoint in `Nat`.  A snapshot run may be base-relative
(load `i` at `b + k + 32 i` modulo `2 ^ 256` for one base value `b`, store `i` likewise at
another or the same) and its ranges may end past `2 ^ 256`.  Deletions
are only a window's loads, its other stores and its `add`/`sub` (a deleted store is tied to its
window); no result of a window statement the output does not keep is defined in the output
(`keptOk`'s `fresh`) or used in it (`unusedOk'`).  The
copy's `d` and `s` are values the output must have bound at the copy: the check does not check
the output's SSA; an unbound operand makes the output stuck, which the simulation allows, and
`unusedOk'` keeps every value the output reads defined in it.  Several windows in one block and
in one function are accepted.  Instruction ids are checked for shape only (review 20, L-1):
`checkStep`'s `FuncSnap.wf` (one per line, distinct), and nothing compares the output's ids with
the input's; the proof needs no correspondence.  Tests: two words snapshot and interleaved, `add`/`sub` chains (the
arithmetic deleted, three words), a kept `add`, two runs in a block and one in another;
mutants: overlapping interleaved ranges, a length other than `32 n`, store `i` of another load,
a load used twice, an interleaved base-relative run, a deleted store outside a window, a changed
copy operand, non-contiguous addresses, another instruction in the window, one word, an
interleaved range past `2 ^ 256`, loads at two bases, a kept `add` moved after the copy.

**Unreachable blocks (review 20, M-1).**  `addrNorm` follows only definitions in blocks the input's
tree reaches (`stmtOf`, which its proof needs), so a run in an unreachable block whose addresses go
through that block's own `add`s was rejected, though the compiler coalesces it.  `blockOk` now
checks an unreachable block's id, phis and terminator only, not its statements: no run of the
input or the output enters it (the terminators are the input's), and the simulation steps only
reachable blocks (`kc_block` takes the reachability `BR` carries).  `unusedOk'` still covers the
whole output.  Tests: `kc_unreach` (Gemini's example; `cbodyOk` alone rejects its block, as the
check did before), `kc_unreach_any` (any body in an unreachable block); mutants
`kc_bad_unreach_term`, `kc_bad_unreach_used` (a deleted value used there), `kc_bad_reach_any`
(the same body with the block reachable).  No step of the corpora has such a run: every
`coalesce_copies` step was accepted before the change.

The other proved checkers: `cfg_cleanup` deletes unreachable blocks, and its check is driven by
the output's blocks, chains from the input's; `edge_split` reads no definitions; the schema
checkers' unfolding and pairing read definitions in any block (only SCCP's facts are restricted,
to the executable set, which the checker validates).  `branch_canonicalize`'s `isZeroArg` has the
same restriction as `stmtOf`, so a peel of a branch in an unreachable block whose `is_zero`s are
defined there is rejected; but Sonatina runs `BranchCanonicalize` right after `cfg_cleanup` in the
one round of `MACHINE_PASSES`, and `branch_conditions` after the round's last `cfg_cleanup`, so
neither sees an unreachable block; every `branch_canonicalize` step of the corpora is accepted
(`branch_conditions` has none).  Accepting it
would mean accepting a changed terminator in an unreachable block, not the same change; not done.

**Stage 2 (ruling R-11.4, review C-1), done:** the interpreter's `evm_mcopy` does not terminate
where a range ends past `2 ^ 256` (`mcopyIR`, below), the byte side is re-proved (`mcopy_oog`),
and the switch `allowBase` is gone: base-relative snapshot runs are accepted, and the bound is
no longer checked of snapshot runs.  Two conditions are new: `32 n < 2 ^ 256` (the copy's
literal; a window of `2 ^ 251` words would otherwise copy `32 n mod 2 ^ 256` bytes), and an
interleaved run's constant ranges must end at or below `2 ^ 256`, which stage 1 checked of every
run: without it the stores' wrapping addresses could reach a later load's word, which `Nat`
disjointness does not exclude.  Neither rejects a run of the corpora (all 398 interleaved copies
are constant, none past `u32`).  Tests: `kc_base`, `kc_base2` (one base; a base each),
`kc_past` (a constant range past `2 ^ 256`, accepted as the copy diverges there; it was the
stage-1 mutant `kc_bad_past`); mutants `kc_bad_base_inter`, `kc_bad_past_inter`,
`kc_bad_two_base` (loads at two bases).

Proof (`CoalesceSound.lean`, `coalesce_sound`, `coalesceCopies_stepSound`; no hypothesis beyond
`StepSound.of_func`'s): the block-for-block simulation of `branch_canonicalize` (`BR`, `BMid`,
`kc_stmts`), a window in place of a deleted `is_zero`.  In a window (`win_walk`) the input runs
each statement and the output its kept `add`/`sub` alongside, in order, binding the same values
(`pureVals_sub`); the window's other statements bind results the output does not define
(`fresh`), so the output's environment still binds less.  Memory (`WInv`): each load of the
window so far is bound to the word of the start memory `m₀` at its address, and the memory is
`m₀` with, in order, the word of `m₀` at load `i`'s address written at store `i`'s (`writes`),
the addresses as the environment binds them; an operand of an earlier statement of the window
keeps its value (`keep_operand`: what defines it comes before).  A load reads `m₀`: it comes
before every store (`loadsFirst`), or, constant and in bounds, its word is disjoint from every
store's so far (`writes_read`).  Store `i` writes load `i`'s word unchanged
(`toByteArray_uInt256`); `ssa` and unique definitions put that load before the store
(`store_load_before`).  At the copy (`win_fol`), L2 on the input at the window's end gives each
address as its base's value plus its `addrNorm` offset modulo `2 ^ 256` (`addrNorm_base_sound`),
so load `i`'s is `S + 32 i` and store `i`'s `D + 32 i` modulo `2 ^ 256`, `S` and `D` the copy's
operands.  If `S + 32 n` or `D + 32 n` exceeds `2 ^ 256`, the output's copy does not terminate
(`exec_mcopy_big`), which `Approx` allows.  Otherwise no address wraps, the writes are the
copy's (`writes_copyMem`, `CopyMem`), and since `ByteArray.write` reads its source before it
writes, that is the output's `mcopy` on a memory related to `m₀` (`copyMem_end`, `MemEq.write`).
So snapshot windows may overlap in either direction, and interleaved ones must be disjoint, as
the checker requires.

Two changes to the checker for the proof: (1) `keptOk` requires each window statement it does
not keep to have no result the output defines (`fresh`, the `deletable` of
`branch_canonicalize`).  The other checks imply it (argued, not proved in Lean): each output
statement equals the input statement it is matched with, the matched positions are distinct and
skip the dropped ones, the phis and parameters are the input's, and the input's definitions are
unique (`ssa`).  (2) The snapshot test is `loadsFirst` (no load after the first store) in place
of "the last load's index is below the first store's"; with a load in the window (`n ≥ 2` is
checked) the two agree.  The tests (`Tests.lean`, `kc_*`) are unchanged and pass.

## `lower_switches` (design §4.9, review H-5 and M-4)

What Sonatina does (`crates/codegen/src/isa/evm/machine/switch.rs` at `machine-steps-main`
`e39b70c4d`; the step runs when `pipeline.rs:56-60` picks the tree: `Auto` at Speed, `Tree` at
any level, never `Linear`; there is one algorithm, the strategy only decides whether it runs):
- candidates (`:30-60`): a block ending in a `br_table` with a default and more than 4 cases,
  every key an immediate; keys sorted by unsigned value (`to_u256`, `:46-52`); the gas
  heuristic `split_index` must split the whole table (`:57`);
- leaf size 4, or 8 when the block's live values and the scrutinee leave fewer than two slots
  of reach (`:76-93`); a table of at most that many cases is left as it is;
- `emit` (`:156-198`): if `split_index` does not split, the block ends in
  `br_table s D cases'` (the default kept); else, at `mid = len / 2`, two new blocks, the block
  ends in `v = lt s k; br v lower upper` with `k` the upper half's first key (as its operand),
  and the halves recurse, upper first; the root always splits (`:57`, the same heuristic);
- every tree instruction is new (`insert_inst_data_from` copies the attribution only); the old
  terminator is erased (`:119`);
- phis (`:114-118`, `:166-173`): each leaf appends to each destination's phis, once per
  destination, the operand from the root (`copy_phi_incoming_block`, `cfg_edit.rs:1110`), and
  after the tree the root's operands are removed (`remove_phi_incoming_from`): the order of a
  phi's operands changes.

What both corpora emit (`ls_shapes.py` over every step; v5 and v6 identical): 45 function steps
in the 265 (44 with one switch, one with six: 50 switches), 3 at FeProofs `-O1`, none at
`-O0`/`-Os`.  Trees, as `(lower upper)` with leaf sizes: 5 cases `(L2 L3)` 19 + 1 (`-O1`), 7
`(L3 L4)` 7, 8 `(L4 L4)` 6, 6 `(L3 L3)` 5 + 1, 11 `((L2 L3) (L3 L3))` 4 + 1, 10
`((L2 L3) (L2 L3))` 3, 13 `((L3 L3) (L3 L4))` 1, 12 `((L3 L3) (L3 L3))` 1, 9 `(L4 (L2 L3))` 1,
18 `((L4 (L2 L3)) (L4 (L2 L3)))` 1, 19 `((L4 (L2 L3)) ((L2 L3) (L2 L3)))` 1, 22
`(((L2 L3) (L3 L3)) ((L2 L3) (L3 L3)))` 1.  Every leaf is the input's cases on its interval in
sorted order; no leaf has more than 4 cases (the pressured size 8 is not exercised); every
pivot lies strictly inside its interval; a key 0 in 5 switches, none `2 ^ 256 - 1`; no
duplicate targets, no default that is also a case's target; 5 targets with phis (all in the
six-switch function), each reached from one leaf; one table kept (one case); every other block
and its instruction ids unchanged; no tree instruction reuses an id.

The checker (`checkLowerSwitches`, `LowerSwitches.lean`; one stage, nothing switched off): the
output's blocks of input ids, in the input's order, have the input's phis with each operand from
a lowered block `r` replaced by one from each leaf of `r`'s tree that goes there (`phiOk`:
semantically through `lab`, and exactly as a permutation of `expected`), and either the input's
statements and terminator (targets input blocks) or, lowered (`rootOk`), the input's
`br_table s D cs` with immediate keys and input targets, the input's statements, `v = lt s k`
(`v` a value the input does not mention, `pivot?`), `br v lo hi`; the trees (`nodeOk`, an
interval `[a, b)`, `[0, 2 ^ 256)` at the root, `[a, k)` towards `lo`, `[k, b)` towards `hi`,
`a < k < b`): an internal node a new block with no phis, exactly `v = lt s k` (fresh) and
`br v lo hi`; a leaf a new block with no phis or statements and exactly
`br_table s D cs'`, `cs'` the input's cases on the interval (`leafOk`), distinct keys, input
targets, and `lab` taking it to `r`; every new block a node of one tree, once, the trees' new
values distinct (`shapeOk`); instruction ids (`idsOk`): unchanged blocks keep theirs, a lowered
block keeps its phis' and statements' and has two new ones, new blocks new ones; the input's
dominator tree valid and the input in strict SSA.  The checker computes the trees and the
leaves' switches (`LSCtx.of`) and checks them; fuel is the output's block count plus one, an
exhausted walk rejects.

Proof (`LowerSwitchesSound.lean`, `lowerSwitches_sound`, `lowerSwitches_stepSound`; no
hypothesis beyond `StepSound.of_func`'s): the simulation `LSCtx.R` relates the output at an
input block to the input at it, the predecessor relabelled (`lab`, as `edge_split`'s), and the
output at a tree node of `r`'s switch, on `[a, b)`, to the input entering `t` from `r`, where the
input's scrutinee `v` is in `[a, b)` and `t` the input table's target for `v`
(design §5.4's "output at new block `n` from `p` ~ input entering `t` from `p`", the interval
lemma being `leafOk_sel`).  The output binds the trees' `lt` results, which the input does not,
so the environments agree on the values the input mentions (`Agree`, over `funcVars`), not
`EnvSub`: the input's statements and terminators run alike (`runStmtO_congr`,
`runTerm_congr`), and a fresh binding keeps the agreement.  A lowered block steps with the
input's block (its `lt` and `br` against the input's table, `runTerm_table`, `lt_br_run`, the
scrutinee read through the definedness invariant); a tree node steps alone, to a related state
with the input unmoved: `Sim.of_steps_env`, `Sim.of_steps` generalized to a stutter step that
binds (`Sim.of_steps` is now its corollary).

Choices: exactness the proof does not need is checked anyway (H-5, M-4): the permutation of
`expected`, `shapeOk`, `idsOk`, the leaves' distinct keys, the pivots' bounds, the type of the
`lt` result.  A phi's operands are compared as a permutation, since Sonatina moves the new ones
to the end (`ls_real_phi`).  Tests (`Tests.lean`, `ls_*`): two real records (BytesViewBounds,
and Order with six switches and target phis), a hand-written switch with keys 0 and
`2 ^ 256 - 1`, a default that is also a case's target, a target two leaves go to, phis and a
kept one-case table, and the same with phi operands reordered; mutants (each rejected by
`validateWith` and by the check alone, `lsCheck`): a pivot one above and one below, swapped
branch targets, a wrong leaf default, a missing key, a wrong target, a key in the other leaf,
an extra instruction in a new block, a condition that is an input value, `slt`, a leaf on
another scrutinee, a leaf with the switch's instruction id, a new block outside the trees, a
changed statement of the switch's block, a node that is an input block, a phi operand left on
the switch's block, one missing for a leaf, a wrong one for a leaf, the key `2 ^ 256 - 1` in the
lower leaf.

## Review 6 (phase 1) findings taken up in phase 2

- F-1: adopted.  `Parse.statement` rejects a `phi` line after a statement (phase 2's one change
  to `Parse.lean`); a scan of the repository's 58 JSON fixtures (1785 blocks) found no such line.
  `wf` checks the `insts` shape and distinct ids kernel side (`FuncSnap.idsOk`).
- F-2: adopted.  `ESCtx.predOf` takes the distinct blocks whose slots target the block.
- F-3: adopted.  `domTree` walks successors without repeats (`succMapOnce`); `valid` reads
  `succMap`.
- F-5: adopted for the symbols (above), and for the summary table in phase 2 item 2
  (`SummariesOk`, `NoRetHolds`).
- F-8: adopted (deviation 7).
- Not taken up here (out of item 1): F-4, F-6, F-7, F-9, F-10.

## Phase-1 history

Commits 7e6f2c1, 9dbd430 and 04f9f01 do not build alone (each needs a later commit); they were
left as they are.

## Memory past 2^256 (ruling 3 as changed by review C-1), implemented

Only `evm_mcopy` with `len > 0` and `src + len > 2^256` or `dst + len > 2^256` diverges in the
IR semantics.  The change is the interpreter's (`Interp.lean`), not the model library's:
`Fe.EVM.mcopy` is also the exported models' `copy_mem` (`FeProofs/Lib/Exported.lean`, and the
proofs of `AbiEncode` and `LimbSlice` over it), whose semantics stay as they were.

```lean
def mcopyIR (dest source len : UInt256) : FeM Unit :=
  if 0 < len.toNat ∧
      (UInt256.size < dest.toNat + len.toNat ∨ UInt256.size < source.toNat + len.toNat) then
    Fe.M.diverge
  else Fe.EVM.mcopy dest source len
```

`EvmOp.run .mcopy [d, s, l]` runs `mcopyIR d s l`, and the byte checker's `evRun .MCOPY` the
same (`CheckEvent.lean` imports `Interp.lean` for it).  The byte side (`check_sound`,
`checkSpills_sound`, statements unchanged): where `mcopyIR` diverges, the bytes' `MCOPY` step is
`.error .OutOfGass` (`mcopy_oog`), which `EvMoves`' first disjunct and `Exhausted` excuse.  The
gas fact is EVMLean's own (`Ethereum/Theory/ReturnDataBound.lean`): `memoryPaidByGas s :=
Cₘ s.activeWords + s.gasAvailable < 2 ^ 256`, which `Xstep_memoryPaidByGas_of_none` keeps through
every step that goes on (calls and creations included), and which a frame's first state has
(`memoryPaidByGas_initState`).  `Agree` carries it (`Agree.paid`), each step that builds an
`Agree` passing it on.  At `MCOPY`, EVMLean's `step_mcopy` checks the memory charge first; the
new size `M activeWords (max dst src) len` is above `2 ^ 251` words and below `2 ^ 256`, so
`Cₘ` of it is at least `2 ^ 493 ≥ 2 ^ 256 > Cₘ activeWords + gas`.  Other memory operations stay
total (C-1: a diverging read would make deleting a dead `mload` unsound).  Proofs adjusted:
`approx_mcopyIR` (the steps' `approx_auto`), the simp sets of `evRun_result`, `evm_run`,
`noPanic_evmRun` and `ir_step_nat` (which decides the bound by `omega` in `ir_clean`), and one
line of WETH9's `returnValue_run`.

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

- Phase 2 item 2, with `cfg_cleanup` checked (`scripts/MachineSteps.lean`, interpreted; its
  `steps` mode checks every function step, the replay trusting the record past each step):
  - FeProofs, complete sidecars (`m1-lean/corpus-v5b`, 20 contracts per level, 40 sections):
    with `edge_split,cfg_cleanup` allowed, `-O0` 19 accepted, 21 rejected at their first
    `coalesce_copies` step; `-O1` and `-Os` 1 accepted, 39 rejected at their first
    `branch_canonicalize` step.  Every `cfg_cleanup` step (92 at `-O1`, 91 at `-Os`) and every
    `edge_split` step (6, 89, 89) is accepted; no pass's summary table fails.
  - The `-O1` dialect corpus (`dialect/corpus-v5-full`; these counts include its
    `feproofs-O0/-O1/-Os` subdirectories, 325 sidecars and 650 sections in all, so FeProofs is
    counted twice): 24 accepted; 604 rejected at their first `branch_canonicalize` step, 21 at
    `coalesce_copies`, 1 at `known_bits_simplify`.  All 600 `cfg_cleanup` and 591 `edge_split`
    steps are accepted; no summary table fails.

- Phase 2, with `branch_canonicalize` and `branch_conditions` checked (sections accepted end to
  end with the four proved kinds; the per-step counts replay past steps that have no checker,
  trusting the record):
  - FeProofs `corpus-v5b`, 40 sections per level: `-O0` 19 accepted, 21 rejected at
    `coalesce_copies`; `-O1` 21 accepted, 19 rejected (first unproved kind: `scalar_canonicalize`
    8, `known_bits_simplify` 7, `sccp_fold` 4); `-Os` the same 21 and 8/7/4.  Every
    `branch_canonicalize` step (73 at `-O1` and `-Os`) is accepted.
  - The 265 sidecars of `corpus-v5-full` (top level only, 530 sections): 351 accepted; 179
    rejected, first at `known_bits_simplify` 80, `sccp_fold` 57, `scalar_canonicalize` 30,
    `lower_switches` 12.  All 621 `branch_canonicalize`, 417 `cfg_cleanup` and 407 `edge_split`
    steps are accepted; no summary table fails.  Unproved steps: `sccp_fold` 133,
    `known_bits_simplify` 94, `scalar_canonicalize` 48, `lower_switches` 45, `coalesce_copies`
    28, `gvn_rewrite` 23, `adce` 9, `gvn_prune` 4.

- Phase 2, with the `coalesce_copies` checker (stage 1; no proof yet) allowed as well, the
  sections accepted end to end by the checkers: FeProofs `-O0` 33 of 40 (7 rejected, all at a
  base-relative copy); `-O1` 21 of 40 and `-Os` 21 of 40 (first rejected kind unchanged:
  `scalar_canonicalize` 8, `known_bits_simplify` 7, `sccp_fold` 4); the 265: 351 of 530 (first
  rejected kind unchanged).  With the four proved kinds only: `-O0` 19, `-O1` 21, `-Os` 21, the
  265 351.

- With `coalesce_copies` proved (`StepKind.proved` now has five kinds), sections accepted end to
  end by `validate`'s kinds (`scripts/MachineSteps.lean`, interpreted): FeProofs `corpus-v5b`
  `-O0` 33 of 40 (7 rejected, all at a base-relative copy), `-O1` 21 of 40 and `-Os` 21 of 40
  (first rejected kind `scalar_canonicalize` 8, `known_bits_simplify` 7, `sccp_fold` 4); the 265
  sidecars of `corpus-v5-full`: 351 of 530 (`known_bits_simplify` 80, `sccp_fold` 57,
  `scalar_canonicalize` 30, `lower_switches` 12).  `coalesce_copies` steps accepted: `-O0` 81 of
  149, `-O1` 14 of 26, `-Os` 14 of 26, the 265 14 of 28; every rejected one is base-relative.  The
  step and section verdicts are the same as those of the checker before the two changes above.

- Stage 2 (base-relative runs accepted, `evm_mcopy` diverging past `2 ^ 256`), sections accepted
  end to end by `validate`'s kinds (`scripts/MachineSteps.lean`, interpreted): FeProofs
  `corpus-v5b` `-O0` 40 of 40 (33 before), `-O1` 21 of 40 and `-Os` 21 of 40 (unchanged; first
  rejected kind `scalar_canonicalize` 8, `known_bits_simplify` 7, `sccp_fold` 4); the 265
  sidecars of `corpus-v5-full`: 351 of 530 (unchanged; `known_bits_simplify` 80, `sccp_fold` 57,
  `scalar_canonicalize` 30, `lower_switches` 12).  `coalesce_copies` steps accepted: all 229
  (`-O0` 149, `-O1` 26, `-Os` 26, the 265 28).  The byte checker (`scripts/DialectSweep.lean`;
  its decision is unchanged): `checkSpills` 40 of 40 sections per level and 529 of 530, `check`
  34, 33, 33 and 520, the same verdicts as before.

- With `sccp_fold` and `known_bits_simplify` proved (`StepKind.proved` has seven kinds), on
  `chain-o1` before it merged `chain` `58f7d69`, sections accepted end to end by `validate`'s
  kinds: FeProofs `-O0` 33 (its 7 rejections the base-relative copies), `-O1` 21, 25 with
  `sccp_fold`, 29 with both; `-Os` 21, 25, 32; the 265 351, 403, 460.  The checker's changes for
  the proof leave every per-step verdict of `scripts/SchemasSteps.lean` as it was (`corpus-v5b`
  86 steps, `corpus-v5-full` 313, all accepted) and every mutant rejected (935 fact mutants, 3006
  output mutants), identical line for line to the earlier outputs.

- Merged `chain` (seven proved kinds, `coalesce_copies` stage 2), on corpus v5 (FeProofs
  `m1-lean/corpus-v5b`; the 265 `provable-pipeline/dialect/top265`, the top-level sidecars of
  `corpus-v5-full`) and corpus v6 (`provable-pipeline/corpus-v6/{feproofs,top265}`, Fe
  `provable-chain` `a4c2ab6eb`).  End to end: `scripts/MachineSteps.lean` with the seven kinds;
  per step: its `steps` mode; byte checker: `scripts/DialectSweep.lean`.  All interpreted.

  | corpus | byte checker `checkSpills` | `check` | end to end (`validate`) | first rejected kind |
  | --- | --- | --- | --- | --- |
  | v5 FeProofs `-O0` | 40/40 | 34/40 | 40/40 | none |
  | v5 FeProofs `-O1` | 40/40 | 33/40 | 29/40 | `scalar_canonicalize` 8, `lower_switches` 3 |
  | v5 FeProofs `-Os` | 40/40 | 33/40 | 32/40 | `scalar_canonicalize` 8 |
  | v5 the 265 | 529/530 | 520/530 | 460/530 | `lower_switches` 34, `scalar_canonicalize` 30, `gvn_prune` 4, `gvn_rewrite` 2 |
  | v6 FeProofs `-O0` | 40/40 | 34/40 | 40/40 | none |
  | v6 FeProofs `-O1` | 40/40 | 33/40 | 29/40 | `scalar_canonicalize` 8, `lower_switches` 3 |
  | v6 FeProofs `-Os` | 40/40 | 33/40 | 32/40 | `scalar_canonicalize` 8 |
  | v6 the 265 | 529/530 | 520/530 | 460/530 | `lower_switches` 34, `scalar_canonicalize` 30, `gvn_prune` 4, `gvn_rewrite` 2 |

  Every rejection end to end is a kind with no proof (`kind not allowed`).  No section's verdict
  differs between v5 and v6; v5's outputs are identical line for line to `chain-o1`'s after its
  merge (end to end and per step) and to `chain`'s stage-2 run (byte checker).  The 265's
  `checkSpills` rejection is one function outside the class (`default_recursive` in v5,
  `direct_dynamic` in v6).

  Function steps accepted, v5 / v6 (`-O0`, `-O1`, `-Os`, the 265); none of a proved kind is
  rejected, no summary table fails:

  | kind | v5 | v6 |
  | --- | --- | --- |
  | `edge_split` | 6, 89, 89, 407 | 6, 93, 89, 413 |
  | `cfg_cleanup` | 0, 92, 91, 417 | 0, 96, 91, 423 |
  | `branch_canonicalize` | 0, 73, 73, 621 | 0, 73, 73, 617 |
  | `coalesce_copies` | 149, 26, 26, 28 | 149, 24, 24, 26 |
  | `sccp_fold` | 0, 35, 35, 133 | 0, 35, 35, 131 |
  | `known_bits_simplify` | 0, 8, 8, 94 | 0, 8, 8, 95 |
  | no proof: `scalar_canonicalize` | 0, 25, 19, 48 | 0, 25, 19, 48 |
  | no proof: `lower_switches` | 0, 3, 0, 45 | 0, 3, 0, 45 |
  | no proof: `gvn_rewrite` | 0, 16, 10, 23 | 0, 16, 10, 23 |
  | no proof: `gvn_prune` | 0, 0, 0, 4 | 0, 0, 0, 4 |
  | no proof: `adce` | 0, 8, 6, 9 | 0, 12, 6, 13 |

  `branch_conditions` has no step in either corpus.  No `known_bits_simplify` step is rejected as
  a demand round: every sidecar of both corpora has `demanded_bits: null`.

- With `lower_switches` proved (`StepKind.proved` has eight kinds; `chain-ls`, after merging
  `chain` `c3b8225`), on the same corpora (`lower-switches/measure.sh`, `scripts/MachineSteps.lean`
  end to end and `steps`, interpreted; the byte checker and the schema verdicts were not rerun,
  nothing they read changed):

  | corpus | end to end (`validate`), before | after | first rejected kind |
  | --- | --- | --- | --- |
  | v5 FeProofs `-O0` | 40/40 | 40/40 | none |
  | v5 FeProofs `-O1` | 29/40 | 32/40 | `scalar_canonicalize` 8 |
  | v5 FeProofs `-Os` | 32/40 | 32/40 | `scalar_canonicalize` 8 |
  | v5 the 265 | 460/530 | 494/530 | `scalar_canonicalize` 30, `gvn_prune` 4, `gvn_rewrite` 2 |
  | v6 FeProofs `-O0` | 40/40 | 40/40 | none |
  | v6 FeProofs `-O1` | 29/40 | 32/40 | `scalar_canonicalize` 8 |
  | v6 FeProofs `-Os` | 32/40 | 32/40 | `scalar_canonicalize` 8 |
  | v6 the 265 | 460/530 | 494/530 | `scalar_canonicalize` 30, `gvn_prune` 4, `gvn_rewrite` 2 |

  Every `lower_switches` step is accepted: `-O1` 3 and the 265 45, in v5 and v6 (none at `-O0`
  and `-Os`); the other kinds' per-step counts are those of the table above, none rejected, no
  summary table failing.

## The top theorem: what it covers (review 20, M-3)

`machine_sound_of_sound` reads of the bytes only `Sound s` (review 6, F-6): the runtime bytes
refine the machine IR's runtime and the init bytes its constructor, at `P1`.  So the statements
are layered: `machine_sound_of_sound` (any allowed kinds, `Sound s`), `machine_sound_proved_of_sound`
(`validate`, `Sound s`), and two corollaries for the two ways the repository has of proving
`Sound s`:

- `machine_sound_proved`: `validate` for both records and `check s = true` (`check_sound`).
  `check s = checkSpills s && s.noSpills`, so it applies only to sidecars without memory spills.
  Its statement is unchanged.
- `machine_sound_spills_proved`: `validate` for both records, `checkSpills s = true` and
  `FrameSafe s` (`checkSpills_sound`), for sidecars with spills.

`check` and `checkSpills` are verdicts on the whole sidecar (every section the object has an
entry for), `validate` on one section's record; the theorems need both sections' records.

**Which theorem applies**, at `42e8439`, both corpora (`validate` per section from
`scripts/MachineSteps.lean`; `check` and `checkSpills` from `scripts/DialectSweep.lean`, whose
outputs at `6060422` are reused: no file the byte checker reads has changed since).  (a)
`validate` and `check`: `machine_sound_proved` applies, no hypothesis left; (b) `validate` and
`checkSpills` but not `check`: only `machine_sound_spills_proved`, under `FrameSafe`; (c) neither.
Sections (each with its own section's byte verdict), then sidecars (both records and the
sidecar's verdicts, as the theorems take them).  v5 and v6 agree section for section:

| set | sections (a) / (b) / (c) | sidecars (a) / (b) / (c) |
| --- | --- | --- |
| FeProofs `-O0` | 34 / 6 / 0 of 40 | 14 / 6 / 0 of 20 |
| FeProofs `-O1` | 29 / 0 / 11 of 40 | 9 / 0 / 11 of 20 |
| FeProofs `-Os` | 32 / 0 / 8 of 40 | 12 / 0 / 8 of 20 |
| the 265 | 460 / 0 / 70 of 530 | 196 / 0 / 69 of 265 |

The (b) sections are the six `-O0` runtimes with memory spills: Bn254Add, Bn254Mul, Ecrecover,
EcrecoverPrecompile, Modexp, Ripemd160 (Blake2F's `-O0` runtime has none).  At `-O1`, `-Os` and
in the 265 every section with spills (7, 7 and 9; the precompiles, `erc4337.EntryPoint`,
`msg_nested_array_arg.Caller`) is rejected by `validate` (`scalar_canonicalize`, once
`gvn_prune`), and the one section `checkSpills` rejects (the runtime of `storage_map_recursive_views.C`) by
`validate` too (`lower_switches`).  Every (c) is a
`validate` rejection; no sidecar both of whose records validate fails `checkSpills`.

**`FrameSafe s`** (`FrameSafe.lean`) asks that the machine IR with its spill stores, under the
sidecar's spill plan (`Sidecar.spillPlan`, found by walking the bytes against the instrumented
machine IR, untrusted), end as the machine IR does: `Implements (s.model .machine)
(s.spilledModel s.spillPlan) CalldataFits` on every message call whose calldata fits, and
`ImplementsDeploy` likewise on every deployment.  The instrumented model panics with
`spillClobbered` where a statement changes a word whose value the bytes reload later, so
`FrameSafe` says no statement clobbers a live spill word, and that no spill store overwrites IR
data the IR reads later.  It is proved only for sidecars without spills
(`frameSafe_of_noSpills`, through which `check_sound` goes).  For no sidecar with spills does the
repository prove it: `fixedSlotsSafe` (inside `checkSpills`) rejects one way of breaking it (a
spill to `0x00`/`0x20` read back as IR data) and is not a proof of it, and
`scripts/frame_safe_diff.sh` (`SpillDiff.lean`) tests it by running the two models on inputs
(precompile generators and two corpus drivers; README, "Relying on `FrameSafe`").

**The records** `rr` and `ri` are arguments of every statement here, not parts of `s`: `Sidecar`
keeps no record (a section's `Lowering` has no field for one).  What ties them to `s` is
`validate`: each record's composition, from its lowered functions through its steps, must be the
section's machine IR (`s.machineOf`, compared function by function), under the section's symbols
(`s.symbolsOf`).  What is not tied: that they are the sidecar's own `machine_steps` (any records
`validate` accepts will do; `machine_steps` in `Read.lean` reads the record of a section from the
same JSON file `sonatina_sidecar` reads `s` from, at elaboration, and that a use passes those is
the user's), and that a record's lowered functions are what lowering made of `s`'s source IR.
For a record with no passes the lowered functions are the machine IR and the theorem restates
`check_sound`.  No projection from `s` to its records exists, so there is no corollary for `s`'s
own records: it would need the record in the sidecar (a `machineSteps` field of `Lowering`, which
`Syntax.lean` cannot have as `Record.lean` imports it: the record types would move below
`Syntax.lean`, or the sidecar get a second structure), `parseLowering` reading `machine_steps`
with `Read.parseMachineSteps`, and `Sidecar.records` projecting both sections'.

## Not done

- `branch_canonicalize`'s zero-compare and inverted-compare rewrites (OPEN, above).
- The summary table's effect and `will_return` claims are not checked (no consumer).
- `known_bits_simplify`'s demand rounds, switched off (`demandRounds`; plan in `SCHEMAS-NOTES.md`).
- `known_bits_simplify`'s `sdiv` by a power of two (`signed_pow2_division`, replacing
  `evm_sdiv x 2^k` in place by `shr k x` or `sar k x`): a known rewrite the checker rejects (an
  in-place change of an instruction, review 20 M-2).  Corpus v6 is the regenerated corpus at the
  compiler that has it, and no `known_bits_simplify` step of it changes an `evm_sdiv`: 0
  occurrences (every such step of v6 is accepted, which an in-place change is not).
