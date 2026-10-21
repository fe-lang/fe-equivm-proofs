import FeProofs.Common.Tactics

/-! Side-goal search regressions. Run: `lake env lean scripts/Tactics.lean`. -/

open Lean Meta Elab Tactic Ethereum Reasoning.Theory Reasoning.Reach FeProofs.RDTactic

-- These regressions deliberately keep irrelevant hypotheses in the search context.
set_option linter.unusedVariables false

elab "test_rd_discharge" u:(rdUsing)? : tactic => withMainContext do
  let g ← getMainGoal
  unless ← discharge g (← elabHints (hintsOf u)) do
    throwError "side-goal search failed"
  replaceMainGoal []

elab "test_rd_reject " p:term u:(rdUsing)? : tactic => withMainContext do
  let s ← saveState
  let ty ← Term.elabTerm p (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let g ← mkFreshExprMVar ty
  let start ← IO.getNumHeartbeats
  let ok ← discharge g.mvarId! (← elabHints (hintsOf u))
  let elapsed := ((← IO.getNumHeartbeats) - start) / 1000
  s.restore
  if ok then throwError "side-goal search accepted an excluded branch"
  if elapsed > 1000 then throwError "rejecting the branch took {elapsed} heartbeats"

elab "test_rd_parameter" : tactic => withMainContext do
  let s ← saveState
  let w ← mkFreshExprMVar (mkConst ``UInt256) (kind := .natural)
  let zero := mkApp (mkConst ``UInt256.ofNat) (mkNatLit 0)
  let g ← mkFreshExprMVar (← mkEq w zero)
  let ok ← discharge g.mvarId! (← elabHints #[← `(term| by rfl)])
  let assigned ← w.mvarId!.isAssigned
  let zeroChosen ← isDefEq (← instantiateMVars w) zero
  s.restore
  unless ok && assigned && zeroChosen do
    throwError "side-goal search rejected a valid unresolved parameter"

-- Unrelated symbolic arithmetic must not consume a unification budget per hypothesis.
set_option maxHeartbeats 2000 in
example (I : ExecutionEnv) (a b : UInt256)
    (hcanon : (calldataWord I.calldata 4).toNat < 2 ^ 160)
    (henough : a.toNat ≤ b.toNat) (hfit : a.toNat + b.toNat < UInt256.size) :
    ([] : List UInt256).length + 6 ≤ 1024 := by
  test_rd_discharge

set_option maxHeartbeats 2000 in
example (I : ExecutionEnv) (a b : UInt256)
    (hcanon : (calldataWord I.calldata 4).toNat < 2 ^ 160)
    (henough : a.toNat ≤ b.toNat) (hfit : a.toNat + b.toNat < UInt256.size)
    (hperm : I.perm = true) : I.perm = true := by
  test_rd_discharge

-- Symbolic hints must not delay a closed stack bound either.
set_option maxHeartbeats 2000 in
example (a b : UInt256) (h : UInt256.lt a b = UInt256.ofNat 0) :
    ([] : List UInt256).length + 6 ≤ 1024 := by
  test_rd_discharge using [h]

-- Stack bounds can use a local fact even when matching it requires reducing length.
set_option maxHeartbeats 2000 in
example (R : List UInt256) (ret : UInt256) (hR : R.length + 9 ≤ 1024) :
    (ret :: R).length + 8 ≤ 1024 := by
  test_rd_discharge

-- Explicit hints retain default-transparency matching of ordinary definitions.
def testPerm (I : ExecutionEnv) : Bool := I.perm

set_option maxHeartbeats 2000 in
example (I : ExecutionEnv) (h : testPerm I = true) : I.perm = true := by
  test_rd_discharge using [h]

-- A local word inequality may differ only in the spelling of the zero literal.
set_option maxHeartbeats 2000 in
example (I : ExecutionEnv) (h : I.weiValue ≠ (⟨0⟩ : UInt256)) :
    I.weiValue ≠ UInt256.ofNat 0 := by
  test_rd_discharge

-- A hint that needs the goal still elaborates there; a bad hint cannot insert sorry.
example (a : UInt256) : a = a := by
  test_rd_discharge using [by rfl]

example (P : Prop) : P → P := by
  fail_if_success test_rd_discharge using [by exact unknown_rd_hint]
  intro h
  exact h

-- These assertions inspect a temporary side goal and restore the proof state.
-- A known opposite branch condition must fail before trying unrelated symbolic hints.
set_option linter.unusedTactic false in
set_option maxHeartbeats 2000 in
example (ee : ExecutionEnv) (p cds : UInt256) (mem : ByteArray)
    (h1 : UInt256.gt p cds = UInt256.ofNat 0)
    (h2 : UInt256.gt (UInt256.ofNat 32) (UInt256.sub cds p) = UInt256.ofNat 0)
    (h3 : UInt256.lt (p + UInt256.ofNat 32) p = UInt256.ofNat 0)
    (h4 : UInt256.lt cds (p + UInt256.ofNat 32) = UInt256.ofNat 0)
    (h5 : UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes p.toNat 32))
      (UInt256.sub cds (p + UInt256.ofNat 32)) = UInt256.ofNat 0)
    (h6 : UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes p.toNat 32))
      (UInt256.ofNat 18446744073709551552) = UInt256.ofNat 0)
    (h7 : UInt256.isZero (UInt256.lt (UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (uInt256OfByteArray (ee.calldata.readBytes p.toNat 32) + UInt256.ofNat 63))
      (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hfp : UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 255) = UInt256.ofNat 0) :
    True := by
  test_rd_reject (UInt256.gt p cds ≠ UInt256.ofNat 0) using [h1, h2, h3, h4, h5, h6, h7, hfp]
  trivial

set_option linter.unusedTactic false in
set_option maxHeartbeats 2000 in
example (p cds : UInt256) (h : UInt256.gt p cds ≠ UInt256.ofNat 0) : True := by
  test_rd_reject (UInt256.gt p cds = UInt256.ofNat 0) using [h]
  trivial

-- Matching an opposite must not choose an unresolved block parameter and reject a valid goal.
set_option linter.unusedTactic false in
example (a : UInt256) (h : a ≠ UInt256.ofNat 0) : True := by
  test_rd_parameter
  trivial
