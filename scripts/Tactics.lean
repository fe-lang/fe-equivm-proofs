import FeProofs.Common.Tactics

/-! Side-goal search regressions. Run: `lake env lean scripts/Tactics.lean`. -/

open Lean Meta Elab Tactic Ethereum Reasoning.Theory FeProofs.RDTactic

-- These regressions deliberately keep irrelevant hypotheses in the search context.
set_option linter.unusedVariables false

elab "test_rd_discharge" u:(rdUsing)? : tactic => withMainContext do
  let g ← getMainGoal
  unless ← discharge g (← elabHints (hintsOf u)) do
    throwError "side-goal search failed"
  replaceMainGoal []

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
