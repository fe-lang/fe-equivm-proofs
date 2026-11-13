import FeProofs.Constant.ModelCorrect
import Fe.EVM.RefineInvariant

/-!
# FeConstant: no message call changes the contract's storage

An instance of `Fe.EVM.refines_keeps`: the account at `a` running the FeConstant bytecode keeps
whatever storage it has, through every message call and creation, at every depth, whoever makes
them.  The model never writes storage and makes no call, so `ModelKeeps` is immediate.
-/

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

namespace FeProofs.Constant

/-- The account runs the FeConstant bytecode and has storage `st`. -/
def Fixed (st : Storage) (acc : Account) : Prop :=
  acc.code = feConstantBytecode ∧ acc.storage = st

theorem fixed_admissible (st : Storage) : Admissible (Fixed st) (· = feConstantBytecode) where
  balance _ _ h := h
  code acc h := by
    rw [h.1]
    decide
  trusted _ h := h.1

theorem model_keeps (a : AccountAddress) (st : Storage) :
    ModelKeeps a (Fixed st) (· = feConstantBytecode) Model.contract
      fun I => I.calldata.size < UInt256.size := by
  intro I σ A feed out w _ _ _ _ hH hrun
  have hsame : ∀ r, Model.runtime.exec I (World.init σ A feed) = r →
      r = some (.ok (out, w)) ∨ r = some (.error (.stop out w)) → w.accounts = σ := by
    intro r hr hr'
    by_cases hsel : selIs I (feConstantSelBytes 0)
    · by_cases hwv : I.weiValue = ⟨0⟩
      · rw [runtime_answer hsel hwv] at hr
        subst hr
        rcases hr' with h | h <;> cases h
        rfl
      · rw [runtime_answer_value hsel hwv] at hr
        subst hr
        rcases hr' with h | h <;> cases h
    · by_cases hsz : 4 ≤ I.calldata.size
      · rw [runtime_noMatch hsz hsel] at hr
        subst hr
        rcases hr' with h | h <;> cases h
      · rw [runtime_short (by omega)] at hr
        subst hr
        rcases hr' with h | h <;> cases h
  exact (hsame _ rfl hrun) ▸ hH

/-- Every message call and creation, at any depth, keeps the storage of an account that runs the
    FeConstant bytecode. -/
theorem feConstantKeepsStorage (a : AccountAddress) (st : Storage) (e : Fin 1025) :
    ThetaGood a (Fixed st) (· = feConstantBytecode) e ∧ LambdaGood a (Fixed st) e :=
  refines_keeps feConstantRefinesModel (fixed_admissible st)
    (fun code h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩)
    (model_keeps a st) e

end FeProofs.Constant
