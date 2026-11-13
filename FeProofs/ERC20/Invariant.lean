import FeProofs.ERC20.ConservationBytecode
import Fe.EVM.RefineInvariant

/-!
# FeERC20: conservation through every message call

The token at `a` keeps the balances of the holders `S` adding up to the recorded supply through
every message call and creation, at every depth, whoever makes them, in every execution in which
each successful frame at `a` is admitted: its calldata is shorter than `2 ^ 64` bytes, and the
holders cover it (`Covers`).  An instance of `Fe.EVM.refinesOn_keeps`, from the certificate of the
exported model (`feERC20RefinesExported`) and its conservation (`Exported.runtime_conserves`).
The token makes no external call, so its model never uses `Deeper`.
-/

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

namespace FeProofs.ERC20

/-- The balances of the holders `S` in an account's storage add up to its recorded supply:
    `Conserved`, on the account. -/
def ConservedAcc (S : List UInt256) (acc : Account) : Prop :=
  (S.map fun h => (acc.storage.getD (Model.balanceSlot h) ⟨0⟩).toNat).sum
    = (acc.storage.getD Model.totalSupplySlot ⟨0⟩).toNat

theorem conserved_iff {c : AccountAddress} {σ : AccountMap} {S : List UInt256} {acc : Account}
    (h : σ[c]? = some acc) : Conserved c σ S ↔ ConservedAcc S acc := by
  simp [Conserved, balanceSum, balance, supply, storageAt, Std.ExtTreeMap.get?_eq_getElem?, h,
    Option.option, ConservedAcc]

/-- The token's account: it runs the ERC20 bytecode, and its holders' balances add up to the
    supply. -/
def Token (S : List UInt256) (acc : Account) : Prop :=
  acc.code = feERC20Bytecode ∧ ConservedAcc S acc

/-- A frame at the token is admitted when its calldata fits and the holders cover it. -/
def Admits (S : List UInt256) (_ : AccountMap) (I : ExecutionEnv) : Prop :=
  CalldataFits I ∧ Covers S I

set_option maxRecDepth 100000 in
theorem bytecode_size_ne_zero : feERC20Bytecode.size ≠ 0 := by
  rw [feERC20Bytecode, ByteArray.size_append]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _))

theorem token_admissible (S : List UInt256) :
    Admissible (Token S) (· = feERC20Bytecode) where
  balance _ _ h := h
  code acc h := by
    rw [h.1]
    exact bytecode_size_ne_zero
  trusted _ h := h.1

theorem model_keeps (a : AccountAddress) {S : List UInt256} (hS : CollisionFree S) :
    ModelKeeps a (Token S) (· = feERC20Bytecode) (Admits S) Exported.contract := by
  intro I σ A feed out w howner _ _ hadm _ hH hrun acc acc' hacc hacc' hcode
  obtain ⟨acc0, h0, hP⟩ := hH
  rw [hacc] at h0
  cases h0
  refine ⟨hcode.trans hP.1, ?_⟩
  have hcons : Conserved I.codeOwner σ S := by
    rw [howner]
    exact (conserved_iff hacc).2 hP.2
  have hc' := Exported.runtime_conserves (w := World.init σ A feed)
    (by simp [World.init, UInt256.size]) hadm.1 hS hadm.2 hcons hrun
  rw [howner] at hc'
  exact (conserved_iff hacc').1 hc'

/-- **Every message call and creation conserves the token's supply.**  For the token at `a` and
    holders `S` whose balance slots do not collide: every message call and every creation, at any
    depth, that starts where `a` runs the ERC20 bytecode with the holders' balances adding up to
    the supply, and in whose execution every successful frame at `a` has calldata shorter than
    `2 ^ 64` bytes and is covered by `S`, ends where the same holds. -/
theorem every_call_conserves (a : AccountAddress) {S : List UInt256} (hS : CollisionFree S)
    (e : Fin 1025) :
    ThetaGood a (Token S) (· = feERC20Bytecode) (Admits S) e
      ∧ LambdaGood a (Token S) (Admits S) e :=
  refinesOn_keeps Exported.feERC20RefinesExported (token_admissible S)
    (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩)
    (fun _ _ _ h => h.1) (model_keeps a hS) e

end FeProofs.ERC20
