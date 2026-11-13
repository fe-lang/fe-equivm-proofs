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

/-! ## Deployment -/

theorem storageAt_eq_getD (c : AccountAddress) (σ : AccountMap) (s : UInt256) :
    storageAt c σ s = (σ.getD c default).storage.getD s ⟨0⟩ := by
  unfold storageAt
  rcases h : σ[c]? with _ | acc
  · rw [Std.ExtTreeMap.get?_eq_getElem?, h,
      Std.ExtTreeMap.getD_eq_fallback (t := σ) (by simpa using h)]
    exact Std.ExtTreeMap.getD_empty.symm
  · rw [Std.ExtTreeMap.get?_eq_getElem?, h, Std.ExtTreeMap.getD_eq_getD_getElem? (t := σ), h]
    rfl

theorem conserved_iff_getD {c : AccountAddress} {σ : AccountMap} {S : List UInt256} :
    Conserved c σ S ↔ ConservedAcc S (σ.getD c default) := by
  simp only [Conserved, balanceSum, balance, supply, storageAt_eq_getD, ConservedAcc]

/-- The exported constructor, run at the new address from empty storage by a deployer among the
    holders, leaves the ERC20 bytecode with the holders' balances adding up to the supply. -/
theorem deploy_model {S : List UInt256} (hS : CollisionFree S) (v : UInt256) (c s : AccountAddress)
    (hdeployer : UInt256.ofNat s.val ∈ S) (I : Env) (σ : AccountMap) (A : Substate)
    (feed : List Supply) (out : ByteArray) (w : World) (hc : I.codeOwner = c) (hs : I.source = s)
    (hempty : (σ.getD c default).storage = default)
    (hrun : Succeeds ((Exported.contract.init (ctorTail v) >>= fun tail =>
      pure (feERC20Bytecode ++ tail)).exec I (World.init σ A feed)) out w) :
    Token S {w.accounts.getD c default with code := out} := by
  have hmem : (World.init σ A feed).memory.size + 1024 < UInt256.size := by
    simp [World.init, UInt256.size]
  have hzero : ∀ h ∈ S, balance I.codeOwner (World.init σ A feed).accounts h = ⟨0⟩ := by
    intro h _
    rw [balance, storageAt_eq_getD, hc]
    simp only [World.init, hempty]
    rfl
  have hcons := Exported.init_conserves hmem hS (hs ▸ hdeployer) hzero hrun
  rw [hc, conserved_iff_getD] at hcons
  refine ⟨?_, hcons⟩
  obtain ⟨w'', hrun', -⟩ := (Exported.init_endsAs v feERC20Bytecode I _ hmem).succeeds hrun
  rcases hrun' with hrun' | hrun' <;> simp only [M.exec_bind] at hrun' <;> split at hrun' <;>
    simp at hrun' <;> rename_i hinit
  · exact hrun'.1.symm
  · subst hrun'
    exact absurd hinit (init_noStop _ I _ _ _)

/-- **Deployment conserves.**  A creation of the ERC20 creation bytecode with argument `v` that
    succeeds, made by a holder in `S` with write permission, ends with the new address running the
    ERC20 bytecode and the holders' balances adding up to the supply.  The new address starts with
    empty storage: `Lambda` creates only at an address without nonce, code or storage. -/
theorem deploy_conserves_token {S : List UInt256} (hS : CollisionFree S) {v : UInt256}
    {L : LambdaCall} (hi : L.i = feERC20CreationBytecode ++ v.toByteArray) (hw : L.w = true)
    (hdeployer : UInt256.ofNat L.s.val ∈ S) (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Token S) L.run.2.1 :=
  refinesDeploy_holds Exported.feERC20DeployRefinesExported (args := ctorTail v) ⟨v, rfl⟩
    (by rw [Exported.ctorTail_eq]; exact hi) hw
    (fun I σ A feed out w hc hs hempty hrun =>
      deploy_model hS v L.addr L.s hdeployer I σ A feed out w hc hs hempty hrun) hz

/-! ## Transactions -/

/-- **Every transaction conserves.**  A transaction that starts where the token at `a` runs the
    ERC20 bytecode with the holders' balances adding up to the supply, whose sender has no code
    (EIP-3607), whose data fits a word, and whose execution admits every successful frame at `a`,
    ends where the same holds, if `a` is not in the self-destruct set it returns. -/
theorem every_transaction_conserves (a : AccountAddress) {S : List UInt256}
    (hS : CollisionFree S) {σ σ' : AccountMap} {H_f : ℕ} {H : BlockHeader}
    {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress} {A : Substate} {z : Bool}
    {gu : UInt256} (hH : Holds a (Token S) σ)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hadmit : TxAdmitted a (Admits S) σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu))
    (hsd : a ∉ A.selfDestructSet.toList) :
    Holds a (Token S) σ' :=
  tx_holds (token_admissible S)
    (frameHyp_of_refinesOn Exported.feERC20RefinesExported
      (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩)
      (fun _ _ _ h => h.1) (model_keeps a hS))
    (fun _ h => h) hH hsender hdata hadmit hΥ hsd

end FeProofs.ERC20
