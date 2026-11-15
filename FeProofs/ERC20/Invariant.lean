import FeProofs.ERC20.ConservationBytecode
import Fe.EVM.RefineInvariant

/-!
# FeERC20: conservation through every message call

The token at `a` keeps the balances of the holders `S` adding up to the recorded supply through
every message call and creation, at every depth, whoever makes them, in every execution in which
each successful frame at `a` is admitted: its calldata is shorter than `2 ^ 64` bytes, and the
holders cover it (`Covers`).  An instance of `Fe.EVM.refinesOn_keeps`, from the certificate of the
exported model (`feERC20RefinesExported`) and its conservation (`Exported.runtime_conserves`).
The token makes no external call, so its model never uses `Deeper`, and admission asks nothing of
the calls a frame at the token makes (`callsAt := fun _ _ _ _ _ _ => True`).  Conservation does
not depend on how a frame is entered (`Enters := fun _ _ _ => True`).

From deployment on: `deploy_conserves_token`, a successful creation of the creation bytecode by a
holder that has an account establishes the invariant at the new address (the new account's
storage starts empty, so every holder starts with no tokens), and `every_transaction_conserves`,
every transaction keeps it, under the hypotheses of `Ethereum.EVM.Invariant.tx_holds`: the sender
has no code, the data fits a word, and the outermost call is admitted.

The statements hold of any runtime and creation bytecode with `P0` certificates
(`every_call_keeps`, `deploy_keeps_token`, `every_transaction_keeps`).  The capstones are their
instances at the pinned bytecode, and `P1.every_call_conserves`, `P1.deploy_conserves_token` and
`P1.every_transaction_conserves` at the bytecode of `P1/`, through its `P1` certificates.  The
token's frames are admitted by their calldata and the holders alone (`callsAt` is `True`), so
`check_xiOk`, that the `P1` bytecode's frames make no call, would remove nothing from them: the
two sets of statements take the same hypotheses.
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

/-- The token's account: it runs `code`, and its holders' balances add up to the supply. -/
def TokenAt (code : ByteArray) (S : List UInt256) (acc : Account) : Prop :=
  acc.code = code ∧ ConservedAcc S acc

/-- The token's account: it runs the ERC20 bytecode, and its holders' balances add up to the
    supply. -/
def Token (S : List UInt256) (acc : Account) : Prop :=
  TokenAt feERC20Bytecode S acc

/-- A frame at the token is admitted when its calldata fits and the holders cover it. -/
def Admits (S : List UInt256) (_ : AccountMap) (I : ExecutionEnv) : Prop :=
  CalldataFits I ∧ Covers S I

set_option maxRecDepth 100000 in
theorem bytecode_size_ne_zero : feERC20Bytecode.size ≠ 0 := by
  rw [feERC20Bytecode, ByteArray.size_append]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _))

theorem P1.bytecode_size_ne_zero : feERC20P1Bytecode.size ≠ 0 := by
  decide +kernel

theorem token_admissible {code : ByteArray} (hsize : code.size ≠ 0) (S : List UInt256) :
    Admissible (TokenAt code S) (· = code) where
  balance _ _ h _ := h
  code acc h := by
    rw [h.1]
    exact hsize
  trusted _ h := h.1

theorem model_keeps (code : ByteArray) (a : AccountAddress) {S : List UInt256}
    (hS : CollisionFree S) :
    ModelKeeps a (TokenAt code S) (· = code) (fun _ _ _ => True) (Admits S)
      (fun _ _ _ _ _ _ => True) Exported.contract := by
  intro I _ _ σ _ _ A feed out w howner _ _ hadm _ _ _ _ _ _ _ hH hrun acc acc' hacc hacc' hcode
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
    holders, leaves the runtime `code` with the holders' balances adding up to the supply. -/
theorem deploy_model (code : ByteArray) {S : List UInt256} (hS : CollisionFree S) (v : UInt256)
    (c s : AccountAddress) (hdeployer : UInt256.ofNat s.val ∈ S) (I : Env) (σ : AccountMap)
    (A : Substate) (feed : List Supply) (out : ByteArray) (w : World) (hc : I.codeOwner = c)
    (hs : I.source = s) (hempty : (σ.getD c default).storage = default)
    (hrun : Succeeds ((Exported.contract.init (ctorTail v) >>= fun tail =>
      pure (code ++ tail)).exec I (World.init σ A feed)) out w) :
    TokenAt code S {w.accounts.getD c default with code := out} := by
  have hmem : (World.init σ A feed).memory.size + 1024 < UInt256.size := by
    simp [World.init, UInt256.size]
  have hzero : ∀ h ∈ S, balance I.codeOwner (World.init σ A feed).accounts h = ⟨0⟩ := by
    intro h _
    rw [balance, storageAt_eq_getD, hc]
    simp only [World.init, hempty]
    rfl
  have hcons := Exported.init_keeps hmem hS (hs ▸ hdeployer) hzero hrun
  rw [hc, conserved_iff_getD] at hcons
  refine ⟨?_, hcons⟩
  obtain ⟨w'', hrun', -⟩ := (Exported.init_endsAs v code I _ hmem).succeeds hrun
  rcases hrun' with hrun' | hrun' <;> simp only [M.exec_bind] at hrun' <;> split at hrun' <;>
    simp at hrun' <;> rename_i hinit
  · exact hrun'.1.symm
  · subst hrun'
    exact absurd hinit (init_noStop _ I _ _ _)

/-! ## Any certified bytecode -/

section Certified

variable {runtime creation : ByteArray}

/-- `every_call_conserves` for a certified runtime. -/
theorem every_call_keeps (hR : RefinesOn .P0 runtime Exported.contract CalldataFits)
    (hsize : runtime.size ≠ 0) (a : AccountAddress) {S : List UInt256} (hS : CollisionFree S)
    (e : Fin 1025) :
    ThetaGood a (TokenAt runtime S) (· = runtime) (fun _ _ _ => True) (Admits S)
        (fun _ _ _ _ _ _ => True) e
      ∧ LambdaGood a (TokenAt runtime S) (Admits S) (fun _ _ _ _ _ _ => True) e :=
  refinesOn_keeps hR (token_admissible hsize S) (fun _ _ _ _ _ => trivial)
    (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩)
    (fun _ _ _ h => h.1) (model_keeps runtime a hS) e

/-- `deploy_conserves_token` for a certified creation bytecode. -/
theorem deploy_keeps_token (hD : RefinesDeploy .P0 creation runtime Exported.contract
      (fun args => ∃ v : UInt256, args = ctorTail v)) {S : List UInt256} (hS : CollisionFree S)
    {v : UInt256}
    {L : LambdaCall} (hi : L.i = creation ++ v.toByteArray) (hs : ∃ acc, L.σ[L.s]? = some acc)
    (hw : L.w = true) (hdeployer : UInt256.ofNat L.s.val ∈ S) (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (TokenAt runtime S) L.run.2.1 :=
  refinesDeploy_holds hD (args := ctorTail v) ⟨v, rfl⟩
    (by rw [Exported.ctorTail_eq]; exact hi) hs hw
    (fun I σ A feed out w hc hs _ hempty hrun =>
      deploy_model runtime hS v L.addr L.s hdeployer I σ A feed out w hc hs hempty hrun) hz

/-- `every_transaction_conserves` for a certified runtime. -/
theorem every_transaction_keeps (hR : RefinesOn .P0 runtime Exported.contract CalldataFits)
    (hsize : runtime.size ≠ 0) (a : AccountAddress) {S : List UInt256}
    (hS : CollisionFree S) {σ σ' : AccountMap} {H_f : ℕ} {H : BlockHeader}
    {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress} {A : Substate} {z : Bool}
    {gu : UInt256} (hH : Holds a (TokenAt runtime S) σ) (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a (Admits S) (fun _ _ _ _ _ _ => True) σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (TokenAt runtime S) σ' ∧ total σ' ≤ total σ :=
  tx_holds (token_admissible hsize S) (fun _ _ _ _ _ => trivial)
    (frameHyp_of_refinesOn hR
      (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩)
      (fun _ _ _ h => h.1) (model_keeps runtime a hS))
    (fun _ h => h) hH hT hsender hdata hpay hfee hnonce hadmit hΥ

end Certified

/-! ## The pinned bytecode -/

/-- **Every message call and creation conserves the token's supply.**  For the token at `a` and
    holders `S` whose balance slots do not collide: every message call and every creation, at any
    depth, that starts where `a` runs the ERC20 bytecode with the holders' balances adding up to
    the supply, and in whose execution every successful frame at `a` has calldata shorter than
    `2 ^ 64` bytes and is covered by `S`, ends where the same holds. -/
theorem every_call_conserves (a : AccountAddress) {S : List UInt256} (hS : CollisionFree S)
    (e : Fin 1025) :
    ThetaGood a (Token S) (· = feERC20Bytecode) (fun _ _ _ => True) (Admits S)
        (fun _ _ _ _ _ _ => True) e
      ∧ LambdaGood a (Token S) (Admits S) (fun _ _ _ _ _ _ => True) e :=
  every_call_keeps Exported.feERC20RefinesExported bytecode_size_ne_zero a hS e

/-- **Deployment conserves.**  A creation of the ERC20 creation bytecode with argument `v` that
    succeeds, made by a holder in `S` that has an account, with write permission, ends with the
    new address running the ERC20 bytecode and the holders' balances adding up to the supply.  The
    new address starts with empty storage: `Lambda` creates only at an address without nonce,
    code or storage.  It adds the new account before it runs the init code when the creator has
    an account, as every creator the EVM runs does. -/
theorem deploy_conserves_token {S : List UInt256} (hS : CollisionFree S) {v : UInt256}
    {L : LambdaCall} (hi : L.i = feERC20CreationBytecode ++ v.toByteArray)
    (hs : ∃ acc, L.σ[L.s]? = some acc) (hw : L.w = true)
    (hdeployer : UInt256.ofNat L.s.val ∈ S) (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Token S) L.run.2.1 :=
  deploy_keeps_token Exported.feERC20DeployRefinesExported hS hi hs hw hdeployer hz

/-- **Every transaction conserves.**  A valid transaction that starts where the token at `a` runs
    the ERC20 bytecode with the holders' balances adding up to the supply, and the ether balances
    of all accounts add up to less than `2 ^ 256`, whose sender has no code (EIP-3607), whose data
    fits a word, and whose execution admits every successful frame at `a`, ends where the same
    holds, with no more ether in total. -/
theorem every_transaction_conserves (a : AccountAddress) {S : List UInt256}
    (hS : CollisionFree S) {σ σ' : AccountMap} {H_f : ℕ} {H : BlockHeader}
    {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress} {A : Substate} {z : Bool}
    {gu : UInt256} (hH : Holds a (Token S) σ) (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a (Admits S) (fun _ _ _ _ _ _ => True) σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (Token S) σ' ∧ total σ' ≤ total σ :=
  every_transaction_keeps Exported.feERC20RefinesExported bytecode_size_ne_zero a hS hH hT hsender
    hdata hpay hfee hnonce hadmit hΥ

/-! ## The bytecode of `P1/` -/

/-- The token's account at the bytecode of `P1/`. -/
def P1.Token (S : List UInt256) (acc : Account) : Prop :=
  TokenAt feERC20P1Bytecode S acc

/-- `every_call_conserves` for the bytecode of `P1/`. -/
theorem P1.every_call_conserves (a : AccountAddress) {S : List UInt256} (hS : CollisionFree S)
    (e : Fin 1025) :
    ThetaGood a (P1.Token S) (· = feERC20P1Bytecode) (fun _ _ _ => True) (Admits S)
        (fun _ _ _ _ _ _ => True) e
      ∧ LambdaGood a (P1.Token S) (Admits S) (fun _ _ _ _ _ _ => True) e :=
  every_call_keeps Sonatina.feERC20RefinesExportedP1.toP0 P1.bytecode_size_ne_zero a hS e

/-- `deploy_conserves_token` for the bytecode of `P1/`. -/
theorem P1.deploy_conserves_token {S : List UInt256} (hS : CollisionFree S) {v : UInt256}
    {L : LambdaCall} (hi : L.i = feERC20P1CreationBytecode ++ v.toByteArray)
    (hs : ∃ acc, L.σ[L.s]? = some acc) (hw : L.w = true)
    (hdeployer : UInt256.ofNat L.s.val ∈ S) (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (P1.Token S) L.run.2.1 :=
  deploy_keeps_token Sonatina.feERC20DeployRefinesExportedP1.toP0 hS hi hs hw hdeployer hz

/-- `every_transaction_conserves` for the bytecode of `P1/`. -/
theorem P1.every_transaction_conserves (a : AccountAddress) {S : List UInt256}
    (hS : CollisionFree S) {σ σ' : AccountMap} {H_f : ℕ} {H : BlockHeader}
    {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress} {A : Substate} {z : Bool}
    {gu : UInt256} (hH : Holds a (P1.Token S) σ) (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a (Admits S) (fun _ _ _ _ _ _ => True) σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (P1.Token S) σ' ∧ total σ' ≤ total σ :=
  every_transaction_keeps Sonatina.feERC20RefinesExportedP1.toP0 P1.bytecode_size_ne_zero a hS hH
    hT hsender hdata hpay hfee hnonce hadmit hΥ

end FeProofs.ERC20
