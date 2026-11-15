import FeProofs.WETH9.RuntimeCorrect
import FeProofs.WETH9.SonatinaCorrect
import FeProofs.WETH9.Solvency
import Fe.EVM.RefineInvariant

/-!
# FeWETH9: solvency through every message call

WETH9 at `a` stays solvent: the ether it holds covers the tokens at every set of distinct balance
slots (`Solvent`), and its account keeps the WETH9 bytecode (`Weth feWETH9Bytecode`).  The
statements name only the model the compiler exports (`Exported.contract`), through its
certificates `feWETH9RefinesExported` and `feWETH9DeployRefinesExported`.  The proof goes
through the hand-written model: the exported runtime ends as it does, with the same accounts and
the same recorded calls (`Exported.runtime_endsAs`), and its solvency is
`FeProofs.WETH9.Solvency`.

- `feWETH9KeepsSolvent`: every message call and creation, at every depth, whoever makes it,
  re-entry included, keeps it and adds no ether, as `ThetaGood` and `LambdaGood` state.
- `feWETH9TxKeepsSolvent`: every transaction keeps it, and the total ether does not grow.
- `feWETH9DeploySolvent`: a successful deployment of the creation bytecode establishes it at the
  new address.

## What the theorems assume

- **Admission** (`Admission`): in the execution, every successful frame at `a`
  - has calldata shorter than `2 ^ 64` bytes (`CalldataFits`), which the certificate of the
    exported model asks, since Fe's std reads a calldata length as a `u64`.  No transaction comes
    near it: gas limits bound calldata far below.
  - writes, when it runs `approve` or a `transferFrom` that spends another's tokens, an
    allowance slot that is no key's balance slot (`Admits`).  Keys are hashed into slots, so a
    collision is a hash collision; the condition is stated per call, on the keys in use, as
    ERC20's `Covers` is.
- **Whose calls admission covers**: admission of a frame at `a` speaks of the calls the exported
  model makes under every feed (`Exported.contract.callsAt`), not of the bytecode's own calls.  A
  frame may use `Deeper` only of admitted calls, and a callee's admission depends on its gas and
  substate, which the model takes from its feed; tying them to the bytecode's calls would need
  EquiVM's `RD` traces to record the path of the run, and they record only that the cursor state
  runs to the same result.  The model's one call is `withdraw`'s, to the caller with no data.
- **Entry** (`Enters`): a frame at `a` is entered from another account, moving the value it
  reports.  The pure layer proves this of every entry from another account; WETH9 never calls
  itself (it calls only its caller, which is never `a`).  A call from `a` to itself with value
  would credit tokens no ether paid for.
- **The sum of all balances** is below `2 ^ 256` where the call or transaction starts, so that no
  balance increase wraps; the transactions are valid as EVMLean's conformance runner checks
  (the sender has no code and can pay the gas limit, the blob fee and the value; the priority fee
  is at most the price; the sender's nonce is below `2 ^ 64 - 1`; the data fits a word).
- **Deployment**: no key's balance slot is slot 0, 1 or 2, where the constructor writes `name`,
  `symbol` and `decimals`.  The deployment has no argument bytes and write permission, and its
  creator has an account, as every creator does in a real execution, so that `Lambda` adds the new
  account before it runs the init code; the new account starts with empty storage, as `Lambda`
  guarantees.
-/

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

namespace FeProofs.WETH9

open Model

theorem noStop_init : init.NoStop := by
  unfold init storeString; dsimp only; weth_no_stop

/-- The hand-written constructor, run at `c` with write permission from empty storage, leaves
    there an account that runs the code it returns, the runtime bytecode, and is solvent, if no
    key's balance slot is slot 0, 1 or 2. -/
theorem deploy_model {c : AccountAddress} {I : Env} {σ : AccountMap} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w : World} (hown : I.codeOwner = c)
    (hempty : (σ.getD c default).storage = default)
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hrun : Succeeds ((Model.contract.init ByteArray.empty >>= fun tail =>
      pure (feWETH9Bytecode ++ tail)).exec I (World.init σ A feed)) out w) :
    Weth feWETH9Bytecode {w.accounts.getD c default with code := out} := by
  have hns : (Model.contract.init ByteArray.empty >>= fun tail =>
      pure (feWETH9Bytecode ++ tail)).NoStop :=
    M.NoStop.bind (M.NoStop.bind noStop_init fun _ => M.NoStop.pure _) fun _ => M.NoStop.pure _
  have hok := Succeeds.of_noStop hns hrun
  obtain ⟨tail, w₁, h₁, k₁⟩ := exec_bind_ok hok
  simp only [M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at k₁
  obtain ⟨rfl, rfl⟩ := k₁
  obtain ⟨⟨⟩, w₂, h₂, k₂⟩ := exec_bind_ok h₁
  simp only [M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at k₂
  obtain ⟨rfl, rfl⟩ := k₂
  have hs := init_solvent_of_empty h₂ hslots (by rw [hown]; exact hempty)
  rw [hown] at hs
  exact ⟨by simp, hs⟩

/-- **A deployment leaves a solvent WETH9.**  A creation of the creation bytecode, with no
    argument bytes, by an account that exists, that succeeds ends with the account at the address
    it created running the runtime bytecode and solvent, if no key's balance slot is slot 0, 1 or
    2.  Through the certificate of the exported deployment entry, which speaks of frames whose
    account exists: `Lambda` adds the new account before it runs the init code when the creator
    has an account, as every creator the EVM runs does. -/
theorem deploy_solvent (hD : RefinesDeploy .P0 feWETH9CreationBytecode feWETH9Bytecode
      Exported.contract (· = ByteArray.empty)) {L : LambdaCall}
    (hi : L.i = feWETH9CreationBytecode ++ ByteArray.empty) (hs : ∃ acc, L.σ[L.s]? = some acc)
    (hw : L.w = true)
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Weth feWETH9Bytecode) L.run.2.1 := by
  refine refinesDeploy_holds hD (args := ByteArray.empty) rfl
    hi hs hw (fun I σ A feed out w hown _ hperm hempty hrun => ?_) hz
  obtain ⟨w', hrun', hacc⟩ := (Exported.init_endsAs I (World.init σ A feed) ByteArray.empty
    feWETH9Bytecode rfl hperm).succeeds hrun
  rw [← hacc]
  exact deploy_model hown hempty hslots hrun'

theorem feWETH9DeploySolvent {L : LambdaCall}
    (hi : L.i = feWETH9CreationBytecode ++ ByteArray.empty) (hs : ∃ acc, L.σ[L.s]? = some acc)
    (hw : L.w = true)
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Weth feWETH9Bytecode) L.run.2.1 :=
  deploy_solvent Exported.feWETH9DeployRefinesExported hi hs hw hslots hz

/-! ## The invariant through every call -/

/-- How a frame at WETH9 may be entered: from another account, moving the value it reports. -/
def Enters (a : AccountAddress) (_ : AccountMap) (I : ExecutionEnv) (v : UInt256) : Prop :=
  I.source ≠ a ∧ v = I.weiValue

theorem fromOthers (a : AccountAddress) : FromOthers a (Enters a) :=
  fun _ _ _ hne hv => ⟨hne, hv⟩

/-- A frame at WETH9 is admitted when its calldata is shorter than `2 ^ 64` bytes, as the
    certificate of the exported model asks, and the allowance slot it writes is no key's balance
    slot. -/
def Admission (_ : AccountMap) (I : ExecutionEnv) : Prop := CalldataFits I ∧ Admits I

set_option maxRecDepth 100000 in
theorem bytecode_size_ne_zero : feWETH9Bytecode.size ≠ 0 := by
  rw [feWETH9Bytecode, ByteArray.size_append]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _))

/-- Solvency survives ether arriving, when the balance does not wrap. -/
theorem weth_admissible : Admissible (Weth feWETH9Bytecode) (· = feWETH9Bytecode) where
  balance acc v h hlt := by
    refine ⟨h.1, fun S hnd => (h.2 S hnd).trans ?_⟩
    show acc.balance.toNat ≤ (acc.balance + v).toNat
    rw [UInt256.toNat_add_of_lt hlt]
    omega
  code acc h := by rw [h.1]; exact bytecode_size_ne_zero
  trusted _ h := h.1

/-- **The exported model keeps the invariant.**  Its runtime ends as the hand-written one does,
    with the same accounts and the same recorded calls (`Exported.runtime_endsAs`); the one call
    recorded is `withdraw`'s, to the caller, which is not WETH9.  `made_theta_good` gives that it
    keeps `Weth`, from what `recorded_call` shows of it, and `runtime_keeps` the rest. -/
theorem model_keeps (a : AccountAddress) :
    ModelKeeps a (Weth feWETH9Bytecode) (· = feWETH9Bytecode) (Enters a) Admission
      Exported.contract.callsAt Exported.contract := by
  intro I σpre v σ σ₀ g A feed out w howner _ _ hadm hdeep hcalls hσ hen hv hTpre hHpre _ hrun
    acc acc' hacc hacc' hcode
  obtain ⟨hne, rfl⟩ := hen
  subst howner
  obtain ⟨wh, hrunh, hacch, hcallsh⟩ :=
    (Exported.runtime_endsAs I (World.init σ A feed) rfl hadm.1).succeeds_calls hrun
  have hok := Succeeds.of_noStop noStop_runtime hrunh
  rw [← hacch] at hacc'
  refine runtime_keeps hσ hne hv hTpre hHpre hadm.2 hrunh (fun T hT => ?_) acc acc' hacc hacc'
    hcode
  obtain ⟨he, hd, hr, -, hval, htot, hH₁, hH₂, -⟩ := recorded_call hσ hne hv hTpre hHpre hok hT
  obtain ⟨⟨acc'', h'', hP⟩, -, -⟩ := made_theta_good hdeep hcalls hrun (hcallsh ▸ hT) he hd
    (fun h => absurd h hr) (fun h => absurd h hr) hval htot hH₁ hH₂
  intro x hx
  rw [h''] at hx
  cases hx
  exact hP.2

/-- **Every message call and creation keeps WETH9 solvent.**  For WETH9 at `a`: every message
    call and every creation, at any depth, that starts where `a` runs the WETH9 bytecode and is
    solvent, and in whose execution every successful frame at `a` is admitted (`Admission`, for
    the calls the exported model makes under every feed), ends where the same holds, with no more
    ether in total, if it is entered with value its payer has and the balances add up to less
    than `2 ^ 256`. -/
theorem keeps_solvent (hR : RefinesOn .P0 feWETH9Bytecode Exported.contract CalldataFits)
    (a : AccountAddress) (e : Fin 1025) :
    ThetaGood a (Weth feWETH9Bytecode) (· = feWETH9Bytecode) (Enters a) Admission
        Exported.contract.callsAt e
      ∧ LambdaGood a (Weth feWETH9Bytecode) Admission Exported.contract.callsAt e :=
  refinesOn_keeps_calls hR weth_admissible (fromOthers a)
    (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩) (fun _ _ _ h => h.1)
    (model_keeps a) e

/-- **Every transaction keeps WETH9 solvent.**  A valid transaction that starts where WETH9 at
    `a` runs its bytecode and is solvent, and the ether balances of all accounts add up to less
    than `2 ^ 256`, whose sender has no code (EIP-3607), whose data fits a word, and whose
    execution admits every successful frame at `a`, ends where the same holds, with no more
    ether in total. -/
theorem tx_keeps_solvent (hR : RefinesOn .P0 feWETH9Bytecode Exported.contract CalldataFits)
    (a : AccountAddress) {σ σ' : AccountMap} {H_f : ℕ}
    {H : BlockHeader} {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress}
    {A : Substate} {z : Bool} {gu : UInt256} (hH : Holds a (Weth feWETH9Bytecode) σ)
    (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a Admission Exported.contract.callsAt σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (Weth feWETH9Bytecode) σ' ∧ total σ' ≤ total σ :=
  tx_holds weth_admissible (fromOthers a)
    (frameHyp_of_refinesOn_calls hR
      (fun _ h => ⟨ByteArray.empty, by rw [h, ByteArray.append_empty], rfl⟩) (fun _ _ _ h => h.1)
      (model_keeps a))
    (fun _ h => h) hH hT hsender hdata hpay hfee hnonce hadmit hΥ

/-- **Every message call and creation keeps WETH9 solvent** (`feWETH9KeepsSolvent`). -/
theorem feWETH9KeepsSolvent (a : AccountAddress) (e : Fin 1025) :
    ThetaGood a (Weth feWETH9Bytecode) (· = feWETH9Bytecode) (Enters a) Admission
        Exported.contract.callsAt e
      ∧ LambdaGood a (Weth feWETH9Bytecode) Admission Exported.contract.callsAt e :=
  keeps_solvent Exported.feWETH9RefinesExported a e

/-- **Every transaction keeps WETH9 solvent** (`feWETH9TxKeepsSolvent`). -/
theorem feWETH9TxKeepsSolvent (a : AccountAddress) {σ σ' : AccountMap} {H_f : ℕ}
    {H : BlockHeader} {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress}
    {A : Substate} {z : Bool} {gu : UInt256} (hH : Holds a (Weth feWETH9Bytecode) σ)
    (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a Admission Exported.contract.callsAt σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (Weth feWETH9Bytecode) σ' ∧ total σ' ≤ total σ :=
  tx_keeps_solvent Exported.feWETH9RefinesExported a hH hT hsender hdata hpay hfee hnonce hadmit hΥ

/-! ## Through the `P1` certificates

The same three theorems, resting on the certificates through the Sonatina checker
(`SonatinaCorrect.lean`), which use no `native_decide`, weakened to `P0` (`RefinesOn.toP0`,
`RefinesDeploy.toP0`). -/

/-- `feWETH9KeepsSolvent` through the `P1` certificate. -/
theorem feWETH9KeepsSolventP1 (a : AccountAddress) (e : Fin 1025) :
    ThetaGood a (Weth feWETH9Bytecode) (· = feWETH9Bytecode) (Enters a) Admission
        Exported.contract.callsAt e
      ∧ LambdaGood a (Weth feWETH9Bytecode) Admission Exported.contract.callsAt e :=
  keeps_solvent Sonatina.feWETH9RefinesExportedP1.toP0 a e

/-- `feWETH9TxKeepsSolvent` through the `P1` certificate. -/
theorem feWETH9TxKeepsSolventP1 (a : AccountAddress) {σ σ' : AccountMap} {H_f : ℕ}
    {H : BlockHeader} {blocks : ProcessedBlocks} {T : Transaction} {S_T : AccountAddress}
    {A : Substate} {z : Bool} {gu : UInt256} (hH : Holds a (Weth feWETH9Bytecode) σ)
    (hT : total σ < UInt256.size)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hpay : T.base.gasLimit.toNat * (txPrice T H_f).toNat + calcBlobFee H T + T.base.value.toNat
      ≤ (balOf σ S_T).toNat)
    (hfee : (txFee T H_f).toNat ≤ (txPrice T H_f).toNat)
    (hnonce : (σ.getD S_T default).nonce.toNat < 2 ^ 64 - 1)
    (hadmit : TxAdmitted a Admission Exported.contract.callsAt σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a (Weth feWETH9Bytecode) σ' ∧ total σ' ≤ total σ :=
  tx_keeps_solvent Sonatina.feWETH9RefinesExportedP1.toP0 a hH hT hsender hdata hpay hfee hnonce
    hadmit hΥ

/-- `feWETH9DeploySolvent` through the `P1` certificate. -/
theorem feWETH9DeploySolventP1 {L : LambdaCall}
    (hi : L.i = feWETH9CreationBytecode ++ ByteArray.empty) (hs : ∃ acc, L.σ[L.s]? = some acc)
    (hw : L.w = true)
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Weth feWETH9Bytecode) L.run.2.1 :=
  deploy_solvent Sonatina.feWETH9DeployRefinesExportedP1.toP0 hi hs hw hslots hz

end FeProofs.WETH9
