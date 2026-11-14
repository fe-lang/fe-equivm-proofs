import FeProofs.WETH9.ModelCorrect
import FeProofs.WETH9.Solvency
import Fe.EVM.RefineInvariant

/-!
# FeWETH9: solvency from deployment on

The base case of the invariant `Weth feWETH9Bytecode`: a successful creation of the WETH9
creation bytecode, with no argument bytes, leaves at the new address an account that runs the
runtime bytecode and is solvent (`deploy_solvent`), if no key's balance slot is the slot of
`name`, `symbol` or `decimals`.  From the deployment certificate `feWETH9DeployRefinesModel` and
the constructor's solvency (`init_solvent_of_empty`), through `refinesDeploy_holds`.
-/

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

namespace FeProofs.WETH9

open Model

theorem noStop_init : init.NoStop := by
  unfold init storeString; dsimp only; weth_no_stop

/-- **A deployment leaves a solvent WETH9.**  A creation of the creation bytecode that succeeds
    ends with the account at the address it created running the runtime bytecode and solvent, if
    no key's balance slot is slot 0, 1 or 2. -/
theorem deploy_solvent {L : LambdaCall} (hi : L.i = feWETH9CreationBytecode ++ ByteArray.empty)
    (hw : L.w = true)
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hz : L.run.2.2.2.2.1 = true) :
    L.run.1 = L.addr ∧ Holds L.addr (Weth feWETH9Bytecode) L.run.2.1 := by
  refine refinesDeploy_holds feWETH9DeployRefinesModel (args := ByteArray.empty) rfl hi hw
    (fun I σ A feed out w hown _ hempty hrun => ?_) hz
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

end FeProofs.WETH9
