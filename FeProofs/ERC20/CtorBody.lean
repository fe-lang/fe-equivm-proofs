import FeProofs.ERC20.CtorTrace
import FeProofs.ERC20.Storage

/-!
# FeERC20 constructor body (Stele side)

The constructor's argument store and its two storage writes under the generated Solidity layout:
`balanceOf[msg.sender]` at `keccak256(caller ‖ 0)` and `totalSupply` in slot 2.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

/-- The constructor's argument store. -/
abbrev ctorLocals (i : Int) : Store :=
  Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) [.int i])

theorem ctorLocals_initialSupply (i : Int) : (ctorLocals i).get? "initialSupply" = some (.int i) := by
  simp [ctorLocals, contract, Syntax.contractSyntax]

theorem ctorLocals_balanceOf (i : Int) : (ctorLocals i).get? "balanceOf" = none := by
  simp [ctorLocals, contract, Syntax.contractSyntax]

theorem ctorLocals_totalSupply (i : Int) : (ctorLocals i).get? "totalSupply" = none := by
  simp [ctorLocals, contract, Syntax.contractSyntax]

abbrev balanceOfSenderRef : StorageRef := { base := "balanceOf", steps := [.mindex (.env .caller)] }

theorem balanceOfSender_write {L : Store} {evm : EVM.State} (hL : L.get? "balanceOf" = none)
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage balanceOfSenderRef
        (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.address evm.executionEnv.source))) w) :=
  assignStorageRef_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (er := { base := "balanceOf", steps := [.mindex (.address evm.executionEnv.source)] })
    (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (loc := uint256Loc (solcMappingSlot ⟨0⟩ (keyValueToWord (.address evm.executionEnv.source)))) hL
    (by simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, envValue, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax]) rfl rfl
    (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ w)

theorem totalSupply_write {L : Store} {evm : EVM.State} (hL : L.get? "totalSupply" = none)
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage totalSupplyRef
        (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ w) :=
  assignStorageRef_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := uint256Loc ⟨2⟩) hL totalSupplyRef_eval
    (by show storageTypeAt? contract.storage _ = _; decide) rfl rfl (Or.inl ⟨_, rfl⟩)
    (storageLocStore_uint256 evm ⟨2⟩ w)

/-- The constructor's Stele post state: the argument at `balanceOf[msg.sender]` and in slot 2. -/
abbrev ctorPost (evm : EVM.State) (w : UInt256) : EVM.State :=
  Stele.EVM.storageStore
    (Stele.EVM.storageStore evm evm.executionEnv.codeOwner
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address evm.executionEnv.source))) w)
    evm.executionEnv.codeOwner ⟨2⟩ w

theorem feERC20CtorBody_ok (evm : EVM.State) (i : Int) (h0 : 0 ≤ i)
    (hlt : i < Int.ofNat (EVM.twoPow 256))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (ctorLocals i) contract.ctor.body
      (.returned { contract := contract, locals := ctorLocals i } (ctorPost evm (EVM.word i.toNat))
        none) := by
  have hval : ∀ evm' : EVM.State,
      evalExpr? config { contract := contract, locals := ctorLocals i } evm' (.var "initialSupply") =
        .ok (.int (Int.ofNat (EVM.word i.toNat).toNat)) := by
    intro evm'
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((ctorLocals i).get? "initialSupply") = _
    rw [ctorLocals_initialSupply, constructorUInt256Word_toNat i h0 hlt]
    simp [EvalResult.ofOption, Int.toNat_of_nonneg h0]
  have hb := balanceOfSender_write (L := ctorLocals i) (evm := evm) (ctorLocals_balanceOf i)
    (EVM.word i.toNat)
  have ht := totalSupply_write (L := ctorLocals i)
    (evm := Stele.EVM.storageStore evm evm.executionEnv.codeOwner
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address evm.executionEnv.source))) (EVM.word i.toNat))
    (ctorLocals_totalSupply i) (EVM.word i.toNat)
  rw [storageStore_executionEnv] at ht
  have hev : evalExprs? config { contract := contract, locals := ctorLocals i }
      (ctorPost evm (EVM.word i.toNat))
      [.cast (.intLit 0) (.elem .address), .env .caller, .var "initialSupply"] =
      .ok [.address (AccountAddress.ofNat 0), .address (ctorPost evm (EVM.word i.toNat)).executionEnv.source,
        .int i] := by
    simp only [evalExprs?, evalExpr?, ctorLocals_initialSupply, envValue, EvalResult.bind,
      EvalResult.ofOption, bind, pure]
    simp [castValue?]
  have hperm1 : (Stele.EVM.storageStore evm evm.executionEnv.codeOwner
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address evm.executionEnv.source)))
      (EVM.word i.toNat)).executionEnv.perm = true := by
    rw [storageStore_executionEnv]; exact hperm
  have hperm2 : (ctorPost evm (EVM.word i.toNat)).executionEnv.perm = true := by
    simp only [ctorPost, storageStore_executionEnv]; exact hperm
  exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue
    (evalCallvalueEq_true hwv)) (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm)
      (hval evm) hb) (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm1) (hval _) ht)
      (ExecBlock.consNormal (ExecStmt.emit hperm2 hev) ExecBlock.nil))))

end FeProofs.ERC20
