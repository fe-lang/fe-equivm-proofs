import FeProofs.WETH9.CtorTrace

/-!
# FeWETH9 constructor body (Stele side)

The Stele constructor is `require(msg.value == 0); name = "Wrapped Ether"; symbol = "WETH";
decimals = 18;`.  Each string assignment goes through `solidityWriteBytesValue?`: it reverts on a
head whose length contradicts its flag (`strHeadBad`, the condition under which Fe's `stored_len`
panics), and otherwise zeroes the old data words (none for a short old value) and stores the new
head.  `decimals = 18` replaces the low byte of slot 2.

`steleStrWrite_accountMap` shows that the Stele write (zero, then store the head) leaves the same
account map as the initcode's (store the head, then zero): the zeroed words `keccak256(slot) + i`
never hit slot 0 or 1.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9.Ctor

set_option maxRecDepth 2000000

/-- The generated Solidity layout of the contract's storage. -/
abbrev ctorLayout : StorageLayout := solidityLayout! [contract.structs] [contract.storage]

theorem ctor_storageBackend : config.storageBackend = solidityStorageBackend ctorLayout := rfl

theorem ctorBody_eq : contract.ctor.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .assign .storage { base := "name", steps := [] } (.bytesLit nameBytes),
     .assign .storage { base := "symbol", steps := [] } (.bytesLit symbolBytes),
     .assign .storage { base := "decimals", steps := [] } (.intLit 18)] := rfl

/-! ## `decimals = 18` -/

/-- Stele's write of `decimals`: the low byte of slot 2. -/
abbrev steleDecimals (evm : EVM.State) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) (UInt256.ofNat 18) 0)

theorem decimalsStmt {L : Store} {evm : EVM.State} (hL : L.get? "decimals" = none)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt config { contract := contract, locals := L } evm
      (.assign .storage { base := "decimals", steps := [] } (.intLit 18))
      (.ok { contract := contract, locals := L } (steleDecimals evm)) :=
  ExecStmt.assign (hperm := Or.inr hperm) (evalLit 18)
    (assignStorageRef_storage_scalar_value (layout := ctorLayout)
      (ty := .elem (.int (.uint ⟨8, by decide⟩))) (loc := packedByteLoc ⟨2⟩ 0) hL
      (strRef_eval "decimals") rfl ctor_storageBackend rfl (Or.inl ⟨_, rfl⟩)
      (storageLocStore_packedByte evm ⟨2⟩ (UInt256.ofNat 18) 0))

/-! ## The constructor body -/

/-- The Stele states after `name = …` and `symbol = …`. -/
abbrev steleName (evm : EVM.State) : EVM.State := steleStrWrite evm ⟨0⟩ nameBytes

abbrev steleSymbol (evm : EVM.State) : EVM.State := steleStrWrite (steleName evm) ⟨1⟩ symbolBytes

theorem ctorBody_nameRevert {evm : EVM.State} (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbad : strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) :
    ExecTransitionBody config contract evm ∅ contract.ctor.body .reverted := by
  rw [ctorBody_eq]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (strStmt_revert ctor_storageBackend (by simp) rfl rfl hbad)

theorem ctorBody_symbolRevert {evm : EVM.State} (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))
    (hbad : strHeadBad (Stele.EVM.storageLoad (steleName evm) evm.executionEnv.codeOwner ⟨1⟩)) :
    ExecTransitionBody config contract evm ∅ contract.ctor.body .reverted := by
  rw [ctorBody_eq]
  rw [← steleStrWrite_executionEnv evm ⟨0⟩ nameBytes] at hbad
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (strStmt_ok ctor_storageBackend (by simp) rfl rfl (by decide) hperm hok) <|
        ExecBlock.consRevert (strStmt_revert ctor_storageBackend (by simp) rfl rfl hbad)

theorem ctorBody_ok {evm : EVM.State} (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true)
    (hok0 : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))
    (hok1 : ¬ strHeadBad (Stele.EVM.storageLoad (steleName evm) evm.executionEnv.codeOwner ⟨1⟩)) :
    ExecTransitionBody config contract evm ∅ contract.ctor.body
      (.returned { contract := contract, locals := ∅ } (steleDecimals (steleSymbol evm)) none) := by
  rw [ctorBody_eq]
  have he1 := steleStrWrite_executionEnv evm ⟨0⟩ nameBytes
  have he2 := steleStrWrite_executionEnv (steleName evm) ⟨1⟩ symbolBytes
  rw [← he1] at hok1
  exact ExecFuncBody.execBlockOK <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (strStmt_ok ctor_storageBackend (by simp) rfl rfl (by decide) hperm hok0) <|
        ExecBlock.consNormal (strStmt_ok ctor_storageBackend (by simp) rfl rfl (by decide) (by rw [he1]; exact hperm)
          hok1) <|
          ExecBlock.consNormal (decimalsStmt (by simp) (by rw [he2, he1]; exact hperm))
            ExecBlock.nil

/-! ## Account maps -/

/-- `keccak256(0)` and `keccak256(1)`: where the data words of `name` and `symbol` start. -/
theorem dataBase0 : solidityBytesDataBaseSlot ⟨0⟩ =
    ⟨0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563⟩ := by
  decide +kernel

theorem dataBase1 : solidityBytesDataBaseSlot ⟨1⟩ =
    ⟨0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6⟩ := by
  decide +kernel

/-- No data word a `name` or `symbol` write zeroes is the head slot itself. -/
theorem dataSlot_ne (slot : UInt256) (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩) (S : UInt256) :
    ∀ i, i < strOldWords S → slot ≠ solidityBytesDataBaseSlot slot + UInt256.ofNat i := by
  intro i hi heq
  have hn := strOldWords_lt S
  have ht := congrArg UInt256.toNat heq
  rw [uadd_toNat, ulit_toNat' i (by change _ < 2 ^ 256; omega)] at ht
  rcases hslot with rfl | rfl
  · rw [dataBase0, show (⟨0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563⟩ :
      UInt256).toNat = 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563 from rfl]
      at ht
    change 0 = _ % 2 ^ 256 at ht
    omega
  · rw [dataBase1, show (⟨0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6⟩ :
      UInt256).toNat = 0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6 from rfl]
      at ht
    change 1 = _ % 2 ^ 256 at ht
    omega

theorem steleDecimals_accountMap {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} :
    (steleDecimals (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I))).accountMap =
      ctorMap σ I := by
  have he1 : (steleName (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv = I :=
    steleStrWrite_executionEnv _ _ _
  have he2 : (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv = I := by
    rw [steleSymbol, steleStrWrite_executionEnv, he1]
  have h1 : (steleName (initState σ σ₀ (Sat256.ofUInt256 g) A I)).accountMap = nameMap σ I := by
    rw [steleName, steleStrWrite_accountMap _ _ _ (dataSlot_ne _ (Or.inl rfl) _)]
    rfl
  have h2 : (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I)).accountMap =
      symbolMap σ I := by
    rw [steleSymbol, steleStrWrite_accountMap _ _ _ (dataSlot_ne _ (Or.inr rfl) _), he1, h1]
  rw [steleDecimals, storageStore_accountMap, he2, storageLoad_eq_solcSlotWord, h2,
    setPackedByte_low _ _ (by decide)]
  rfl

end FeProofs.WETH9.Ctor
