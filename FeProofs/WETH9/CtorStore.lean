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

/-! ## String assignments -/

/-- Stele's write of a short string at `slot`: zero the old data words, then store the head. -/
abbrev steleStrWrite (evm : EVM.State) (slot : UInt256) (bytes : ByteArray) : EVM.State :=
  Stele.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evm slot 0
      (strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))
    evm.executionEnv.codeOwner slot (solidityShortBytesWord bytes)

theorem steleStrWrite_executionEnv (evm : EVM.State) (slot : UInt256) (bytes : ByteArray) :
    (steleStrWrite evm slot bytes).executionEnv = evm.executionEnv := by
  rw [steleStrWrite, storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv]

theorem strWrite_bad {evm : EVM.State} {er : EvaledStorageRef} {slot : UInt256} {bytes : ByteArray}
    (hlay : ctorLayout er = some (.anchor slot))
    (hbad : strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    config.storageBackend.write er .string (.bytes bytes) evm = .revert := by
  unfold strHeadBad strHeadLen at hbad
  rcases land_one_cases (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) with hf | hf
  · rw [if_pos hf] at hbad
    exact writeSolidityStringMalformedShort ctor_storageBackend hlay rfl hf hbad
  · have hne : UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩ ≠
        ⟨0⟩ := by
      rw [hf]; decide
    rw [if_neg hne] at hbad
    exact writeSolidityStringMalformedLong ctor_storageBackend hlay rfl hne hbad

theorem strWrite_ok {evm : EVM.State} {er : EvaledStorageRef} {slot : UInt256} {bytes : ByteArray}
    (hlay : ctorLayout er = some (.anchor slot)) (hsize : bytes.size < 32)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    config.storageBackend.write er .string (.bytes bytes) evm =
      .ok (steleStrWrite evm slot bytes) := by
  unfold strHeadBad strHeadLen at hok
  rcases land_one_cases (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) with hf | hf
  · have hw : strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) = 0 := by
      rw [strOldWords, if_pos hf]
    rw [if_pos hf] at hok
    rw [writeSolidityStringShortPacked ctor_storageBackend hlay hsize rfl
      (checkBytesPacked_of_storageLoad_land_one_zero rfl hf) hf rfl hok, steleStrWrite, hw]
    rfl
  · have hne : UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩ ≠
        ⟨0⟩ := by
      rw [hf]; decide
    have hw : strOldWords (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) =
        ((UInt256.div (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨2⟩).toNat + 31) /
          32 := by
      rw [strOldWords, if_neg hne, strHeadLen, if_neg hne]
    rw [if_neg hne] at hok
    rw [writeSolidityStringShortFromLongPrepared ctor_storageBackend hlay hsize rfl hne rfl hok,
      clearSolidityBytesDataWordsFrom_executionEnv, steleStrWrite, hw]

theorem strRef_eval {L : Store} {evm : EVM.State} (base : Ident) :
    evalStorageRef config { contract := contract, locals := L } evm { base := base, steps := [] } =
      .ok { base := base, steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalBytesLit {L : Store} {evm : EVM.State} (bytes : ByteArray) :
    evalExpr? config { contract := contract, locals := L } evm (.bytesLit bytes) =
      .ok (.bytes bytes) := by
  rw [evalExpr?]; rfl

/-- `base = bytes` for a `string` field at `slot`, over a malformed head. -/
theorem strStmt_revert {L : Store} {evm : EVM.State} {base : Ident} {slot : UInt256}
    {bytes : ByteArray} (hL : L.get? base = none)
    (hty : storageTypeAt? contract.storage { base := base, steps := [] } = some .string)
    (hlay : ctorLayout { base := base, steps := [] } = some (.anchor slot))
    (hbad : strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.assign .storage { base := base, steps := [] } (.bytesLit bytes)) .reverted :=
  ExecStmt.assignStoreRevert (evalBytesLit bytes) (by
    simp only [assignStorageRef?, resolveStorageRef?_ok hL (strRef_eval base) hty,
      strWrite_bad hlay hbad, bind, EvalResult.bind])

/-- `base = bytes` for a `string` field at `slot`, over a well-formed head. -/
theorem strStmt_ok {L : Store} {evm : EVM.State} {base : Ident} {slot : UInt256}
    {bytes : ByteArray} (hL : L.get? base = none)
    (hty : storageTypeAt? contract.storage { base := base, steps := [] } = some .string)
    (hlay : ctorLayout { base := base, steps := [] } = some (.anchor slot))
    (hsize : bytes.size < 32) (hperm : evm.executionEnv.perm = true)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.assign .storage { base := base, steps := [] } (.bytesLit bytes))
      (.ok { contract := contract, locals := L } (steleStrWrite evm slot bytes)) :=
  ExecStmt.assign (hperm := Or.inr hperm) (evalBytesLit bytes) (by
    simp only [assignStorageRef?, resolveStorageRef?_ok hL (strRef_eval base) hty,
      strWrite_ok hlay hsize hok, bind, EvalResult.bind, pure])

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

theorem setPackedByte_decimals (w : UInt256) :
    setPackedByte w (UInt256.ofNat 18) 0 = decimalsWord w := by
  have hw : w.toNat < 2 ^ 256 := w.val.isLt
  apply u256_inj
  rw [setPackedByte_toNat, u256_lor_toNat, uland_toNat,
    show (UInt256.lnot (UInt256.ofNat 255)).toNat = 2 ^ 256 - 2 ^ 8 by decide,
    show (UInt256.ofNat 18).toNat = 18 from rfl, Nat.and_comm]
  change _ = Nat.lor 18 (Nat.land w.toNat (2 ^ 256 - 2 ^ 8)) % UInt256.size
  rw [natLandClearLow8 w.toNat hw, nat_lor_shift_add 18 (w.toNat / 2 ^ 8) 8 (by norm_num)]
  have hlt : 18 + w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size := by change _ < 2 ^ 256; omega
  rw [show ((0 : Fin 32) : ℕ) = 0 from rfl, Nat.mod_eq_of_lt hlt]
  omega

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
      ExecBlock.consRevert (strStmt_revert (by simp) rfl rfl hbad)

theorem ctorBody_symbolRevert {evm : EVM.State} (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true)
    (hok : ¬ strHeadBad (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))
    (hbad : strHeadBad (Stele.EVM.storageLoad (steleName evm) evm.executionEnv.codeOwner ⟨1⟩)) :
    ExecTransitionBody config contract evm ∅ contract.ctor.body .reverted := by
  rw [ctorBody_eq]
  rw [← steleStrWrite_executionEnv evm ⟨0⟩ nameBytes] at hbad
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (strStmt_ok (by simp) rfl rfl (by decide) hperm hok) <|
        ExecBlock.consRevert (strStmt_revert (by simp) rfl rfl hbad)

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
      ExecBlock.consNormal (strStmt_ok (by simp) rfl rfl (by decide) hperm hok0) <|
        ExecBlock.consNormal (strStmt_ok (by simp) rfl rfl (by decide) (by rw [he1]; exact hperm)
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

/-- Stele's string write leaves the account map the initcode leaves: zeroing the old data words
    commutes with storing the head. -/
theorem steleStrWrite_accountMap (evm : EVM.State) (slot : UInt256)
    (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩) (bytes : ByteArray) :
    (steleStrWrite evm slot bytes).accountMap =
      strWriteMap evm.executionEnv evm.accountMap slot bytes := by
  rw [steleStrWrite, storageStore_accountMap, clearSolidityBytesDataWordsFrom_accountMap,
    strWriteMap, clearDataWordsForwardFrom_sstore_comm _ _ _ _ _ _
      (dataSlot_ne slot hslot (solcSlotWord evm.accountMap evm.executionEnv slot))]
  rfl

theorem steleDecimals_accountMap {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} :
    (steleDecimals (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I))).accountMap =
      ctorMap σ I := by
  have he1 : (steleName (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv = I :=
    steleStrWrite_executionEnv _ _ _
  have he2 : (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv = I := by
    rw [steleSymbol, steleStrWrite_executionEnv, he1]
  have h1 : (steleName (initState σ σ₀ (Sat256.ofUInt256 g) A I)).accountMap = nameMap σ I := by
    rw [steleName, steleStrWrite_accountMap _ _ (Or.inl rfl)]
    rfl
  have h2 : (steleSymbol (initState σ σ₀ (Sat256.ofUInt256 g) A I)).accountMap =
      symbolMap σ I := by
    rw [steleSymbol, steleStrWrite_accountMap _ _ (Or.inr rfl), he1, h1]
  rw [steleDecimals, storageStore_accountMap, he2, storageLoad_eq_solcSlotWord, h2,
    setPackedByte_decimals]
  rfl

end FeProofs.WETH9.Ctor
