import FeProofs.Deposit.Le64
import FeProofs.Deposit.Sha256
import FeProofs.Deposit.CreationBlocks_001

/-!
# FeDeposit constructor loop

The initcode fills `zero_hashes[1..31]`: for `h < 31` it loads `zero_hashes[h]` (slot `33 + h`),
stores it at memory words 0 and 1, hashes `[0, 64)` with precompile 2 (reverting unless the call
succeeds and returns a word), and stores the first returned word in slot `34 + h`.  The spec's
`for` loop makes the same storage reads, the same opaque `sha256_pair` calls and the same writes;
`ctorLoop` simulates the two loops together by induction on the remaining iterations, linking the
EVM accounts to the Stele state with `SourceState`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- The initcode as the creation summaries see it (no constructor arguments). -/
abbrev ctorCode : ByteArray := feDepositCreationBytecode ++ ByteArray.empty

/-! ## The hashed buffer -/

theorem write32_size_ge (src base : ByteArray) (dest : ℕ) (hsrc : 32 ≤ src.size)
    (hlo : dest ≤ base.size) : dest + 32 ≤ (src.write 0 base dest 32).size := by
  rw [write32_eq src base dest hsrc hlo, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract]
  omega

/-- Storing `w` at memory words 0 and 1 makes `[0, 64)` the pair payload `w ‖ w`. -/
theorem pairMem_read (w : UInt256) (mem : ByteArray) :
    (w.toByteArray.write 0 (w.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 64).toNat = pairPayload w w := by
  have hw : 32 ≤ w.toByteArray.size := by rw [toByteArray_size]
  show (w.toByteArray.write 0 (w.toByteArray.write 0 mem 0 32) 32 32).readWithPadding 0 64 = _
  have hAsz := write32_size_ge w.toByteArray mem 0 hw (Nat.zero_le _)
  have hA0 : (w.toByteArray.write 0 mem 0 32).extract 0 32 = w.toByteArray := by
    rw [← readWithPadding_eq_extract _ 0 hAsz, write32_read_back _ _ 0 hw (Nat.zero_le _),
      extract_word_all]
  generalize w.toByteArray.write 0 mem 0 32 = A at hAsz hA0
  have hB := write32_size_ge w.toByteArray A 32 hw (by omega)
  have hXY : (A.extract 0 32 ++ w.toByteArray.extract 0 32).size = 64 := by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  rw [readWithPadding_eq_extract' _ 0 64 (by decide) (by decide) (by omega),
    write32_eq _ _ 32 hw (by omega), extract_append_left _ _ 0 64 (by rw [hXY]),
    byteArray_extract_of_size _ 64 hXY, hA0, extract_word_all, pairPayload_eq]

theorem pairMem_size (w : UInt256) (mem : ByteArray) :
    64 ≤ (w.toByteArray.write 0 (w.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32).size := by
  have hw : 32 ≤ w.toByteArray.size := by rw [toByteArray_size]
  have hAsz := write32_size_ge w.toByteArray mem 0 hw (Nat.zero_le _)
  exact write32_size_ge w.toByteArray _ 32 hw (by simpa using hAsz)

/-! ## `zero_hashes[i]`: slot `33 + i`

Adapted from the `get_deposit_root` read facts, with the write counterpart. -/

/-- The generated Solidity layout of the contract's storage. -/
def ctorLayout : StorageLayout := storageBackend.locate?

theorem ctor_storageBackend : config.storageBackend = solidityStorageBackend ctorLayout := rfl

theorem ctorKeyWord {i : Nat} (hi : i < 32) :
    keyValueToWord (.int (Int.ofNat i)) = UInt256.ofNat i := by
  simp only [keyValueToWord, EVM.wordOfInt, EVM.word]
  rw [if_neg (by simp)]
  rfl

theorem zeroHashRef_eval {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i))) :
    evalStorageRef config { contract := contract, locals := L } evm
        { base := "zero_hashes", steps := [.aindex idx] } =
      .ok { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } := by
  have hty : storageTypeAt? contract.storage { base := "zero_hashes", steps := [] } =
      some (.array (.elem (.int (.uint ⟨256, by decide⟩))) 32) := rfl
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
    arrayIndexInBounds?, hty, bind, EvalResult.bind, pure, EvalResult.ofOption, hi]

theorem zeroHash_type (i : Nat) :
    storageTypeAt? contract.storage { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

theorem zeroHash_loc {i : Nat} (hi : i < 32) :
    ctorLayout { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (uint256Loc (⟨33⟩ + UInt256.ofNat i))) := by
  show some (StorageAddr.leaf _) = _
  simp only [ctorKeyWord hi, ulit_toNat' i (lt_of_lt_of_le hi (by decide)), Nat.div_one,
    Nat.mod_one, Nat.zero_mul]
  rfl

theorem zeroHash_read {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i)))
    (hbase : L.get? "zero_hashes" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "zero_hashes", steps := [.aindex idx] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (⟨33⟩ + UInt256.ofNat i)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int (.uint ⟨256, by decide⟩)) hbase (zeroHashRef_eval hi hidx)
    (zeroHash_type i) ctor_storageBackend (zeroHash_loc hi), storageLocLoad_uint256]

theorem zeroHash_write {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i)))
    (hbase : L.get? "zero_hashes" = none) (v : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage
        { base := "zero_hashes", steps := [.aindex idx] } (.int (Int.ofNat v.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (⟨33⟩ + UInt256.ofNat i) v) :=
  assignStorageRef_storage_scalar_value hbase (zeroHashRef_eval hi hidx) (zeroHash_type i)
    ctor_storageBackend (zeroHash_loc hi) (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ v)

/-! ## Word facts for the loop -/

theorem callOutput_load32 (mem out : ByteArray) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hin : 32 ≤ mem.size) :
    memLoad (⟨0⟩ : UInt256) (callOutputMem mem out (⟨0⟩ : UInt256) (UInt256.ofNat 32)) =
      calldataWord out 0 :=
  callOutput_load mem out ⟨0⟩ hb hs (by simpa using hin)

theorem lt31_word {h : ℕ} (hlt : h < 31) :
    UInt256.isZero (UInt256.lt (UInt256.ofNat h) (UInt256.ofNat 31)) = UInt256.ofNat 0 := by
  have hw : UInt256.ofNat h < UInt256.ofNat 31 :=
    (ofNat_lt_ofNat (lt_trans hlt (by decide)) (by decide)).mpr hlt
  simp only [UInt256.lt, decide_eq_true hw]; decide

theorem lt32_size_word {n : ℕ} (hn : 32 ≤ n) (hb : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) = UInt256.ofNat 0 := by
  have hw : ¬ (UInt256.ofNat n < UInt256.ofNat 32) := by
    rw [ofNat_lt_ofNat hb (by decide)]; omega
  simp only [UInt256.lt, decide_eq_false hw]; decide

theorem lt32_size_word_ne {n : ℕ} (hn : n < 32) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) ≠ UInt256.ofNat 0 := by
  have hw : UInt256.ofNat n < UInt256.ofNat 32 :=
    (ofNat_lt_ofNat (lt_trans hn (by decide)) (by decide)).mpr hn
  simp only [UInt256.lt, decide_eq_true hw]; decide

theorem succ_word {h : ℕ} (hlt : h < 31) :
    UInt256.ofNat 1 + UInt256.ofNat h = UInt256.ofNat (h + 1) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' 1 (by decide), ulit_toNat' h (lt_trans hlt (by decide)),
    ulit_toNat' (h + 1) (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega),
    Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]
  omega

/-! ## The loop as Stele syntax -/

abbrev ctorInit : List Stmt :=
  [.letDecl "height" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

abbrev ctorCond : Expr := .binary .lt (.var "height") (.intLit 31)

abbrev ctorPost : List Stmt :=
  [.assign .localVar { base := "height", steps := [] } (.binary .add (.var "height") (.intLit 1))]

abbrev ctorLoopBody : List Stmt :=
  [ .letDecl "cur" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage { base := "zero_hashes", steps := [.aindex (.var "height")] }),
    .internalCall "sha256_pair" [.var "cur", .var "cur"] "next",
    .assign .storage
      { base := "zero_hashes", steps := [.aindex (.binary .add (.var "height") (.intLit 1))] }
      (.var "next") ]

theorem ctorBody_eq :
    contract.ctor.body =
      [.require (.binary .eq (.env .callvalue) (.intLit 0)),
       .for ctorInit ctorCond ctorPost ctorLoopBody] := rfl

theorem evalHeightLt {L : Store} {evm : EVM.State} {h : ℕ}
    (hh : L.get? "height" = some (.int (Int.ofNat h))) :
    evalExpr? config { contract := contract, locals := L } evm ctorCond =
      .ok (.bool (decide (Int.ofNat h < 31))) :=
  evalBin (by decide) (by decide) (evalVarL hh) (evalLit 31) (evalBinaryOp_lt_int_ok _ _)

theorem evalHeightSucc {L : Store} {evm : EVM.State} {h : ℕ}
    (hh : L.get? "height" = some (.int (Int.ofNat h))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .add (.var "height") (.intLit 1)) = .ok (.int (Int.ofNat (h + 1))) := by
  rw [evalBin (by decide) (by decide) (evalVarL hh) (evalLit 1) (evalBinaryOp_add_int_ok _ _)]
  rfl

/-! ## The simulation -/

/-- `zero_hashes[h]` as the loop reads it. -/
abbrev curWord (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) : UInt256 :=
  solcSlotWord σ I (⟨33⟩ + UInt256.ofNat h)

abbrev loopL1 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) : Store :=
  L.insert "cur" (.int (Int.ofNat (curWord σ I h).toNat))

abbrev loopL2 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) (out : ByteArray) : Store :=
  (loopL1 L σ I h).insert "next" (shaDigest out)

abbrev loopL3 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) (out : ByteArray) : Store :=
  (loopL2 L σ I h out).insert "height" (.int (Int.ofNat (h + 1)))

theorem ctorLoop {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true) :
    ∀ n h, h + n = 31 → ∀ {σh : AccountMap} {evmh : EVM.State} {mem rdata : ByteArray}
      {aw : UInt256} {k C : ℕ} {L : Store},
      L.get? "height" = some (.int (Int.ofNat h)) → L.get? "zero_hashes" = none →
      RD ctorCode I g s0 (UInt256.ofNat 5) [UInt256.ofNat h] mem aw rdata σh k C →
      SourceState s0 I σh evmh →
      (RDrev ctorCode g s0 ∧
        ExecForLoop config { contract := contract, locals := L } evmh ctorCond ctorPost ctorLoopBody
          .reverted) ∨
      (∃ (σf : AccountMap) (evmf : EVM.State) (Lf : Store) (mem' rdata' : ByteArray)
          (aw' : UInt256) (k' C' : ℕ),
        SourceState s0 I σf evmf ∧
        RD ctorCode I g s0 (UInt256.ofNat 71) [UInt256.ofNat 31] mem' aw' rdata' σf k' C' ∧
        ExecForLoop config { contract := contract, locals := L } evmh ctorCond ctorPost ctorLoopBody
          (.ok { contract := contract, locals := Lf } evmf)) := by
  intro n
  induction n with
  | zero =>
    intro h hn σh evmh mem rdata aw k C L hh hz rd hs
    obtain rfl : h = 31 := by omega
    right
    have rd71 := feDepositCreationBlocks.feDepositCreation_block_5_taken (by simp) (by decide)
      (by jump_dest) rd
    refine ⟨σh, evmh, L, mem, rdata, aw, _, _, hs, rd71, ExecForLoop.falseDone ?_⟩
    rw [evalHeightLt hh]
    rfl
  | succ m ih =>
    intro h hn σh evmh mem rdata aw k C L hh hz rd hs
    have hlt : h < 31 := by omega
    have hcond : evalExpr? config { contract := contract, locals := L } evmh ctorCond =
        .ok (.bool true) := by
      have hlt' : Int.ofNat h < 31 := Int.ofNat_lt.mpr hlt
      rw [evalHeightLt hh, decide_eq_true hlt']
    have rd14 := feDepositCreationBlocks.feDepositCreation_block_5_fallthrough (by simp)
      (lt31_word hlt) rd
    obtain ⟨gas, k1, C1, rd35⟩ := feDepositCreationBlocks.feDepositCreation_block_14 (by simp) rd14
    simp only [feDepositCreationBlocks.feDepositCreation_block_14_stack,
      feDepositCreationBlocks.feDepositCreation_block_14_memory] at rd35
    obtain ⟨evm', σ', z, out, aw', k2, C2, hcall, hs', rd36, hob⟩ :=
      staticCallBridge rd35 hs (by native_decide) (by simp)
    have rd36' := RD.normalizePC (pc' := UInt256.ofNat 36) rd36 (by decide)
    rw [pairMem_read, ← precompile2_eq] at hcall
    -- the Stele body up to the call
    have hcur := zeroHash_read (L := L) (evm := evmh) (i := h) (by omega) (evalVarL hh) hz
    rw [hs.storageRead] at hcur
    have hcurVar : evalExpr? config { contract := contract, locals := loopL1 L σh I h } evmh
        (.var "cur") =
        .ok (.int (Int.ofNat (σh.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD ((UInt256.ofNat 33) + UInt256.ofNat h) (⟨0⟩ : UInt256))).toNat)) :=
      evalVarL (store_get_self _ _ _)
    by_cases hok : z = true ∧ 32 ≤ out.size
    · obtain ⟨rfl, hout⟩ := hok
      have rd45 := feDepositCreationBlocks.feDepositCreation_block_36_taken (by simp) (by decide)
        (by jump_dest) rd36'
      have rd54 := feDepositCreationBlocks.feDepositCreation_block_45_fallthrough
        (by simp [feDepositCreationBlocks.feDepositCreation_block_36_taken_stack])
        (lt32_size_word hout hob) rd45
      obtain ⟨k3, C3, rd5⟩ := feDepositCreationBlocks.feDepositCreation_block_54
        (by simp [feDepositCreationBlocks.feDepositCreation_block_36_taken_stack]) hperm
        (by jump_dest) rd54
      simp only [feDepositCreationBlocks.feDepositCreation_block_54_stack,
        feDepositCreationBlocks.feDepositCreation_block_36_taken_stack] at rd5
      rw [callOutput_load32 _ out hob hout (le_trans (by decide) (pairMem_size _ _)),
        succ_word hlt] at rd5
      -- the Stele body after the call
      have hcall2 := shaPairCall_ok (caller := { contract := contract, locals := loopL1 L σh I h })
        rfl (ret := "next") hcurVar hcurVar hcall hout
      have hh2 : (loopL2 L σh I h out).get? "height" = some (.int (Int.ofNat h)) := by
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh]
      have hz2 : (loopL2 L σh I h out).get? "zero_hashes" = none := by
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hz]
      have hassign := zeroHash_write (evm := evm') (i := h + 1) (by omega) (evalHeightSucc hh2) hz2
        (calldataWord out 0)
      rw [hs'.env] at hassign
      have hs'' := hs'.storageWrite (⟨33⟩ + UInt256.ofNat (h + 1)) (calldataWord out 0)
      have hstore := ExecStmt.assign (hperm := Or.inr (by rw [hs'.env]; exact hperm))
        (evalVarL (store_get_self _ _ _)) hassign
      have hpost := ExecStmt.assign (cfg := config) (hperm := Or.inl rfl)
        (evalHeightSucc (evm := Stele.EVM.storageStore evm' I.codeOwner (⟨33⟩ + UInt256.ofNat (h + 1))
          (calldataWord out 0)) hh2) (assignLocal_ok (old := .int (Int.ofNat h)) hh2)
      have hh3 : (loopL3 L σh I h out).get? "height" = some (.int (Int.ofNat (h + 1))) :=
        store_get_self _ _ _
      have hz3 : (loopL3 L σh I h out).get? "zero_hashes" = none := by
        rw [store_get_ne _ _ (by decide), hz2]
      have hbody : ExecBlock config { contract := contract, locals := L } evmh ctorLoopBody
          (.ok { contract := contract, locals := loopL2 L σh I h out }
            (Stele.EVM.storageStore evm' I.codeOwner (⟨33⟩ + UInt256.ofNat (h + 1))
              (calldataWord out 0))) :=
        ExecBlock.consNormal (ExecStmt.letDecl hcur) <|
          ExecBlock.consNormal hcall2 <| ExecBlock.consNormal hstore ExecBlock.nil
      rcases ih (h + 1) (by omega) hh3 hz3 rd5 hs'' with ⟨hrev, hloop⟩ | ⟨σf, evmf, Lf, mem', rdata', aw'', k', C', hsf, rd71, hloop⟩
      · exact Or.inl ⟨hrev, ExecForLoop.iterate hcond hbody (ExecBlock.consNormal hpost ExecBlock.nil) hloop⟩
      · exact Or.inr ⟨σf, evmf, Lf, mem', rdata', aw'', k', C', hsf, rd71,
          ExecForLoop.iterate hcond hbody (ExecBlock.consNormal hpost ExecBlock.nil) hloop⟩
    · left
      refine ⟨?_, ExecForLoop.bodyRevert hcond (ExecBlock.consNormal (ExecStmt.letDecl hcur)
        (ExecBlock.consRevert (shaPairCall_revert rfl hcurVar hcurVar hcall hok)))⟩
      cases z with
      | false =>
        exact feDepositCreationBlocks.feDepositCreation_block_41
          (by simp [feDepositCreationBlocks.feDepositCreation_block_36_fallthrough_stack])
          (feDepositCreationBlocks.feDepositCreation_block_36_fallthrough (by simp) (by decide) rd36')
      | true =>
        have hshort : out.size < 32 := by
          by_contra hge; exact hok ⟨rfl, by omega⟩
        have rd45 := feDepositCreationBlocks.feDepositCreation_block_36_taken (by simp) (by decide)
          (by jump_dest) rd36'
        exact feDepositCreationBlocks.feDepositCreation_block_41
          (by simp [feDepositCreationBlocks.feDepositCreation_block_36_taken_stack])
          (feDepositCreationBlocks.feDepositCreation_block_45_taken
            (by simp [feDepositCreationBlocks.feDepositCreation_block_36_taken_stack])
            (lt32_size_word_ne hshort) (by jump_dest) rd45)

end FeProofs.Deposit
