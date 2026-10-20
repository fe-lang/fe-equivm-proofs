import FeProofs.IndexedPackedStore.Dispatch
import FeProofs.IndexedPackedStore.Elems
import FeProofs.IndexedPackedStore.Static
import FeProofs.Common.Basic
import Reasoning.ExternalCall

/-!
# FeIndexedPackedStore `setTwo(uint256,uint256,uint256,uint256)`

Arm entry pc 153: call-value check, head check (pc 159), the first `index < 64` check (pc 171), the
first lane write followed by the second index check (pc 182), then the second lane write and an
empty return (pc 263).  A bad second index reverts after the first write, which the revert
discards; under `STATICCALL` the first `SSTORE` halts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach FeProofs.Common

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev setTwoStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "first_index" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert
    "first_value" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))).insert "second_index"
    (.int (Int.ofNat (calldataWord I.calldata 68).toNat))).insert "second_value"
    (.int (Int.ofNat (calldataWord I.calldata 100).toNat))

set_option maxHeartbeats 1000000 in
theorem feIndexedPackedStoreSetTwoBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feIndexedPackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feIndexedPackedStoreSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feIndexedPackedStoreSelBytes 1) rfl hsel
  have hd := feIndexedPackedStoreDispatch_setTwo (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feIndexedPackedStoreReachSetTwoBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_153_fallthrough (by simp) hwv rd
    simp only [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_153_fallthrough_stack] at rd1
    by_cases hok : 132 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨hlen, hhi⟩ := hok
      have rd2 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_159_fallthrough (by simp)
        (solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 4) (by omega) hhi hsize) rd1
      have hdec : config.externalABI.decodeCalldata? (setTwoTransition.params.map Param.name)
          (transitionSignature setTwoTransition).paramTypes I.calldata = some (setTwoStore I) := by
        show decodeCalldata ["first_index", "first_value", "second_index", "second_value"]
          [abiUInt256, abiUInt256, abiUInt256, abiUInt256] I.calldata = _
        exact decodeCalldata_four_uint256_ok hlen hhi
      set i1 := (calldataWord I.calldata 4).toNat with hi1
      set i2 := (calldataWord I.calldata 68).toNat with hi2
      set evm := initState σ σ₀ (Sat256.ofUInt256 g) A I with hevm
      have hx1 : (setTwoStore I).get? "first_index" = some (.int (Int.ofNat i1)) := by
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
          store_get_self]
      have hv1 : (setTwoStore I).get? "first_value" =
          some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) := by
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
      have hx2 : (setTwoStore I).get? "second_index" = some (.int (Int.ofNat i2)) := by
        rw [store_get_ne _ _ (by decide), store_get_self]
      have hv2 : (setTwoStore I).get? "second_value" =
          some (.int (Int.ofNat (calldataWord I.calldata 100).toNat)) := store_get_self _ _ _
      have hreq := ExecStmt.requireTrue (cfg := config)
        (stele := { contract := contract, locals := setTwoStore I })
        (evalCallvalueEq_true (evm := evm) (by simp only [hevm, initState]; exact hwv))
      by_cases hin1 : i1 < 64
      · have rd3 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_171_fallthrough (by simp)
          (by rw [ult_one (by rw [ulit_toNat' 64 (by decide)]; exact hin1)]; decide) rd2
        simp only [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_171_fallthrough_stack] at rd3
        have hreq1 := ExecStmt.requireTrue (cfg := config)
          (stele := { contract := contract, locals := setTwoStore I }) (evm := evm)
          (by rw [evalIndexLt hx1, decide_eq_true hin1])
        have hval1 := evalCastU8 (evm := evm) (L := setTwoStore I) hv1
        have hasg1 := assignElem (evm := evm) hin1 hx1 (by simp) (calldataWord I.calldata 36)
        set evm1 := Stele.EVM.storageStore evm evm.executionEnv.codeOwner (elemSlot i1)
          (setPackedByte (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (elemSlot i1))
            (calldataWord I.calldata 36) (elemByte i1)) with hevm1
        by_cases hperm : I.perm = true
        · have hp0 : evm.executionEnv.perm = true := by simp only [hevm, initState]; exact hperm
          have hp1 : evm1.executionEnv.perm = true := by
            rw [hevm1, storageStore_executionEnv]; exact hp0
          have hassign1 := ExecStmt.assign (Or.inr hp0) hval1 hasg1
          by_cases hin2 : i2 < 64
          · obtain ⟨k4, C4, rd4⟩ := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_182_fallthrough
              (by simp) hperm
              (by rw [ult_one (by rw [ulit_toNat' 64 (by decide)]; exact hin2)]; decide) rd3
            simp only [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_182_fallthrough_stack] at rd4
            have rret := RDret.of_output_eq
              (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_263 (by simp) hperm rd4)
              (byteArray_readWithPadding_zero _ _)
            have hreq2 := ExecStmt.requireTrue (cfg := config)
              (stele := { contract := contract, locals := setTwoStore I }) (evm := evm1)
              (by rw [evalIndexLt hx2, decide_eq_true hin2])
            have hval2 := evalCastU8 (evm := evm1) (L := setTwoStore I) hv2
            have hasg2 := assignElem (evm := evm1) hin2 hx2 (by simp) (calldataWord I.calldata 100)
            refine rret.reEquivExecutionGen hcode hd hdec
              (ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq (ExecBlock.consNormal hreq1
                (ExecBlock.consNormal hassign1 (ExecBlock.consNormal hreq2 (ExecBlock.consNormal
                  (ExecStmt.assign (Or.inr hp1) hval2 hasg2) ExecBlock.nil))))))
              ?_ (returnEquiv.fallthrough rfl rfl (by native_decide))
            have hs0 : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
            have hs1 := hs0.storageWrite (elemSlot i1)
              (setPackedByte (solcSlotWord σ I (elemSlot i1)) (calldataWord I.calldata 36) (elemByte i1))
            have hevm1' : evm1 = Stele.EVM.storageStore evm I.codeOwner (elemSlot i1)
                (setPackedByte (solcSlotWord σ I (elemSlot i1)) (calldataWord I.calldata 36)
                  (elemByte i1)) := by
              rw [hevm1, hs0.storageRead]
              rfl
            have hs2 := hs1.storageWrite (elemSlot i2)
              (setPackedByte (solcSlotWord (sstoreAccountMap I.codeOwner σ (elemSlot i1)
                (setPackedByte (solcSlotWord σ I (elemSlot i1)) (calldataWord I.calldata 36)
                  (elemByte i1))) I (elemSlot i2)) (calldataWord I.calldata 100) (elemByte i2))
            rw [laneWrite_eq, laneWrite_eq, shr5_eq, shr5_eq]
            refine hs2.accounts.trans ?_
            have hload : Stele.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (elemSlot i2) =
                solcSlotWord (sstoreAccountMap I.codeOwner σ (elemSlot i1)
                  (setPackedByte (solcSlotWord σ I (elemSlot i1)) (calldataWord I.calldata 36)
                    (elemByte i1))) I (elemSlot i2) := by
              rw [hevm1']; exact hs1.storageRead (elemSlot i2)
            have hco : evm1.executionEnv.codeOwner = I.codeOwner := by rw [hevm1', hs1.env]
            rw [hload, hco, ← hevm1']
          · obtain ⟨k4, C4, rd4⟩ := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_182_taken
              (by simp) hperm
              (by rw [ult_zero (by rw [ulit_toNat' 64 (by decide)]; exact Nat.le_of_not_lt hin2)]; decide)
              (by jump_dest) rd3
            exact RDrev.reEquivExecutionRevert hcode
              (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75
                (by simp [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_182_taken_stack]) rd4)
              hd hdec
              (ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consNormal hreq1
                (ExecBlock.consNormal hassign1 (ExecBlock.consRevert (ExecStmt.requireFalse
                  (by rw [evalIndexLt hx2, decide_eq_false hin2])))))))
        · have hpf : I.perm = false := by simpa using hperm
          exact RDstatic.reEquivStaticHalt hcode
            (feIndexedPackedStore_block_182_static (by simp) rd3 hpf) hd hdec
            (ExecFuncBody.execBlockStatic (ExecBlock.consNormal hreq (ExecBlock.consNormal hreq1
              (ExecBlock.consStatic
                (ExecStmt.assignStatic hval1 hasg1 (by simp only [hevm, initState]; exact hpf))))))
      · have rd3 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_171_taken (by simp)
          (by rw [ult_zero (by rw [ulit_toNat' 64 (by decide)]; exact Nat.le_of_not_lt hin1)]; decide)
          (by jump_dest) rd2
        exact RDrev.reEquivExecutionRevert hcode
          (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75
            (by simp [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_171_taken_stack]) rd3)
          hd hdec
          (ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consRevert
            (ExecStmt.requireFalse (by rw [evalIndexLt hx1, decide_eq_false hin1])))))
    · have hbad : I.calldata.size < 132 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
          (UInt256.ofNat (32 * 4)) = ⟨1⟩ := by
        rcases hbad with h | h
        · exact solcCalldataStaticLenCheckShort hsz h hsize (by norm_num)
        · exact solcCalldataStaticLenCheckHuge h hsize (by norm_num)
      have rd2 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_159_taken (by simp)
        (fun h => absurd (hslt.symm.trans h) (by decide)) (by jump_dest) rd1
      refine RDrev.reEquivDecodingFailed hcode
        (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75 (by simp) rd2) hd ?_
      show decodeCalldata ["first_index", "first_value", "second_index", "second_value"]
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256] I.calldata = _
      rcases hbad with h | h
      · exact decodeCalldata_four_uint256_none_short h
      · exact decodeCalldata_four_uint256_none_huge h
  · have rd1 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_153_taken (by simp) hwv
      (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75
        (by simp [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_153_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.IndexedPackedStore
