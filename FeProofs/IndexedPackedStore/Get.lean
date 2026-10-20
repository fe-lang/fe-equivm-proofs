import FeProofs.IndexedPackedStore.Dispatch
import FeProofs.IndexedPackedStore.Elems
import FeProofs.Common.Basic

/-!
# FeIndexedPackedStore `get(uint256)`

Arm entry pc 336: call-value check, head check (pc 342), the `index < 64` check (pc 354), then the
lane read of word `keccak256(0) + index / 32` and the 32-byte return (pc 365).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.IndexedPackedStore

set_option maxRecDepth 2000000

abbrev indexStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "index" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))

theorem feIndexedPackedStoreGetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feIndexedPackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feIndexedPackedStoreSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feIndexedPackedStoreSelBytes 2) rfl hsel
  have hd := feIndexedPackedStoreDispatch_get (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feIndexedPackedStoreReachGetBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_336_fallthrough (by simp) hwv rd
    simp only [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_336_fallthrough_stack] at rd1
    by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨hlen, hhi⟩ := hok
      have rd2 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_342_fallthrough (by simp)
        (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
      have hdec : config.externalABI.decodeCalldata? (getTransition.params.map Param.name)
          (transitionSignature getTransition).paramTypes I.calldata = some (indexStore I) := by
        show decodeCalldata ["index"] [abiUInt256] I.calldata = _
        exact decodeCalldata_uint256_ok hlen hhi
      set i := (calldataWord I.calldata 4).toNat with hi
      have hxi : (indexStore I).get? "index" = some (.int (Int.ofNat i)) := store_get_self _ _ _
      have hreq := ExecStmt.requireTrue (cfg := config)
        (stele := { contract := contract, locals := indexStore I })
        (evalCallvalueEq_true (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv))
      by_cases hin : i < 64
      · have rd3 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_354_fallthrough (by simp)
          (by
            rw [ult_one (by rw [ulit_toNat' 64 (by decide)]; exact hin)]
            decide) rd2
        simp only [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_354_fallthrough_stack] at rd3
        have rret := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_365 (by simp) rd3
        have hout : ((UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight
            (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
              ((UInt256.ofNat 18569430475105882587588266137607568536673111973893317399460219858819262702947) +
                (UInt256.shiftRight (calldataWord I.calldata 4) (UInt256.ofNat 5))) (⟨0⟩ : UInt256)))
            (UInt256.shiftLeft (UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 31))
              (UInt256.ofNat 3)))).toByteArray.write 0 ByteArray.empty (⟨0⟩ : UInt256).toNat 32).readWithPadding
            (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat =
            (packedByte (solcSlotWord σ I (elemSlot i)) (elemByte i)).toByteArray := by
          refine (toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)).trans ?_
          rw [laneRead_eq, shr5_eq]
          rfl
        have rret := RDret.of_output_eq rret hout
        have hval := evalElemCast (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hin hxi (by simp)
        rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hval
        exact rret.reEquivExecution hcode hd hdec
          (ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq (ExecBlock.consNormal
            (ExecStmt.requireTrue (by rw [evalIndexLt hxi, decide_eq_true hin]))
            (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hval))))))
          (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have rd3 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_354_taken (by simp)
          (by
            rw [ult_zero (by rw [ulit_toNat' 64 (by decide)]; exact Nat.le_of_not_lt hin)]
            decide) (by jump_dest) rd2
        exact RDrev.reEquivExecutionRevert hcode
          (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75
            (by simp [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_354_taken_stack]) rd3) hd hdec
          (ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consRevert
            (ExecStmt.requireFalse (by rw [evalIndexLt hxi, decide_eq_false hin])))))
    · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = ⟨1⟩ := by
        rcases hbad with h | h
        · exact solcDecodeLenCheckShort_4_32 hsz h hsize
        · exact solcDecodeLenCheckHuge_4_32 h hsize
      have rd2 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_342_taken (by simp)
        (by rw [hslt]; decide) (by jump_dest) rd1
      refine RDrev.reEquivDecodingFailed hcode
        (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75 (by simp) rd2) hd ?_
      show decodeCalldata ["index"] [abiUInt256] I.calldata = _
      rcases hbad with h | h
      · exact decodeCalldata_uint256_none_short h
      · exact decodeCalldata_uint256_none_huge h
  · have rd1 := feIndexedPackedStoreBlocks.feIndexedPackedStore_block_336_taken (by simp) hwv
      (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feIndexedPackedStoreBlocks.feIndexedPackedStore_block_75
        (by simp [feIndexedPackedStoreBlocks.feIndexedPackedStore_block_336_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.IndexedPackedStore
