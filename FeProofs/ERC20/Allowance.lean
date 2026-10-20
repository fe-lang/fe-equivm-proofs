import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `allowance(address,address)`

Arm entry pc 743: call-value check, head-size check (pc 749), the canonical-address checks for
`owner` (pc 761) and `spender` (pc 771), then the nested map read
`SLOAD(keccak256(spender ‖ keccak256(owner ‖ 1)))` returned as one word (pc 781).  Every failed
check jumps to the revert block at pc 86.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- `allowance(address,address)`: the theorem `Correct.lean` routes selector 5 to. -/
theorem feERC20AllowanceBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 5) rfl hsel
  have hd := feERC20Dispatch_allowance
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachAllowanceBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  have hdecFail : ∀ {cd : ByteArray}, decodeCalldata ["owner", "spender"]
      [.elem .address, .elem .address] cd = none →
      config.externalABI.decodeCalldata? (allowanceTransition.params.map Param.name)
        (transitionSignature allowanceTransition).paramTypes cd = none := fun h => h
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feERC20Blocks.feERC20_block_743_fallthrough (by simp) hwv rd
    simp only [feERC20Blocks.feERC20_block_743_fallthrough_stack] at rd1
    by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feERC20Blocks.feERC20_block_749_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_64 hlen hhi hsize) rd1
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have rd3 := feERC20Blocks.feERC20_block_761_fallthrough (by simp)
            (shiftRight160_eq_zero hc0) rd2
          simp only [feERC20Blocks.feERC20_block_761_fallthrough_stack] at rd3
          by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · have rd4 := feERC20Blocks.feERC20_block_771_fallthrough (by simp)
              (shiftRight160_eq_zero hc1) rd3
            simp only [feERC20Blocks.feERC20_block_771_fallthrough_stack] at rd4
            have rret := feERC20Blocks.feERC20_block_781 (by simp) rd4
            rw [keccakWord_mapSlot, keccakWord_mapSlot] at rret
            have rret' := RDret.of_output_eq rret
              (toByteArray_write32_read_back _ (solcSlotWordAt (mapSlot (calldataWord I.calldata 36)
                (mapSlot (calldataWord I.calldata 4) (UInt256.ofNat 1))) σ I) 0 (Nat.zero_le _))
            have hdec : config.externalABI.decodeCalldata? (allowanceTransition.params.map Param.name)
                (transitionSignature allowanceTransition).paramTypes I.calldata =
                some (((∅ : Store).insert "owner"
                  (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "spender"
                  (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))) :=
              decodeCalldata_address_address_ok hlen hhi hc0 hc1
            have hread := allowance_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (L := ((∅ : Store).insert "owner"
                (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "spender"
                (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)))
              hc0 hc1 (by simp) ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
              (store_get_self _ _ _)
            rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
            exact rret'.reEquivExecution hcode hd hdec
              (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
              (returnEquiv_of_encode (uint256ReturnEncoding _))
          · have rd4 := feERC20Blocks.feERC20_block_771_taken (by simp)
              (shiftRight160_ne_zero (Nat.le_of_not_lt hc1)) (by jump_dest) rd3
            exact RDrev.reEquivDecodingFailed hcode
              (feERC20Blocks.feERC20_block_86
                (by simp [feERC20Blocks.feERC20_block_771_taken_stack]) rd4) hd
              (hdecFail (decodeCalldata_address_address_none_noncanon1 hlen hhi hc0 hc1))
        · have rd3 := feERC20Blocks.feERC20_block_761_taken (by simp)
            (shiftRight160_ne_zero (Nat.le_of_not_lt hc0)) (by jump_dest) rd2
          exact RDrev.reEquivDecodingFailed hcode
            (feERC20Blocks.feERC20_block_86
              (by simp [feERC20Blocks.feERC20_block_761_taken_stack]) rd3) hd
            (hdecFail (decodeCalldata_address_address_none_noncanon0 hlen hhi hc0))
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feERC20Blocks.feERC20_block_749_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_64 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        exact RDrev.reEquivDecodingFailed hcode
          (feERC20Blocks.feERC20_block_86 (by simp) rd2) hd
          (hdecFail (decodeCalldata_address_address_none_huge hbig))
    · have hshort : I.calldata.size < 68 := by omega
      have rd2 := feERC20Blocks.feERC20_block_749_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_64 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode
        (feERC20Blocks.feERC20_block_86 (by simp) rd2) hd
        (hdecFail (decodeCalldata_address_address_none_short hsz hshort))
  · have rd1 := feERC20Blocks.feERC20_block_743_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feERC20Blocks.feERC20_block_86
        (by simp [feERC20Blocks.feERC20_block_743_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ERC20
