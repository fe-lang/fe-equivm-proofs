import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `balanceOf(address)`

Arm entry pc 540: call-value check, head-size check (pc 546), the canonical-address check
`SHR(160, word) = 0` (pc 558), then `MSTORE(0, owner); MSTORE(32, 0); SLOAD(KECCAK256(0, 64))`
returned as one word (pc 568).  Every failed check jumps to the revert block at pc 86.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach FeProofs.Common

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem feERC20BalanceOfBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 3) rfl hsel
  have hd := feERC20Dispatch_balanceOf
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachBalanceOfBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feERC20Blocks.feERC20_block_540_fallthrough (by simp) hwv rd
    simp only [feERC20Blocks.feERC20_block_540_fallthrough_stack] at rd1
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd2 := feERC20Blocks.feERC20_block_546_fallthrough (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have rd3 := feERC20Blocks.feERC20_block_558_fallthrough (by simp)
            (shiftRight160_eq_zero hcanon) rd2
          simp only [feERC20Blocks.feERC20_block_558_fallthrough_stack] at rd3
          have rret := feERC20Blocks.feERC20_block_568 (by simp) rd3
          rw [keccakWord_mapSlot] at rret
          have rret' := RDret.of_output_eq rret
            (toByteArray_write32_read_back _ (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨0⟩) σ I)
              0 (Nat.zero_le _))
          have hdec : config.externalABI.decodeCalldata? (balanceOfTransition.params.map Param.name)
              (transitionSignature balanceOfTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "owner"
                (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) :=
            decodeCalldata_address_ok hlen hhi hcanon
          have hread := balanceOf_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (L := (∅ : Store).insert "owner"
              (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) hcanon
            (by simp) (store_get_self _ _ _)
          rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
          exact rret'.reEquivExecution hcode hd hdec
            (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
            (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have rd3 := feERC20Blocks.feERC20_block_558_taken (by simp)
            (shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)) (by jump_dest) rd2
          refine RDrev.reEquivDecodingFailed hcode
            (feERC20Blocks.feERC20_block_86
              (by simp [feERC20Blocks.feERC20_block_558_taken_stack]) rd3) hd ?_
          show decodeCalldata ["owner"] [.elem .address] I.calldata = _
          exact decodeCalldata_address_none_noncanon hlen hhi hcanon
      · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        have rd2 := feERC20Blocks.feERC20_block_546_taken (by simp)
          (fun h => absurd ((solcDecodeLenCheckHuge_4_32 hbig hsize).symm.trans h) (by decide))
          (by jump_dest) rd1
        refine RDrev.reEquivDecodingFailed hcode
          (feERC20Blocks.feERC20_block_86 (by simp) rd2) hd ?_
        show decodeCalldata ["owner"] [.elem .address] I.calldata = _
        exact decodeCalldata_address_none_huge hbig
    · have hshort : I.calldata.size < 36 := by omega
      have rd2 := feERC20Blocks.feERC20_block_546_taken (by simp)
        (fun h => absurd ((solcDecodeLenCheckShort_4_32 hsz hshort hsize).symm.trans h) (by decide))
        (by jump_dest) rd1
      refine RDrev.reEquivDecodingFailed hcode
        (feERC20Blocks.feERC20_block_86 (by simp) rd2) hd ?_
      show decodeCalldata ["owner"] [.elem .address] I.calldata = _
      exact decodeCalldata_address_none_short hsz hshort
  · have rd1 := feERC20Blocks.feERC20_block_540_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feERC20Blocks.feERC20_block_86
        (by simp [feERC20Blocks.feERC20_block_540_taken_stack]) rd1) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ERC20
