import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.Storage
import FeProofs.Common.Basic

/-!
# FeERC20 `totalSupply()`

Arm entry pc 189: the call-value check (revert block 86), then `MSTORE(0, SLOAD(2))` and a
32-byte `RETURN` at pc 194.  There are no arguments, so no head check.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

theorem feERC20TotalSupplyDecode {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `totalSupply()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem feERC20TotalSupplyBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 1) rfl hsel
  have h0 : ¬ selIs I (feERC20SelBytes 0) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd := feERC20Dispatch_totalSupply h0 hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTotalSupplyBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feERC20Blocks.feERC20_block_189_fallthrough (by simp) hwv rd
    have rret := feERC20Blocks.feERC20_block_194 (by simp) rd1
    have hout : ((σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0
          ByteArray.empty (⟨0⟩ : UInt256).toNat 32).readWithPadding (⟨0⟩ : UInt256).toNat
          (UInt256.ofNat 32).toNat = (solcSlotWordAt ⟨2⟩ σ I).toByteArray :=
      toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)
    rw [hout] at rret
    have hread := totalSupply_read (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (by simp)
    rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
    exact rret.reEquivExecution hcode hd (feERC20TotalSupplyDecode hsz)
      (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
      (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWordAt ⟨2⟩ σ I)))
  · have rd1 := feERC20Blocks.feERC20_block_189_taken (by simp) hwv (by jump_dest) rd
    exact RDrev.reEquivDispatchedRevert hcode (feERC20Blocks.feERC20_block_86 (by simp) rd1)
      hd fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ERC20
