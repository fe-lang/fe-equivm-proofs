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
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := totalSupply_read (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (by simp)
  rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  exact rd.reEquivExecution hcode hd (feERC20TotalSupplyDecode hsz)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWordAt ⟨2⟩ σ I)))

end FeProofs.ERC20
