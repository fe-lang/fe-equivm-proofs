import FeProofs.ScalarStore.Dispatch
import FeProofs.ScalarStore.Storage
import FeProofs.Common.Basic

/-!
# FeScalarStore `get()`

Arm entry pc 67: the call-value check, then `MSTORE(0, SLOAD(0))` and a 32-byte `RETURN`
at pc 72.  There are no arguments, so no head check.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ScalarStore

set_option maxRecDepth 2000000

theorem feScalarStoreGetDecode {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (getTransition.params.map Param.name)
      (transitionSignature getTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `get()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem feScalarStoreGetBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 1) rfl hsel
  have h0 : ¬ selIs I (feScalarStoreSelBytes 0) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd := feScalarStoreDispatch_get h0 hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachGetBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
  have hread := stored_read (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (by simp)
  exact rd.reEquivExecution hcode hd (feScalarStoreGetDecode hsz)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWordAt ⟨0⟩ σ I)))

end FeProofs.ScalarStore
