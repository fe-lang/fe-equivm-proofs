import FeProofs.Deposit.Dispatch
import FeProofs.Deposit.Le64
import FeProofs.Common.Basic

/-!
# FeDeposit `get_deposit_count()`

Arm entry pc 1716 checks call value.  The body (pc 1723) loads slot 32, masks it to 64 bits,
byte-swaps it into an SSZ chunk with three passes, allocates the `bytes` value at `0x100`, writes
the head offset at `0xa0`, `MCOPY`s the value behind it, and returns `[0xa0, 0x100)`.  The spec's
`le64(uint64(deposit_count))` performs the same passes (`Le64.lean`), so the returned word is the
ABI encoding of its eight bytes.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

theorem feDepositGetCountDecode {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (get_deposit_countTransition.params.map Param.name)
      (transitionSignature get_deposit_countTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `get_deposit_count()`: the theorem `Correct.lean` routes selector 2 to. -/
theorem feDepositGet_deposit_countBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feDepositSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feDepositSelBytes 2) rfl hsel
  have h0 : ¬ selIs I (feDepositSelBytes 0) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h1 : ¬ selIs I (feDepositSelBytes 1) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd := feDepositDispatch_get_deposit_count h0 h1 hsel
  obtain ⟨k, C, rd⟩ := feDepositReachGet_deposit_countBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd using [hwv, (by native_decide)]
  rw [evmChunk_eq, countReturn_eq] at rd
  obtain ⟨F, hbody⟩ := getCountBody (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (by simp only [initState]; exact hwv)
  rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hbody
  exact rd.reEquivExecution hcode hd (feDepositGetCountDecode hsz) hbody
    (returnEquiv.returned rfl (le64_returnEncoding _))

end FeProofs.Deposit
