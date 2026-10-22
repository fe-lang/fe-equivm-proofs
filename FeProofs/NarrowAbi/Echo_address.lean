import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_address(address)`

Arm entry pc 242: call-value check, head-size check (pc 248), the canonical-address check
`SHR(160, word) = 0` (pc 260), and `MSTORE(0, word); RETURN(0, 32)` (pc 270).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_addressBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 3) rfl hsel
  have hd := feNarrowAbiDispatch_echo_address hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_addressBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · nonpayable_revert rd hcode hd hwv
  by_cases hlen : 36 ≤ I.calldata.size
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckHuge_4_32 (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_huge (by omega))
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · rd_run rd using [shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
  rd_run rd using [shiftRight160_eq_zero hcanon]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
  exact rd.reEquivExecution hcode hd (decodeCalldata_address_ok hlen hhi hcanon)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
      (evalLocalVar (store_get_self _ _ _)))
    (returnEquiv_of_encode (addressReturnEncoding hcanon))

end FeProofs.NarrowAbi
