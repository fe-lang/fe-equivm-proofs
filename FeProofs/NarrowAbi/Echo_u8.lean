import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_u8(uint8)`

Arm entry pc 124: call-value check, head-size check (pc 130), the canonical check
`GT(word, 255)` (pc 142), and `MSTORE(0, word); RETURN(0, 32)` (pc 172).  A dirty word takes the
`None` path (pc 158), whose tag check at pc 163 reverts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_u8Body {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 1) rfl hsel
  have hd := feNarrowAbiDispatch_echo_u8 hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_u8Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hlen : 36 ≤ I.calldata.size
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_uint_none_short _ (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckHuge_4_32 (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_uint_none_huge _ (by omega))
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have h256 : EVM.twoPow 8 = 256 := rfl
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.twoPow 8
  swap
  · rd_run rd using [(ugt_one (a := calldataWord I.calldata 4) (b := UInt256.ofNat 255)
      (show 255 < _ by omega)).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd
      ((decodeCalldata_uint_result _ hlen hhi).trans (if_neg hcanon))
  rd_run rd using [ugt_zero (a := calldataWord I.calldata 4) (b := UInt256.ofNat 255)
    (show _ ≤ 255 by omega)]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
  exact rd.reEquivExecution hcode hd ((decodeCalldata_uint_result _ hlen hhi).trans (if_pos hcanon))
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
      (evalLocalVar (store_get_self _ _ _)))
    (returnEquiv_of_encode (uint8ReturnEncoding _ hcanon))

end FeProofs.NarrowAbi
