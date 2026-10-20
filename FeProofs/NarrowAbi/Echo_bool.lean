import FeProofs.NarrowAbi.Dispatch
import FeProofs.NarrowAbi.Words
import FeProofs.Common.Basic

/-!
# FeNarrowAbi `echo_bool(bool)`

Arm entry pc 180: call-value check, head-size check (pc 186), the canonical check (zero at
pc 198, otherwise `EQ(1, word)` at pc 206), and the re-encoding of the decoded flag as `0`/`1`
(pcs 221–237).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

theorem feNarrowAbiEcho_boolBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feNarrowAbiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feNarrowAbiSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feNarrowAbiSelBytes 2) rfl hsel
  have hd := feNarrowAbiDispatch_echo_bool
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feNarrowAbiReachEcho_boolBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hlen : 36 ≤ I.calldata.size
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_word_none_short rfl (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · rd_run rd using [hwv, (solcDecodeLenCheckHuge_4_32 (by omega) hsize).trans_ne (by decide)]
    exact rd.reEquivDecodingFailed hcode hd (decodeCalldata_word_none_huge rfl (by omega))
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hbody : ∀ b : Bool, ExecTransitionBody config contract
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ((∅ : Store).insert "value" (.bool b))
      echo_boolTransition.body
      (.returned { contract := contract, locals := (∅ : Store).insert "value" (.bool b) }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [.bool b])) := fun b =>
    nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv)
      (evalLocalVar (store_get_self _ _ _))
  -- The argument word as the block summaries spell it.
  have hW : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
      calldataWord I.calldata 4 := rfl
  by_cases hw0 : calldataWord I.calldata 4 = ⟨0⟩
  · rd_run rd using [hW.trans hw0]
    u256_lits at rd
    rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
    have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
        (transitionSignature echo_boolTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bool false)) := by
      show decodeCalldata ["value"] [.elem .bool] I.calldata = _
      rw [decodeCalldata_word rfl hlen hhi, hw0]
      rfl
    exact rd.reEquivExecution hcode hd hdec (hbody false)
      (returnEquiv_of_encode boolFalseReturnEncoding)
  by_cases hw1 : calldataWord I.calldata 4 = ⟨1⟩
  · rd_run rd using [hW.trans hw1]
    u256_lits at rd
    rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
    have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
        (transitionSignature echo_boolTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "value" (.bool true)) := by
      show decodeCalldata ["value"] [.elem .bool] I.calldata = _
      rw [decodeCalldata_word rfl hlen hhi, hw1]
      rfl
    exact rd.reEquivExecution hcode hd hdec (hbody true)
      (returnEquiv_of_encode boolTrueReturnEncoding)
  rd_step rd using [isZero_eq_zero_of_ne hw0]
  rd_run rd using [hW, uInt256_eq_zero_of_ne (a := UInt256.ofNat 1)
    (fun h => hw1 (uInt256_eq_one_eq h).symm)]
  have hdec : config.externalABI.decodeCalldata? (echo_boolTransition.params.map Param.name)
      (transitionSignature echo_boolTransition).paramTypes I.calldata = none := by
    show decodeCalldata ["value"] [.elem .bool] I.calldata = _
    rw [decodeCalldata_word rfl hlen hhi]
    have hz : (↑(calldataWord I.calldata 4).val : Nat) ≠ 0 := fun h => hw0 (u256_inj h)
    have ho : (↑(calldataWord I.calldata 4).val : Nat) ≠ 1 := fun h => hw1 (u256_inj h)
    simp only [decodeABIWord?, if_neg hz, if_neg ho]
    rfl
  exact RDrev.reEquivDecodingFailed hcode rd hd hdec

end FeProofs.NarrowAbi
