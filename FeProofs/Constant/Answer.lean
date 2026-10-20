import FeProofs.Constant.Dispatch

/-!
# FeConstant `answer()`

Fe checks call value inside the selector arm (pc 26).  With zero call value the body stores
`42` at memory offset 0 and returns that word; otherwise it reverts.
Dispatcher arm entry: pc 26; reach lemma `feConstantReachAnswerBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Constant

set_option maxRecDepth 2000000

theorem feConstantAnswerDecode {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (answerTransition.params.map Param.name)
      (transitionSignature answerTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- The word stored by `MSTORE(0, 42)` reads back as the returned 32 bytes. -/
theorem feConstantAnswerOutput :
    ((UInt256.ofNat 42).toByteArray.write 0 ByteArray.empty (⟨0⟩ : UInt256).toNat 32).readWithPadding
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat = UInt256.toByteArray ⟨42⟩ :=
  toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)

/-- `answer()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem feConstantAnswerBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feConstantBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feConstantSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feConstantSelBytes 0) rfl hsel
  have hd := feConstantDispatch_answer hsel
  obtain ⟨k, C, rd⟩ := feConstantReachAnswerBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feConstantBlocks.feConstant_block_26_taken (by simp) (by rw [hwv]; decide)
      (by jump_dest) rd
    have rret := feConstantBlocks.feConstant_block_36 (by simp) rd1
    rw [feConstantAnswerOutput] at rret
    exact rret.reEquivExecutionTransport hcode hd (feConstantAnswerDecode hsz)
      (nonpayableIntLiteralBodyReturns _ _ 42 (by simp only [initState]; exact hwv))
      (rvEvm := some [.int (Int.ofNat (UInt256.toNat ⟨42⟩))]) rfl
      (returnEquiv_of_encode (uint256ReturnEncoding ⟨42⟩))
  · have rd1 := feConstantBlocks.feConstant_block_26_fallthrough (by simp)
      (isZero_eq_zero_of_ne hwv) rd
    have rrev := feConstantBlocks.feConstant_block_32 (by simp) rd1
    exact rrev.reEquivExecutionRevert hcode hd (feConstantAnswerDecode hsz)
      (bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end FeProofs.Constant
