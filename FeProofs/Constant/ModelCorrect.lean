import FeProofs.Constant.Correct
import FeProofs.Constant.Model
import Fe.EVM.Reach

/-!
# FeConstant: the runtime bytecode refines the model

The EVM half is the trace `Answer.lean` and `Dispatch.lean` already establish, restated as
terminals that mention the bytecode only.  The model half is evaluation of `Model.runtime`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.Constant

set_option maxRecDepth 2000000

/-! ## What the bytecode does -/

/-- `answer()` with no call value returns the word 42 and leaves the accounts unchanged. -/
theorem feConstantAnswerRet {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feConstantBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feConstantSelBytes 0)) (hwv : I.weiValue = ⟨0⟩) :
    RDret feConstantBytecode g (initState σ σ₀ g A I) σ (UInt256.toByteArray ⟨42⟩) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feConstantSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feConstantReachAnswerBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [hwv]
  rw [feConstantAnswerOutput] at rd
  exact rd

/-- `answer()` with call value reverts. -/
theorem feConstantAnswerRev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feConstantBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feConstantSelBytes 0)) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feConstantBytecode g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feConstantSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feConstantReachAnswerBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [isZero_eq_zero_of_ne hwv]
  exact rd

/-! ## What the model does -/

theorem runtime_short {I : ExecutionEnv} {w : World} (h : I.calldata.size < 4) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, h]

theorem runtime_noMatch {I : ExecutionEnv} {w : World} (hsz : 4 ≤ I.calldata.size)
    (h : ¬ selIs I (feConstantSelBytes 0)) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  have hsel : (Model.answerSelector == I.calldata.extract 0 4) = false := by
    simpa [selIs, Model.answerSelector, feConstantSelBytes] using h
  simp [Model.runtime, calldata, Nat.not_lt.mpr hsz, hsel]

theorem runtime_answer_value {I : ExecutionEnv} {w : World}
    (hsel : selIs I (feConstantSelBytes 0)) (hwv : I.weiValue ≠ ⟨0⟩) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feConstantSelBytes 0) rfl hsel
  have hsel' : (Model.answerSelector == I.calldata.extract 0 4) = true := hsel
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, hsel', hwv]

theorem runtime_answer {I : ExecutionEnv} {w : World}
    (hsel : selIs I (feConstantSelBytes 0)) (hwv : I.weiValue = ⟨0⟩) :
    Model.runtime.exec I w = some (.ok (UInt256.toByteArray ⟨42⟩, w)) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feConstantSelBytes 0) rfl hsel
  have hsel' : (Model.answerSelector == I.calldata.extract 0 4) = true := hsel
  simp [Model.runtime, calldata, nonPayable, Model.answer, Nat.not_lt.mpr hsz, hsel', hwv]

/-! ## Refinement -/

theorem feConstantRefinesModel : Refines .P0 feConstantBytecode Model.contract := by
  intro σ σ₀ g A I hcode hsize
  refine RefinesFor.closed ?_
  by_cases hsel : selIs I (feConstantSelBytes 0)
  · by_cases hwv : I.weiValue = ⟨0⟩
    · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode
        (feConstantAnswerRet hcode hsize hsel hwv) (runtime_answer hsel hwv) rfl
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feConstantAnswerRev hcode hsize hsel hwv) (runtime_answer_value hsel hwv) (by simp)
  · by_cases hsz : 4 ≤ I.calldata.size
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feConstantX_noMatch hcode hsz hsize (feConstantNoSelectorMatches hsel))
        (runtime_noMatch hsz hsel) (by simp)
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feConstantX_short hcode (by omega)) (runtime_short (by omega)) (by simp)

/-- Deployment with no constructor arguments. -/
theorem feConstantDeployRefinesModel :
    RefinesDeploy .P0 feConstantCreationBytecode feConstantBytecode Model.contract
      (· = ByteArray.empty) := by
  refine RefinesDeploy.closed ?_
  intro σ σ₀ g A I args hargs hcode _
  subst hargs
  rw [ByteArray.append_empty] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode (feConstantCtorRet hcode hwv)
      (w' := World.init σ A) (by simp [Model.contract, Model.init, nonPayable, hwv]) rfl
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feConstantCtorRev hcode hwv)
      (f := .revert ByteArray.empty) (by simp [Model.contract, Model.init, nonPayable, hwv])
      (by simp)

end FeProofs.Constant
