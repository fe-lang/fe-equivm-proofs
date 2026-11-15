import FeProofs.CodeScalar.Constructor
import FeProofs.CodeScalar.Model
import Fe.EVM.Reach

/-!
# FeCodeScalar: the bytecode refines the model

The first certificate of a contract with an immutable field.  The runtime bytecode refines the
model whatever word follows it, and the creation bytecode returns the runtime bytecode followed
by the word the model's constructor computes.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.CodeScalar

set_option maxRecDepth 2000000

/-! ## What the model does -/

section Model

variable {I : ExecutionEnv} {w : World}

theorem sel0 (h : selIs I (feCodeScalarSelBytes 0)) :
    (Model.getSelector == I.calldata.extract 0 4) = true := h

theorem sel0_not (h : ¬ selIs I (feCodeScalarSelBytes 0)) :
    (Model.getSelector == I.calldata.extract 0 4) = false := by
  simpa [selIs, Model.getSelector, feCodeScalarSelBytes] using h

theorem runtime_short (h : I.calldata.size < 4) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, h]

theorem runtime_noMatch (hsz : 4 ≤ I.calldata.size) (h0 : ¬ selIs I (feCodeScalarSelBytes 0)) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, Nat.not_lt.mpr hsz, ne_of_beq_false (sel0_not h0)]

theorem runtime_get_value (hsz : 4 ≤ I.calldata.size) (hsel : selIs I (feCodeScalarSelBytes 0))
    (hwv : I.weiValue ≠ ⟨0⟩) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, eq_of_beq (sel0 hsel), hwv]

/-- The word the model reads: the last 32 bytes of the running code. -/
theorem immutable_read (v : UInt256) (hcode : I.code = feCodeScalarBytecode ++ v.toByteArray) :
    Model.get.exec I w = some (.ok (v, w)) := by
  have hsize : I.code.size = 87 := by rw [hcode, code_size]
  have hat : (UInt256.ofNat 87 - UInt256.ofNat ((1 - 0) * 32)).toNat = 55 := by decide
  have hread : I.code.readWithPadding 55 32 = v.toByteArray := by
    rw [hcode, readWithPadding_eq_extract _ 55 (by have := code_size v; omega),
      extract_append_right' _ _ 55 (55 + 32) feCodeScalarBytecode_size.symm
        (by rw [feCodeScalarBytecode_size, toByteArray_size])]
  simp [Model.get, cload, immutableAt, hsize, hat, hread, uInt256OfByteArray_toByteArray]

theorem runtime_get (v : UInt256) (hcode : I.code = feCodeScalarBytecode ++ v.toByteArray)
    (hsz : 4 ≤ I.calldata.size) (hsel : selIs I (feCodeScalarSelBytes 0))
    (hwv : I.weiValue = ⟨0⟩) :
    Model.runtime.exec I w = some (.ok (v.toByteArray, w)) := by
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, eq_of_beq (sel0 hsel), hwv,
    immutable_read v hcode]

end Model

/-! ## Refinement -/

/-- The runtime bytecode followed by any word refines the model. -/
theorem feCodeScalarRefinesModel : Refines .P0 feCodeScalarBytecode Model.contract := by
  intro σ σ₀ g A I tail hcode htail _ hsize
  have htail : tail.size = 32 := htail
  rw [← toByteArray_uInt256OfByteArray_of_size32 htail] at hcode
  generalize uInt256OfByteArray tail = v at hcode
  refine RefinesFor.closed ?_
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feCodeScalarX_short hcode (by omega))
      (runtime_short (by omega)) (by simp)
  by_cases h0 : selIs I (feCodeScalarSelBytes 0)
  · by_cases hwv : I.weiValue = ⟨0⟩
    · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode
        (feCodeScalarGetRet v hcode hsize h0 hwv) (runtime_get v hcode hsz h0 hwv) rfl
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feCodeScalarGetRev hcode hsize h0 hwv) (runtime_get_value hsz h0 hwv) (by simp)
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
      (feCodeScalarX_noMatch hcode hsz hsize h0) (runtime_noMatch hsz h0) (by simp)

/-! ## Deployment -/

theorem init_value {I : ExecutionEnv} {w : World} {args : ByteArray} (out : ByteArray)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    (Model.init args >>= fun tail => pure (out ++ tail)).exec I w
      = some (.error (.revert ByteArray.empty)) := by
  simp [Model.init, nonPayable, hwv]

theorem init_ok {I : ExecutionEnv} {w : World} (out : ByteArray) (v : UInt256)
    (hwv : I.weiValue = ⟨0⟩) :
    (Model.init v.toByteArray >>= fun tail => pure (out ++ tail)).exec I w
      = some (.ok (out ++ v.toByteArray, w)) := by
  have hsz : v.toByteArray.size = 32 := toByteArray_size v
  have hword : uInt256OfByteArray (v.toByteArray.readBytes 0 32) = v := by
    rw [show v.toByteArray.readBytes 0 32 = v.toByteArray from ?_, uInt256OfByteArray_toByteArray]
    apply ByteArray.ext
    apply Array.ext'
    rw [readBytes_at_toList_any _ 0 (by omega), List.drop_zero]
    exact List.take_of_length_le (by rw [Array.length_toList]; exact Nat.le_of_eq hsz)
  simp [Model.init, nonPayable, hwv, hsz, hword]

/-- Deployment with one ABI-encoded `uint256` argument: the deployed code is the runtime
    bytecode followed by the argument word, and no account changes. -/
theorem feCodeScalarDeployRefinesModel :
    RefinesDeploy .P0 feCodeScalarCreationBytecode feCodeScalarBytecode Model.contract
      (fun args => ∃ v : UInt256, args = v.toByteArray) := by
  refine RefinesDeploy.closed ?_
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode _ _
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode (feCodeScalarCtorRet v hcode hwv)
      (init_ok _ v hwv) rfl
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feCodeScalarCtorRev hcode hwv)
      (init_value _ hwv) (by simp)

/-- The tail the constructor returns has the size the runtime certificate assumes. -/
theorem init_tail_size {I : ExecutionEnv} {w w' : World} {args tail : ByteArray}
    (h : (Model.contract.init args).exec I w = some (.ok (tail, w'))) :
    tail.size = Model.contract.immutables := by
  by_cases hwv : I.weiValue = ⟨0⟩ <;> by_cases hsz : args.size < 32 <;>
    simp [Model.contract, Model.init, nonPayable, hwv, hsz] at h
  rw [← h.1]
  exact toByteArray_size _

end FeProofs.CodeScalar
