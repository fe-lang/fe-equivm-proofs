import FeProofs.ScalarStore.Correct
import FeProofs.ScalarStore.Model
import Fe.EVM.Reach

/-!
# FeScalarStore: the bytecode refines the model

The EVM half restates the traces of `Get.lean`, `Set.lean` and `Constructor.lean` as terminals
that mention the bytecode only.  The model half is evaluation of `Model.runtime` and `Model.init`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.ScalarStore

set_option maxRecDepth 2000000

/-! ## What the bytecode does -/

theorem feScalarStoreGetRet {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 1)) (hwv : I.weiValue = ⟨0⟩) :
    RDret feScalarStoreBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (solcSlotWordAt ⟨0⟩ σ I)) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 1) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachGetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back ByteArray.empty _ 0 (by decide)] at rd
  exact rd

theorem feScalarStoreGetRev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 1)) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feScalarStoreBytecode g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 1) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachGetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
  exact rd

theorem feScalarStoreSetRevValue {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev feScalarStoreBytecode g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachSetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
  exact rd

theorem feScalarStoreSetRevHead {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev feScalarStoreBytecode g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachSetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
  exact rd

theorem feScalarStoreSetRet {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true) :
    RDret feScalarStoreBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ (calldataWord I.calldata 4)) ByteArray.empty := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachSetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd to 59 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  rd_step rd
  have hout : ByteArray.empty.readWithPadding (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat
      = ByteArray.empty := byteArray_readWithPadding_zero _ _
  rw [hout] at rd
  exact rd

theorem feScalarStoreSetStatic {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = feScalarStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = false) :
    RDstatic feScalarStoreBytecode g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feScalarStoreSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feScalarStoreReachSetBody (g := g) (σ := σ) (σ₀ := σ₀) (A := A)
    hcode hsz hsize hsel
  rd_run rd to 59 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hperm' : ¬ I.perm = true := by simp [hperm]
  rd_step rd
  exact rd

/-! ## What the model does -/

section Model

variable {I : ExecutionEnv} {w : World}

theorem sel0 (h : selIs I (feScalarStoreSelBytes 0)) :
    (Model.setSelector == I.calldata.extract 0 4) = true := h

theorem sel0_not (h : ¬ selIs I (feScalarStoreSelBytes 0)) :
    (Model.setSelector == I.calldata.extract 0 4) = false := by
  simpa [selIs, Model.setSelector, feScalarStoreSelBytes] using h

theorem sel1 (h : selIs I (feScalarStoreSelBytes 1)) :
    (Model.getSelector == I.calldata.extract 0 4) = true := h

theorem sel1_not (h : ¬ selIs I (feScalarStoreSelBytes 1)) :
    (Model.getSelector == I.calldata.extract 0 4) = false := by
  simpa [selIs, Model.getSelector, feScalarStoreSelBytes] using h

theorem runtime_short (h : I.calldata.size < 4) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, h]

theorem runtime_noMatch (hsz : 4 ≤ I.calldata.size)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (h1 : ¬ selIs I (feScalarStoreSelBytes 1)) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, Nat.not_lt.mpr hsz, sel0_not h0, sel1_not h1]

theorem runtime_set_value (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue ≠ ⟨0⟩) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, sel0 hsel, hwv]

theorem runtime_set_head (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hbad : BadHead I.calldata 1) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, sel0 hsel, hwv, hbad]

theorem runtime_set (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hok : ¬ BadHead I.calldata 1) (hperm : I.perm = true) :
    Model.runtime.exec I w = some (.ok (ByteArray.empty,
      { w with accounts := storeWord I.codeOwner w.accounts ⟨0⟩ (calldataWord I.calldata 4) })) := by
  simp [Model.runtime, Model.set, Model.storedSlot, calldata, nonPayable, sstore,
    Nat.not_lt.mpr hsz, sel0 hsel, hwv, hok, hperm]

theorem runtime_set_static (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (feScalarStoreSelBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hok : ¬ BadHead I.calldata 1) (hperm : I.perm = false) :
    Model.runtime.exec I w = some (.error .static) := by
  simp [Model.runtime, Model.set, calldata, nonPayable, sstore, Nat.not_lt.mpr hsz, sel0 hsel,
    hwv, hok, hperm]

theorem runtime_get_value (hsz : 4 ≤ I.calldata.size)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (hsel : selIs I (feScalarStoreSelBytes 1))
    (hwv : I.weiValue ≠ ⟨0⟩) :
    Model.runtime.exec I w = some (.error (.revert ByteArray.empty)) := by
  simp [Model.runtime, calldata, nonPayable, Nat.not_lt.mpr hsz, sel0_not h0, sel1 hsel, hwv]

theorem runtime_get (hsz : 4 ≤ I.calldata.size)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (hsel : selIs I (feScalarStoreSelBytes 1))
    (hwv : I.weiValue = ⟨0⟩) :
    Model.runtime.exec I w
      = some (.ok (UInt256.toByteArray (solcSlotWordAt ⟨0⟩ w.accounts I), w)) := by
  simp [Model.runtime, Model.get, Model.storedSlot, calldata, nonPayable, sload,
    Nat.not_lt.mpr hsz, sel0_not h0, sel1 hsel, hwv, solcSlotWordAt, solcSlotWord]

end Model

/-! ## Refinement -/

theorem feScalarStoreRefinesModel : Refines .P0 feScalarStoreBytecode Model.contract := by
  intro σ σ₀ g A I hcode hsize
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feScalarStoreX_short hcode (by omega))
      (runtime_short (by omega)) (by simp)
  by_cases h0 : selIs I (feScalarStoreSelBytes 0)
  · by_cases hwv : I.weiValue = ⟨0⟩
    swap
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feScalarStoreSetRevValue hcode hsize h0 hwv) (runtime_set_value hsz h0 hwv) (by simp)
    by_cases hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feScalarStoreSetRevHead hcode hsize h0 hwv hbad) (runtime_set_head hsz h0 hwv (by simpa [BadHead] using hbad))
        (by simp)
    have hlen : 36 ≤ I.calldata.size := by omega
    have hhi : I.calldata.size < 2 ^ 255 + 4 := by omega
    by_cases hperm : I.perm = true
    · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode
        (feScalarStoreSetRet hcode hsize h0 hwv hlen hhi hperm)
        (runtime_set hsz h0 hwv (by simpa [BadHead] using hbad) hperm) rfl
    · have hpf : I.perm = false := by simpa using hperm
      exact agrees_of_static (g := Sat256.ofUInt256 g) hcode
        (feScalarStoreSetStatic hcode hsize h0 hwv hlen hhi hpf)
        (runtime_set_static hsz h0 hwv (by simpa [BadHead] using hbad) hpf)
  · by_cases h1 : selIs I (feScalarStoreSelBytes 1)
    · by_cases hwv : I.weiValue = ⟨0⟩
      · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode
          (feScalarStoreGetRet hcode hsize h1 hwv) (runtime_get hsz h0 h1 hwv) rfl
      · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
          (feScalarStoreGetRev hcode hsize h1 hwv) (runtime_get_value hsz h0 h1 hwv) (by simp)
    · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
        (feScalarStoreX_noMatch hcode hsz hsize (feScalarStoreNoSelectorMatches h0 h1))
        (runtime_noMatch hsz h0 h1) (by simp)

/-! ## Deployment -/

/-- Reading all 32 bytes of a 32-byte array returns it. -/
theorem readBytes_all32 (b : ByteArray) (h : b.size = 32) : b.readBytes 0 32 = b := by
  apply ByteArray.ext
  apply Array.ext'
  rw [readBytes_at_toList_any b 0 (by omega), List.drop_zero]
  exact List.take_of_length_le (by rw [Array.length_toList]; exact Nat.le_of_eq h)

theorem init_value {I : ExecutionEnv} {w : World} {args : ByteArray} (hwv : I.weiValue ≠ ⟨0⟩) :
    (Model.contract.init args >>= fun _ => pure feScalarStoreBytecode).exec I w
      = some (.error (.revert ByteArray.empty)) := by
  simp [Model.contract, Model.init, nonPayable, hwv]

theorem init_ok {I : ExecutionEnv} {w : World} (v : UInt256) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) :
    (Model.contract.init (ctorTail v) >>= fun _ => pure feScalarStoreBytecode).exec I w
      = some (.ok (feScalarStoreBytecode,
          { w with accounts := storeWord I.codeOwner w.accounts ⟨0⟩ v })) := by
  have hsz : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hword : uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v := by
    rw [readBytes_all32 _ hsz, ctorTail, word_toBytesBE_toByteArray_eq_toByteArray,
      uInt256OfByteArray_toByteArray]
  simp [Model.contract, Model.init, Model.initBody, Model.storedSlot, nonPayable, sstore, hwv,
    hperm, hsz, hword]

/-- Deployment with one ABI-encoded `uint256` argument. -/
theorem feScalarStoreDeployRefinesModel :
    RefinesDeploy .P0 feScalarStoreCreationBytecode feScalarStoreBytecode Model.contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode (feScalarStoreCtorRet v hcode hwv hperm)
      (init_ok v hwv hperm) rfl
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feScalarStoreCtorRev hcode hwv)
      (init_value hwv) (by simp)

end FeProofs.ScalarStore
