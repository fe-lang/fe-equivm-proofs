import FeProofs.PackedStore.Correct
import FeProofs.PackedStore.ExportedCorrect
import Fe.EVM.Reach

/-!
# FePackedStore: the bytecode refines the exported arms

`handContract` runs the exporter's arm bodies `recv0_arm0` to `recv0_arm4` and its `init`
(`Exported.lean`).  The entry code around them (selector dispatch, call-value and calldata
checks, argument decoding, result encoding) is written by hand.

One theorem per arm: on calldata with that arm's selector, the bytecode runs out of gas or agrees
with the arm.  The EVM half of each replays the traces of the Stele proofs as terminals that
mention the bytecode only; the model half evaluates the arm with the `…_exec` theorems.  The word
the exported arms read and write, `wordSlot = mapSlot 0 0`, is the bytecode's `packedSlot`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.PackedStore.Exported

set_option maxRecDepth 2000000

/-! ## Entry code -/

/-- `sol("get0()")` -/
def get0Selector : ByteArray := ⟨#[0x90, 0xbb, 0x7b, 0x44]⟩

/-- `sol("get1()")` -/
def get1Selector : ByteArray := ⟨#[0x05, 0x4c, 0x1a, 0x75]⟩

/-- `sol("set0(uint256)")` -/
def set0Selector : ByteArray := ⟨#[0xf2, 0x6f, 0xee, 0xc9]⟩

/-- `sol("set1(uint256)")` -/
def set1Selector : ByteArray := ⟨#[0x9b, 0xc3, 0x9d, 0x3c]⟩

/-- `sol("setBoth(uint256,uint256)")` -/
def setBothSelector : ByteArray := ⟨#[0x92, 0xcf, 0x1e, 0xf5]⟩

def get0Arm : FeM ByteArray := do
  nonPayable
  return (← recv0_arm0).toByteArray

def get1Arm : FeM ByteArray := do
  nonPayable
  return (← recv0_arm1).toByteArray

def set0Arm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  recv0_arm2 (word cd 4)
  return ByteArray.empty

def set1Arm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  recv0_arm3 (word cd 4)
  return ByteArray.empty

def setBothArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  recv0_arm4 (word cd 4) (word cd 36)
  return ByteArray.empty

/-- The runtime entry, written by hand: match the selector and run its arm.  Calldata with no selector, or with
    one no arm declares, reverts with no data. -/
def handRuntime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then M.revert ByteArray.empty
  else if get0Selector == cd.extract 0 4 then get0Arm
  else if get1Selector == cd.extract 0 4 then get1Arm
  else if set0Selector == cd.extract 0 4 then set0Arm cd
  else if set1Selector == cd.extract 0 4 then set1Arm cd
  else if setBothSelector == cd.extract 0 4 then setBothArm cd
  else M.revert ByteArray.empty

/-- Deployment rejects call value, then runs `init`.  The contract takes no arguments. -/
def initEntry (_args : ByteArray) : FeM Unit := do
  nonPayable
  init

def handContract : ContractModel :=
  { init := fun args => initEntry args >>= fun _ => pure ByteArray.empty, runtime := handRuntime }

/-! ## The arms -/

variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}

/-- The model starts with empty memory, so every lookup of an arm has room for its buffer. -/
theorem init_room (σ : AccountMap) (A : Substate) :
    (World.init σ A).memory.size + 128 < UInt256.size := by
  simp [World.init, UInt256.size]

/-- What an arm must show: out of gas, or agreement with its model. -/
abbrev ArmAgrees (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (arm : FeM ByteArray) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g A I) (arm.exec I (World.init σ A))

theorem get0Arm_refines {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 1)) :
    ArmAgrees σ σ₀ g A I get0Arm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 1) rfl hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachGet0Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [get0Arm, exec_nonPayable, hwv]) (by simp)
  rd_run rd using [hwv]
  rw [keccak_packedSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _), packedByte_lane0] at rd
  exact agrees_of_ret hcode rd (w' := afterLookup (World.init σ A))
    (by simp [get0Arm, exec_nonPayable, hwv,
      get0_exec I (World.init σ A) (by have := init_room σ A; omega)]; rfl) rfl

theorem get1Arm_refines {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 0)) :
    ArmAgrees σ σ₀ g A I get1Arm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachGet1Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [get1Arm, exec_nonPayable, hwv]) (by simp)
  rd_run rd using [hwv]
  rw [keccak_packedSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _), packedByte_lane1] at rd
  exact agrees_of_ret hcode rd (w' := afterLookup (World.init σ A))
    (by simp [get1Arm, exec_nonPayable, hwv,
      get1_exec I (World.init σ A) (by have := init_room σ A; omega)]; rfl) rfl

theorem set0Arm_refines {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 4)) :
    ArmAgrees σ σ₀ g A I (set0Arm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 4) rfl hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSet0Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [set0Arm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [set0Arm, exec_nonPayable, hwv, show BadHead I.calldata 1 from hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead : ¬ BadHead I.calldata 1 := by unfold BadHead; omega
  rd_run rd to 205 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  by_cases hperm : I.perm = true
  · rd_step rd
    rw [keccak_packedSlot] at rd
    exact agrees_of_ret hcode (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _))
      (w' := { afterLookup (World.init σ A) with
        accounts := setLane I σ 0 (word I.calldata 4) })
      (by simp [set0Arm, exec_nonPayable, hwv, hhead,
        set0_exec I (World.init σ A) _ (by have := init_room σ A; omega), hperm]; rfl)
      (by simp only [setLane, setPackedByte_lane0]; rfl)
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact agrees_of_static hcode rd
      (by simp [set0Arm, exec_nonPayable, hwv, hhead,
        set0_exec I (World.init σ A) _ (by have := init_room σ A; omega), hpf])

theorem set1Arm_refines {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 3)) :
    ArmAgrees σ σ₀ g A I (set1Arm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 3) rfl hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSet1Body (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [set1Arm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [set1Arm, exec_nonPayable, hwv, show BadHead I.calldata 1 from hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead : ¬ BadHead I.calldata 1 := by unfold BadHead; omega
  rd_run rd to 155 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  by_cases hperm : I.perm = true
  · rd_step rd
    rw [keccak_packedSlot] at rd
    exact agrees_of_ret hcode (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _))
      (w' := { afterLookup (World.init σ A) with
        accounts := setLane I σ 1 (word I.calldata 4) })
      (by simp [set1Arm, exec_nonPayable, hwv, hhead,
        set1_exec I (World.init σ A) _ (by have := init_room σ A; omega), hperm]; rfl)
      (by simp only [setLane, setPackedByte_lane1]; rfl)
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact agrees_of_static hcode rd
      (by simp [set1Arm, exec_nonPayable, hwv, hhead,
        set1_exec I (World.init σ A) _ (by have := init_room σ A; omega), hpf])

theorem setBothArm_refines {g : UInt256}
    (hcode : I.code = fePackedStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (fePackedStoreSelBytes 2)) :
    ArmAgrees σ σ₀ g A I (setBothArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (fePackedStoreSelBytes 2) rfl hsel
  obtain ⟨k, C, rd⟩ := fePackedStoreReachSetBothBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [setBothArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [setBothArm, exec_nonPayable, hwv, show BadHead I.calldata 2 from hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead : ¬ BadHead I.calldata 2 := by unfold BadHead; omega
  rd_run rd to 79 using [hwv, solcDecodeLenCheckOk_4_64 hlen hhi hsize]
  by_cases hperm : I.perm = true
  · rd_step rd
    simp only [keccak_packedSlot] at rd
    exact agrees_of_ret hcode (RDret.of_output_eq rd (byteArray_readWithPadding_zero _ _))
      (w' := { afterLookup (afterLookup (World.init σ A)) with
        accounts := setLane I (setLane I σ 0 (word I.calldata 4)) 1 (word I.calldata 36) })
      (by simp [setBothArm, exec_nonPayable, hwv, hhead,
        setBoth_exec I (World.init σ A) _ _ (init_room σ A), hperm]; rfl)
      (by simp only [setLane, setPackedByte_lane0, setPackedByte_lane1]; rfl)
  · have hpf : I.perm = false := by simpa using hperm
    rd_step rd
    exact agrees_of_static hcode rd
      (by simp [setBothArm, exec_nonPayable, hwv, hhead,
        setBoth_exec I (World.init σ A) _ _ (init_room σ A), hpf])

/-! ## Refinement -/

/-- The runtime bytecode refines the contract built from the exported arms and the hand-written
    entry. -/
theorem fePackedStoreRefinesHandEntry : Refines .P0 fePackedStoreBytecode handContract := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode _ hsize
  refine RefinesFor.closed ?_
  show ArmAgrees σ σ₀ g A I handRuntime
  have sel : ∀ i, (¬ selIs I (fePackedStoreSelBytes i)) →
      (fePackedStoreSelBytes i == I.calldata.extract 0 4) = false := fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (fePackedStoreX_short hcode (by omega))
      (f := .revert ByteArray.empty)
      (by simp [handRuntime, show I.calldata.size < 4 by omega]) (by simp)
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h1 : selIs I (fePackedStoreSelBytes 1)
  · have e : handRuntime.exec I (World.init σ A) = get0Arm.exec I (World.init σ A) := by
      simp [handRuntime, hn4, eq_of_beq (show (get0Selector == I.calldata.extract 0 4) = true from h1)]
    rw [ArmAgrees, e]; exact get0Arm_refines hcode hsize h1
  have n1 : (get0Selector == I.calldata.extract 0 4) = false := sel 1 h1
  by_cases h0 : selIs I (fePackedStoreSelBytes 0)
  · have e : handRuntime.exec I (World.init σ A) = get1Arm.exec I (World.init σ A) := by
      simp [handRuntime, hn4, ne_of_beq_false n1, eq_of_beq (show (get1Selector == I.calldata.extract 0 4) = true from h0)]
    rw [ArmAgrees, e]; exact get1Arm_refines hcode hsize h0
  have n0 : (get1Selector == I.calldata.extract 0 4) = false := sel 0 h0
  by_cases h4 : selIs I (fePackedStoreSelBytes 4)
  · have e : handRuntime.exec I (World.init σ A) = (set0Arm I.calldata).exec I (World.init σ A) := by
      simp [handRuntime, hn4, ne_of_beq_false n1, ne_of_beq_false n0, eq_of_beq (show (set0Selector == I.calldata.extract 0 4) = true from h4)]
    rw [ArmAgrees, e]; exact set0Arm_refines hcode hsize h4
  have n4 : (set0Selector == I.calldata.extract 0 4) = false := sel 4 h4
  by_cases h3 : selIs I (fePackedStoreSelBytes 3)
  · have e : handRuntime.exec I (World.init σ A) = (set1Arm I.calldata).exec I (World.init σ A) := by
      simp [handRuntime, hn4, ne_of_beq_false n1, ne_of_beq_false n0, ne_of_beq_false n4, eq_of_beq (show (set1Selector == I.calldata.extract 0 4) = true from h3)]
    rw [ArmAgrees, e]; exact set1Arm_refines hcode hsize h3
  have n3 : (set1Selector == I.calldata.extract 0 4) = false := sel 3 h3
  by_cases h2 : selIs I (fePackedStoreSelBytes 2)
  · have e : handRuntime.exec I (World.init σ A) = (setBothArm I.calldata).exec I (World.init σ A) := by
      simp [handRuntime, hn4, ne_of_beq_false n1, ne_of_beq_false n0, ne_of_beq_false n4, ne_of_beq_false n3,
        eq_of_beq (show (setBothSelector == I.calldata.extract 0 4) = true from h2)]
    rw [ArmAgrees, e]; exact setBothArm_refines hcode hsize h2
  have n2 : (setBothSelector == I.calldata.extract 0 4) = false := sel 2 h2
  exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
    (fePackedStoreX_noMatch hcode hsz hsize (fePackedStoreNoSelectorMatches h0 h1 h2 h3 h4))
    (f := .revert ByteArray.empty)
    (by simp [handRuntime, hn4, ne_of_beq_false n0, ne_of_beq_false n1, ne_of_beq_false n2, ne_of_beq_false n3, ne_of_beq_false n4]) (by simp)

/-- Deployment, with no constructor arguments, refines the handContract's `init`. -/
theorem fePackedStoreDeployRefinesHandEntry :
    RefinesDeploy .P0 fePackedStoreCreationBytecode fePackedStoreBytecode handContract
      (· = ByteArray.empty) := by
  refine RefinesDeploy.of_unit_closed (init := initEntry) (fun _ => rfl) ?_
  intro σ σ₀ g A I args hargs hcode _ _
  subst hargs
  rw [ByteArray.append_empty] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode (fePackedStoreCtorRet hcode hwv)
      (w' := World.init σ A) (by simp [initEntry, init, exec_nonPayable, hwv]) rfl
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (fePackedStoreCtorRev hcode hwv)
      (f := .revert ByteArray.empty) (by simp [initEntry, exec_nonPayable, hwv])
      (by simp)

end FeProofs.PackedStore.Exported
