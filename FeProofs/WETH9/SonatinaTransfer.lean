import FeProofs.WETH9.SonatinaTransferFromRun

/-!
# FeWETH9's `transfer` and `transferFrom` arms, against the machine IR

Both call Fe's `transfer_from`, which the machine IR keeps as the function `%transfer_from`
(`tfOut`).  Each arm splits on the cases `tfOut` distinguishes: a short balance, the caller as
the source, an allowance of the largest word, a short allowance, and write permission.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) {I : ExecutionEnv} (w : World)

attribute [local simp] Exported.recv0_arm3_entry Exported.recv0_arm3 Exported.recv0_arm8_entry
  Exported.recv0_arm8 Exported.transfer_from_Weth9Store_Evm_Evm Exported.balanceOfField
  Exported.allowanceField Exported.ne_Address_Address Exported.Address_eq Exported.u256_max
  Place.storage store load sload entry exec_nonPayable exec_sstore M.exec_ite

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

/-- The largest word, as the machine IR compares an allowance with it. -/
local notation "maxNat" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- The calldata word at `n`, as the machine IR loads it. -/
local notation "cdw" n => uInt256OfByteArray (I.calldata.readBytes n 32)

set_option hygiene false in
/-- Close one case of `tfOut`: the exported arm by `simp` and the machine IR's rest by `ir_simp`,
    under the case's facts. -/
local macro "tf_case" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try simp (maxSteps := 4000000) (disch := room) [FeProofs.Lib.locateAddress_exec,
    FeProofs.Lib.locateAddressMap_exec, Exported.Evm_caller, Exported.emitTransferLit_exec,
    FeProofs.Lib.returnBool_exec, $ls,*])
  (try ir_simp [$ls,*])
  first | exact .stop_stop rfl rfl rfl | exact .panic_revert 1 | exact .exit _))

set_option hygiene false in
/-- The shared prefix of a `transfer_from` arm: the exported arm by `simp` up to the cases, the
    machine IR by `ir_step` through the call, with `%transfer_from`'s lemma. -/
local macro "tf_prefix" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (maxSteps := 4000000) (disch := room) [hwv, hdec, hshort, hna,
    FeProofs.Lib.locateAddress_exec, FeProofs.Lib.locateAddressMap_exec, Exported.Evm_caller,
    Exported.emitTransferLit_exec, FeProofs.Lib.returnBool_exec, $ls,*]
  repeat ir_step [tfOut, $ls,*]))

variable (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 8000000 in
/-- `transferFrom(address,address,uint256)`. -/
theorem arm_transferFrom (htf : m.func? "transfer_from" = some transferFromFunc)
    (hmem : w.memory.size + 1024 < UInt256.size) (M : ByteArray) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm3_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 18).exec I { w with memory := M })) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeTransferFrom_exec I w.reserved hsz hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 100
  · have hlt : (I.calldata.size : Int) - 4 < 96 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 96 := by omega
  by_cases hna : NotAddress (Fe.EVM.word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  have ha : (Fe.EVM.word I.calldata 4).toNat >>> 160 = 0 := by
    by_contra h; exact hna ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at ha
  by_cases hnb : NotAddress (Fe.EVM.word I.calldata 36)
  · have hb := (notAddress_iff _).mp hnb
    simp only [Fe.EVM.word] at hb
    simp [hwv, hdec, hshort, hna, hnb]
    repeat ir_step
    exact .exit _
  have hb : (Fe.EVM.word I.calldata 36).toNat >>> 160 = 0 := by
    by_contra h; exact hnb ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at hb
  simp only [Fe.EVM.word] at hdec hna hnb ⊢
  tf_prefix [hnb, transferFrom_eq ic I _ htf]
  by_cases hbal : (slotWord I w.accounts (mapSlot (cdw 4) (UInt256.ofNat 3))).toNat <
      (cdw 68).toNat
  · tf_case [hbal, Nat.not_le.mpr hbal]
  have hbal' := Nat.not_lt.mp hbal
  by_cases hs : (cdw 4) = callerWord I
  · have hsN : (cdw 4).toNat = (I.source : Nat) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      rw [hs]; simp [callerWord, Check.toNat_ofNat, UInt256.size]
    have hsE := eq_true hs
    by_cases hp : I.perm = true
    · tf_case [hbal, hbal', hsE, hsN, hp]
    · tf_case [hbal, hbal', hsE, hsN, hp]
  have hsN : ¬ (cdw 4).toNat = (I.source : Nat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [callerWord, Check.toNat_ofNat, UInt256.size] using fun h => hs (Check.eq_of_toNat h)
  by_cases hm : (slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot (cdw 4) (UInt256.ofNat 4)))).toNat = maxNat
  · have hmU : slotWord I w.accounts (mapSlot (callerWord I) (mapSlot (cdw 4) (UInt256.ofNat 4)))
        = UInt256.ofNat maxNat := Check.eq_of_toNat (by rw [hm]; rfl)
    by_cases hp : I.perm = true
    · tf_case [hbal, hbal', hs, hsN, hm, hmU, hp]
    · tf_case [hbal, hbal', hs, hsN, hm, hmU, hp]
  have hmU : ¬ slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot (cdw 4) (UInt256.ofNat 4))) = UInt256.ofNat maxNat :=
    fun h => hm (by rw [h]; rfl)
  by_cases hal : (slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot (cdw 4) (UInt256.ofNat 4)))).toNat < (cdw 68).toNat
  · tf_case [hbal, hbal', hs, hsN, hm, hmU, hal, Nat.not_le.mpr hal]
  have hal' := Nat.not_lt.mp hal
  by_cases hp : I.perm = true
  · tf_case [hbal, hbal', hs, hsN, hm, hmU, hal, hal', hp]
  · tf_case [hbal, hbal', hs, hsN, hm, hmU, hal, hal', hp]

set_option maxHeartbeats 8000000 in
/-- `transfer(address,uint256)`: `transfer_from` from the caller. -/
theorem arm_transfer (htf : m.func? "transfer_from" = some transferFromFunc)
    (hmem : w.memory.size + 1024 < UInt256.size) (M : ByteArray) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm8_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 52).exec I { w with memory := M })) := by
  have hr : w.reserved.memory.size + 1024 < UInt256.size :=
    reserveMemory_room hmem (by decide)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeTransfer_exec I w.reserved hsz hfits
  -- `%transfer_from`'s lemma at the caller's word, as the machine IR passes it.
  have htr := fun w' dst wad => transferFrom_eq ic I w' htf (callerWord I) dst wad
  simp only [callerWord, Check.toNat_ofNat, UInt256.size] at htr
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 68
  · have hlt : (I.calldata.size : Int) - 4 < 64 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 64 := by omega
  by_cases hna : NotAddress (Fe.EVM.word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  have ha : (Fe.EVM.word I.calldata 4).toNat >>> 160 = 0 := by
    by_contra h; exact hna ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at ha hdec hna ⊢
  tf_prefix [htr]
  by_cases hbal : (slotWord I w.accounts (mapSlot (callerWord I) (UInt256.ofNat 3))).toNat <
      (cdw 36).toNat
  · tf_case [hbal, Nat.not_le.mpr hbal]
  have hbal' := Nat.not_lt.mp hbal
  by_cases hp : I.perm = true
  · tf_case [hbal, hbal', hp]
  · tf_case [hbal, hbal', hp]

end FeProofs.WETH9.Sonatina
