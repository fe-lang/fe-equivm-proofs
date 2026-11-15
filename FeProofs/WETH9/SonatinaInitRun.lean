import FeProofs.WETH9.SonatinaLoad

/-!
# FeWETH9's constructor callees, run

The init section's `%revert_error` (its arena at 192), `%stored_len`, and `%store slot ptr len`,
which stores a string shorter than a word, read from memory at `ptr`, at `slot`: it checks the
old head with `%stored_len`, stores the new head, and zeroes the old value's data words, a loop
of as many iterations as the old head says (`clear_run`).
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Reasoning.Theory
open Stele (solidityDecodeBytesLengthHeader solidityBytesDataBaseSlot solidityShortBytesWord)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The init section's `%revert_error c`: `Panic(c)`, its payload stored in the arena at 192. -/
theorem initRevertError_run (hf : m.func? "revert_error" = some initRevertErrorFunc) {c : Nat}
    (hc : c < 2 ^ 256) :
    (runFunc m ic "revert_error" [Val.int 256 c]).exec I w =
      some (.error (.revert (panicData c))) := by
  have hc' : c % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = c := Nat.mod_eq_of_lt hc
  rw [runFunc_entry hf rfl]
  simp [Fe.Sonatina.bind]
  ir_step [panic_read_gap, hc']

open Stele (solidityDecodeBytesLengthHeader) in
/-- The init section's `%stored_len head`, the runtime's: the length a string head encodes, as Stele decodes it, or
    `Panic(0x22)` when the length contradicts the short/long flag. -/
theorem initStoredLen_run (hf : m.func? "stored_len" = some initStoredLenFunc)
    (hr : m.func? "revert_error" = some initRevertErrorFunc) (head : UInt256) :
    (runFunc m ic "stored_len" [Val.int 256 head.toNat]).exec I w =
      match solidityDecodeBytesLengthHeader head with
      | .ok L => some (.ok ([Val.int 256 L], w))
      | _ => some (.error (.revert (panicData 0x22))) := by
  have hh := head.val.isLt
  change head.toNat < 2 ^ 256 at hh
  have e1 : head.toNat &&& 1 = head.toNat % 2 := Nat.and_one_is_mod _
  have e2 : head.toNat &&& 255 = head.toNat % 256 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  have e3 : ∀ x : Nat, x >>> 1 = x / 2 := fun x => by rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hm2 : head.toNat % 256 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 := Nat.mod_eq_of_lt (by omega)
  rw [runFunc_entry hf rfl]
  simp [Fe.Sonatina.bind]
  rcases decodeHeader_cases head with ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨hbad, hrev⟩
  · rw [hok]
    have : ¬ head.toNat / 2 < 32 := by omega
    have hm : head.toNat / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat / 2 := Nat.mod_eq_of_lt (by omega)
    repeat ir_step [e1, e2, e3, ho, this, hm]
  · rw [hok]
    have hm : head.toNat % 256 / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 / 2 := Nat.mod_eq_of_lt (by omega)
    repeat ir_step [e1, e2, e3, he, hlt, hm, hm2]
  · rw [hrev]
    rcases hbad with ⟨ho, hlt⟩ | ⟨he, hge⟩
    · have hm : head.toNat / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      repeat ir_step [e1, e2, e3, ho, hlt, hm, initRevertError_run ic I _ hr (c := 34) (by decide)]
    · have hm : head.toNat % 256 / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 / 2 := Nat.mod_eq_of_lt (by omega)
      have : ¬ head.toNat % 256 / 2 < 32 := by omega
      repeat ir_step [e1, e2, e3, he, this, hm, hm2, initRevertError_run ic I _ hr (c := 34) (by decide)]


theorem one_add_ofNat {i : Nat} (hi : i + 1 < UInt256.size) :
    (⟨1⟩ : UInt256) + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
  rw [u256_add_comm]; exact lit_add_eq (a := i) (b := 1) hi

set_option maxHeartbeats 4000000 in
/-- `%store`'s loop zeroing the `n` data words of a long old value, from its header (block 20)
    entered again from block 19 before word `i`: it ends as `clearDataWordsForwardFrom` from word
    `i`.  The loop is a `do … while`, so its last iteration exits from the header's own block. -/
theorem clear_run (slot : UInt256) (n : Nat) (hn : n < 2 ^ 251) (hperm : I.perm = true)
    (A0 : AccountMap) :
    ∀ i (E : Sonatina.Env) (A : AccountMap), i < n → E[56]? = some (Val.int 256 i) →
      E[3]? = some (Val.int 256 n) →
      E[53]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat) →
      clearDataWordsForwardFrom I.codeOwner A (solidityBytesDataBaseSlot slot) (UInt256.ofNat i)
        (n - i) = A0 →
      (runBlocks m ic initStoreFunc E (some 19) 20).exec I { w with accounts := A } =
        some (.ok ([], { w with accounts := A0 })) := by
  intro i E A hi h56 h3 h53 hA
  refine runBlocks_loop (n := n - 1) (fun i E w' => ∃ A, w' = { w with accounts := A } ∧
      E[56]? = some (Val.int 256 i) ∧ E[3]? = some (Val.int 256 n) ∧
      E[53]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat) ∧
      clearDataWordsForwardFrom I.codeOwner A (solidityBytesDataBaseSlot slot) (UInt256.ofNat i)
        (n - i) = A0) ?_ ?_ i E _ (by omega) ⟨A, rfl, h56, h3, h53, hA⟩
  · rintro i E w' hi ⟨A, rfl, h56, h3, h53, hA⟩ K hK
    have hadd := ofNat_toNat_add (solidityBytesDataBaseSlot slot) (i := i) (by omega)
    ir_step_nat [hadd]
    ir_step_nat
    refine hK _ _ ⟨_, rfl, by simp only [Std.TreeMap.getElem?_insert]; simp,
      by simp only [Std.TreeMap.getElem?_insert]; simp [h3],
      by simp only [Std.TreeMap.getElem?_insert]; simp [h53], ?_⟩
    rw [← hA, show n - i = (n - (i + 1)) + 1 by omega, clearDataWordsForwardFrom,
      one_add_ofNat (by unfold UInt256.size; omega)]
    rfl
  · rintro E w' ⟨A, rfl, h56, h3, h53, hA⟩
    have hadd := ofNat_toNat_add (solidityBytesDataBaseSlot slot) (i := n - 1) (by omega)
    repeat ir_step_nat [hadd]
    rw [← hA, show n - (n - 1) = 0 + 1 by omega, clearDataWordsForwardFrom]
    rfl

theorem leadWord_idem (v : UInt256) (r : Nat) : leadWord (leadWord v r) r = leadWord v r := by
  unfold leadWord
  split
  · exact Check.eq_of_toNat (by rw [uland_toNat, uland_toNat, Nat.and_assoc, Nat.and_self])
  · rfl

theorem ofNat_lor (a : UInt256) {n : Nat} (hn : n < UInt256.size) :
    UInt256.ofNat (a.toNat ||| n) = a ||| UInt256.ofNat n := by
  have ha := a.val.isLt
  change a.toNat < UInt256.size at ha
  apply Check.eq_of_toNat
  rw [show (a ||| UInt256.ofNat n) = UInt256.lor a (UInt256.ofNat n) from rfl,
    u256_lor_toNat_exact, Check.toNat_ofNat, Check.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have h2 : (2 : Nat) ^ 256 = UInt256.size := rfl
  exact Nat.mod_eq_of_lt (h2 ▸ Nat.or_lt_two_pow (h2 ▸ ha) (h2 ▸ hn))

/-- The memory `%store` leaves: a long old value's slot hashed in the arena at 160. -/
def storeMem (w : World) (slot head : UInt256) : ByteArray :=
  if head.toNat % 2 = 1 then slot.toByteArray.write 0 w.memory 160 32 else w.memory

open Classical in
set_option maxHeartbeats 8000000 in
/-- `%store slot ptr len` of a string of `len < 32` bytes, whose word lies at `ptr + 32`:
    `Panic(0x22)` on a bad old head, or the head stored and the old value's data words zeroed,
    as `strWriteMap` writes them. -/
theorem store_run (hf : m.func? "store" = some initStoreFunc)
    (hs : m.func? "stored_len" = some initStoredLenFunc)
    (hr : m.func? "revert_error" = some initRevertErrorFunc)
    (slot v : UInt256) (ptr len : Nat) (bytes : ByteArray) (hlen0 : 0 < len) (hlen : len < 32)
    (hptr : ptr + 64 < 2 ^ 32)
    (hv : uInt256OfByteArray (w.memory.readWithPadding (ptr + 32) 32) = v)
    (hword : leadWord v len ||| UInt256.ofNat (len * 2) = solidityShortBytesWord bytes) :
    (runFunc m ic "store" [Val.int 256 slot.toNat, Val.int 256 ptr, Val.int 256 len]).exec I w =
      if strHeadBad (slotWord I w.accounts slot) then some (.error (.revert (panicData 0x22)))
      else if I.perm then
        some (.ok ([], { w with
          accounts := strWriteMap I w.accounts slot bytes
          memory := storeMem w slot (slotWord I w.accounts slot) }))
      else some (.error .static) := by
  have hh := (slotWord I w.accounts slot).val.isLt
  change (slotWord I w.accounts slot).toNat < 2 ^ 256 at hh
  have hhead : UInt256.ofNat ((leadWord (leadWord v len) len).toNat ||| len * 2) =
      solidityShortBytesWord bytes := by
    rw [leadWord_idem, ofNat_lor _ (by unfold UInt256.size; omega), hword]
  rw [runFunc_entry hf rfl]
  rcases decodeHeader_cases (slotWord I w.accounts slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · generalize hL : (slotWord I w.accounts slot).toNat / 2 = L at hge hok
    have hL255 : L < 2 ^ 255 := by omega
    have hbad : ¬ strHeadBad (slotWord I w.accounts slot) := fun h => by
      rw [(Exported.strHeadBad_iff _).mp h] at hok; cases hok
    have hold : strOldWords (Reasoning.Reach.solcSlotWord w.accounts I slot) = (L + 31) / 32 := by
      have hf1 : UInt256.land (slotWord I w.accounts slot) ⟨1⟩ = ⟨1⟩ := headFlag_odd ho
      show strOldWords (slotWord I w.accounts slot) = _
      unfold strOldWords strHeadLen
      rw [hf1, ite_eq_right (by decide), ite_eq_right (by decide), udiv_toNat, ← hL]
      rfl
    have hbs : UInt256.ofNat (fromByteArrayBigEndian (KEC slot.toByteArray)) =
        solidityBytesDataBaseSlot slot := keccakSlot_eq _
    have hbs' : fromByteArrayBigEndian (KEC slot.toByteArray) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        (solidityBytesDataBaseSlot slot).toNat := by rw [← hbs]; rfl
    rw [ite_eq_right hbad, storeMem, ite_eq_left ho]
    simp [Fe.Sonatina.bind]
    ir_step_nat [initStoredLen_run ic I _ hs hr, hok]
    ir_step_nat [Nat.and_one_is_mod, ho]
    ir_step_nat
    ir_step_nat
    ir_step_nat
    by_cases hperm : I.perm = true
    swap
    · ir_step_nat [mask_leadWord _ _ hlen]
    ir_step_nat [mask_leadWord _ _ hlen]
    ir_step_nat
    ir_step_nat [word_read_gap]
    ir_step_nat
    have h0 : ∀ b : UInt256, b + (⟨0⟩ : UInt256) = b := fun b => Fe.EVM.add_zero b
    by_cases hW1 : 1 < (L + 31) / 32
    · ir_step_nat
      obtain ⟨k, hk⟩ : ∃ k, (L + 31) / 32 = k + 1 := ⟨(L + 31) / 32 - 1, by omega⟩
      exact clear_run ic I { w with memory := slot.toByteArray.write 0 w.memory 160 32 } slot
        ((L + 31) / 32) (by omega) hperm _ 1 _ _ (by omega)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [strWriteMap]; rw [hold, hk, Nat.add_sub_cancel, clearDataWordsForwardFrom, h0,
              show (⟨1⟩ : UInt256) + ⟨0⟩ = UInt256.ofNat 1 by decide]; rfl)
    · ir_step_nat
      ir_step_nat
      simp only [strWriteMap]
      rw [hold, show (L + 31) / 32 = 0 + 1 by omega, clearDataWordsForwardFrom,
        clearDataWordsForwardFrom, h0]
      rfl
  · generalize hL : (slotWord I w.accounts slot).toNat % 256 / 2 = L at hlt hok
    have hbad : ¬ strHeadBad (slotWord I w.accounts slot) := fun h => by
      rw [(Exported.strHeadBad_iff _).mp h] at hok; cases hok
    have hold : strOldWords (Reasoning.Reach.solcSlotWord w.accounts I slot) = 0 := by
      have hf0 : UInt256.land (slotWord I w.accounts slot) ⟨1⟩ = ⟨0⟩ := headFlag_even he
      show strOldWords (slotWord I w.accounts slot) = _
      unfold strOldWords
      rw [ite_eq_left hf0]
    rw [ite_eq_right hbad, storeMem,
      ite_eq_right (show ¬ (slotWord I w.accounts slot).toNat % 2 = 1 by omega)]
    simp [Fe.Sonatina.bind]
    ir_step_nat [initStoredLen_run ic I _ hs hr, hok]
    ir_step_nat [Nat.and_one_is_mod, he]
    ir_step_nat
    ir_step_nat
    ir_step_nat
    by_cases hperm : I.perm = true
    swap
    · ir_step_nat [mask_leadWord _ _ hlen]
    ir_step_nat [mask_leadWord _ _ hlen]
    ir_step_nat
    ir_step_nat
    ir_step_nat
    try simp only [strWriteMap, hold, clearDataWordsForwardFrom]
    rfl
  · have hbad : strHeadBad (slotWord I w.accounts slot) := (Exported.strHeadBad_iff _).mpr hrev
    rw [ite_eq_left hbad]
    simp [Fe.Sonatina.bind]
    ir_step_nat [initStoredLen_run ic I _ hs hr, hrev]

open Classical in
/-- `store_run` as a rewrite for `ir_step` at a call site whose memory holds the string's word,
    its side conditions for `simp` to discharge. -/
theorem store_eq (hf : m.func? "store" = some initStoreFunc)
    (hs : m.func? "stored_len" = some initStoredLenFunc)
    (hr : m.func? "revert_error" = some initRevertErrorFunc) (s : Nat) (bytes : ByteArray)
    {w : World} {ptr len : Nat} (hslot : s < 2 ^ 256) (hlen0 : 0 < len) (hlen : len < 32)
    (hptr : ptr + 64 < 2 ^ 32)
    (hword : leadWord (uInt256OfByteArray (w.memory.readWithPadding (ptr + 32) 32)) len |||
      UInt256.ofNat (len * 2) = solidityShortBytesWord bytes) :
    (runFunc m ic "store" [Val.int 256 s, Val.int 256 ptr, Val.int 256 len]).exec I w =
      if strHeadBad (slotWord I w.accounts (UInt256.ofNat s)) then
        some (.error (.revert (panicData 0x22)))
      else if I.perm then
        some (.ok ([], { w with
          accounts := strWriteMap I w.accounts (UInt256.ofNat s) bytes
          memory := storeMem w (UInt256.ofNat s) (slotWord I w.accounts (UInt256.ofNat s)) }))
      else some (.error .static) := by
  have h := store_run ic I w hf hs hr (UInt256.ofNat s) _ ptr len bytes hlen0 hlen hptr rfl hword
  rwa [show (UInt256.ofNat s).toNat = s from lit_toNat hslot] at h

end FeProofs.WETH9.Sonatina
