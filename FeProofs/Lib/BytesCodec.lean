import FeProofs.Lib.ExportedCorrect
import FeProofs.Lib.AbiBytes

/-!
# Std's `bytes` codec, as exported

`decode_msg_field_from_Sol_Bytes_CallData`, std's decoder of a `bytes` field of a message from
call data, against the ABI's reading of a `bytes` value (`bytesAt?`): the field's head word is
the tail's offset from the message's start, the tail its length word followed by the bytes.
-/

namespace FeProofs.Lib

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

/-- The `bytes` value whose head word is at `head` of call data `cd`, of a message that starts
    at `base`, as std's decoder accepts it: the offset does not overflow, the tail's length word
    lies within call data, the bytes too, and their count is at most `2 ^ 64 - 64`; else none. -/
def bytesAt? (cd : ByteArray) (base head : Nat) : Option ByteArray :=
  let off := (uInt256OfByteArray (cd.readBytes head 32)).toNat
  let p := base + off
  let L := (uInt256OfByteArray (cd.readBytes p 32)).toNat
  if off ≤ UInt256.size - 1 - base ∧ p + 32 ≤ cd.size ∧ p + 32 + L ≤ cd.size ∧ L ≤ 2 ^ 64 - 64 then
    some (cd.extract (p + 32) (p + 32 + L))
  else none

attribute [local simp]
  checkedAdd checkedSub alloc mstore readPaddedWord zeroMem returnData panicCode toNat0 toNat32

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checkedTail_exec (base off : UInt256) :
    (checked_tail_Sol base off).exec I w =
      if UInt256.size - 1 - base.toNat < off.toNat then some (.error (.revert ByteArray.empty))
      else some (.ok (base + off, w)) := by
  have hmax : (~~~UInt256.ofNat 0).toNat = UInt256.size - 1 := by decide
  have hsub : (~~~UInt256.ofNat 0 - base).toNat = UInt256.size - 1 - base.toNat := by
    rw [show ~~~UInt256.ofNat 0 - base = UInt256.sub (~~~UInt256.ofNat 0) base from rfl,
      usub_toNat (by rw [hmax]; have := base.val.isLt; change base.toNat < UInt256.size at this; omega),
      hmax]
  simp only [checked_tail_Sol, hsub]
  split_ifs <;> simp_all [revertEmpty] <;> omega


/-- The `n` zero bytes `alloc` appends, as `zeros`. -/
theorem replicate_zeros (n : Nat) : (⟨Array.replicate n 0⟩ : ByteArray) = zeros n := rfl

theorem zeros_append (a b : Nat) : zeros a ++ zeros b = zeros (a + b) := by
  apply ByteArray.ext
  simp [zeros, Array.replicate_append_replicate]

theorem zeros_extract' (n a b : Nat) : (zeros n).extract a b = zeros (min b n - a) := by
  apply ByteArray.ext
  simp [zeros, ByteArray.data_extract]

theorem word0_bytes : (UInt256.ofNat 0).toByteArray = zeros 32 := by
  apply ByteArray.ext; apply Array.toList_inj.mp; decide +kernel

theorem extract_split (d : ByteArray) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    d.extract a c = d.extract a b ++ d.extract b c := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [Array.extract_append_extract, Nat.min_eq_left hab, Nat.max_eq_right hbc]

/-- What std's copy of a `bytes` payload leaves in `cap` fresh zero bytes after `mem`: its last
    word zeroed again, then the length word and the `L` bytes from `p` of call data copied to its
    start.  That is the payload's ABI tail. -/
theorem payload_memory (mem cd : ByteArray) (p L : Nat) (hc : p + 32 + L ≤ cd.size)
    (hw : cd.extract p (p + 32) = wordOf L) :
    cd.write p ((UInt256.ofNat 0).toByteArray.write 0 (mem ++ zeros ((L + 63) / 32 * 32))
        (mem.size + ((L + 63) / 32 * 32 - 32)) 32) mem.size (32 + L) =
      mem ++ abiBytesTail (cd.extract (p + 32) (p + 32 + L)) := by
  have hd : (cd.extract (p + 32) (p + 32 + L)).size = L := by
    rw [ByteArray.size_extract]; omega
  have hcap : 32 ≤ (L + 63) / 32 * 32 := by omega
  have hz : (UInt256.ofNat 0).toByteArray.write 0 (mem ++ zeros ((L + 63) / 32 * 32))
      (mem.size + ((L + 63) / 32 * 32 - 32)) 32 = mem ++ zeros ((L + 63) / 32 * 32) := by
    rw [write_tail _ mem _ 0 ((L + 63) / 32 * 32 - 32) 32 rfl (by decide)
      (by rw [word0_bytes, zeros_size']) (by rw [zeros_size']; omega), word0_bytes,
      zeros_extract', zeros_extract', zeros_extract', zeros_append, zeros_append]
    rw [zeros_size']
    congr 2
    omega
  rw [hz, write_tail cd mem _ p 0 (32 + L) (by simp) (by omega) (by omega)
      (by rw [zeros_size']; omega), zeros_extract', zeros_extract',
    show p + (32 + L) = p + 32 + L by omega, extract_split cd (show p ≤ p + 32 by omega)
      (show p + 32 ≤ p + 32 + L by omega), hw, zeros_size']
  have he : zeros (min 0 ((L + 63) / 32 * 32) - 0) = ByteArray.empty := rfl
  rw [he, ByteArray.empty_append]
  simp only [abiBytesTail, hd, padLen]
  rw [show min ((L + 63) / 32 * 32) ((L + 63) / 32 * 32) - (0 + (32 + L)) = (32 - L % 32) % 32 by
    omega]

/-- A word rounded down to a multiple of 32, as `and _ (not 31)` makes it.  (The same fact as
    `Fe.Sonatina.and_mask32`, which lives above the checker.) -/
theorem land_mask32 (x : Nat) (hx : x < 2 ^ 256) :
    x &&& 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      x / 32 * 32 := by
  have hm : (115792089237316195423570985008687907853269984665640564039457584007913129639904 : Nat)
      = (2 ^ 251 - 1) <<< 5 := by norm_num [Nat.shiftLeft_eq]
  have hr : x / 32 * 32 = (x >>> 5) <<< 5 := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  by_cases h5 : 5 ≤ j
  · rw [show 5 + (j - 5) = j by omega]
    by_cases hj : j < 256
    · simp [h5, show j - 5 < 251 by omega]
    · have : x.testBit j = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
          (show 256 ≤ j by omega)))
      simp [h5, this]
  · simp [h5]

/-- A word of call data within it is its 32 bytes there. -/
theorem readBytes32_extract (cd : ByteArray) {off : Nat} (h : off + 32 ≤ cd.size) :
    cd.readBytes off 32 = cd.extract off (off + 32) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [readBytes_at_toList_any cd off h, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, show off + 32 - off = 32 by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Std's copy of a `bytes` payload whose tail starts at `p` of call data: revert unless the
    length word and the `L` bytes after it lie within call data and `L ≤ 2 ^ 64 - 64`; else the
    pointer, length and size of a fresh buffer that holds the payload's ABI tail. -/
theorem copyPayload_exec (p : Nat) (hp : p < 2 ^ 256) (hfits : I.calldata.size < 2 ^ 64)
    (hroom : w.memory.size + 2 ^ 64 < UInt256.size) :
    (copy_dynamic_payload_from_with_input_len_Sol_CallData ⟨UInt256.ofNat 0⟩ (UInt256.ofNat p)
      (UInt256.ofNat I.calldata.size)).exec I w =
      let L := (uInt256OfByteArray (I.calldata.readBytes p 32)).toNat
      if p + 32 ≤ I.calldata.size ∧ p + 32 + L ≤ I.calldata.size ∧ L ≤ 2 ^ 64 - 64 then
        some (.ok ((UInt256.ofNat w.memory.size, uInt256OfByteArray (I.calldata.readBytes p 32),
            UInt256.ofNat ((L + 63) / 32 * 32)),
          { w with memory := w.memory ++ abiBytesTail (I.calldata.extract (p + 32) (p + 32 + L)) }))
      else some (.error (.revert ByteArray.empty)) := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have tN : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := ulit_toNat' _ (by omega)
  have tp : (UInt256.ofNat p).toNat = p := ulit_toNat' _ (by omega)
  have t0p : (UInt256.ofNat 0 + UInt256.ofNat p).toNat = p := by
    rw [uadd_toNat, tp, show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add]
    exact Nat.mod_eq_of_lt (show p < UInt256.size by omega)
  have hmax : (~~~UInt256.ofNat 0).toNat = 2 ^ 256 - 1 := by decide
  have hmaxp : MAX_PAYLOAD_LEN = pure (UInt256.ofNat (2 ^ 64 - 32)) := by
    have e1 : (UInt256.ofNat 18446744073709551615).sub (UInt256.ofNat 31) =
        UInt256.ofNat 18446744073709551584 := by decide
    simp [MAX_PAYLOAD_LEN, MAX_ALLOCATION, downcast_saturate_u64_usize, hmax, e1,
      show (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 from rfl,
      show (UInt256.ofNat 31).toNat = 31 from rfl]
  generalize hLw : uInt256OfByteArray (I.calldata.readBytes p 32) = Lw
  by_cases c1 : I.calldata.size < p
  · simp [copy_dynamic_payload_from_with_input_len_Sol_CallData,
      checked_dynamic_payload_with_input_len_Sol_CallData, checked_frame_end_Sol, tN, tp, c1,
      Sol_decode_error, revertEmpty]
    omega
  have hsubNp : (UInt256.ofNat I.calldata.size - UInt256.ofNat p).toNat = I.calldata.size - p := by
    rw [ofNat_sub_ofNat (by omega) (by omega), ulit_toNat' _ (by omega)]
  by_cases c2 : I.calldata.size - p < 32
  · simp [copy_dynamic_payload_from_with_input_len_Sol_CallData,
      checked_dynamic_payload_with_input_len_Sol_CallData, checked_frame_end_Sol, tN, tp, c1, c2,
      hsubNp, Sol_decode_error, revertEmpty]
    omega
  have sub' : ∀ a b : Nat, a < UInt256.size → b ≤ a →
      (UInt256.ofNat a).sub (UInt256.ofNat b) = UInt256.ofNat (a - b) :=
    fun a b ha hb => ofNat_sub_ofNat ha hb
  have hp32 : UInt256.ofNat p + UInt256.ofNat 32 = UInt256.ofNat (p + 32) :=
    ofNat_add_ofNat (by omega)
  obtain ⟨L, hL, rfl⟩ : ∃ L, L < 2 ^ 256 ∧ Lw = UInt256.ofNat L :=
    ⟨Lw.toNat, Lw.val.isLt, (u256_ofNat_toNat Lw).symm⟩
  have tL : (UInt256.ofNat L).toNat = L := ulit_toNat' _ (by omega)
  have hpN : p + 32 ≤ I.calldata.size := by omega
  have t32p : (UInt256.ofNat (p + 32)).toNat = p + 32 := ulit_toNat' _ (by omega)
  have hsub2 := sub' I.calldata.size (p + 32) (by omega) hpN
  have tNp : (UInt256.ofNat (I.calldata.size - (p + 32))).toNat = I.calldata.size - (p + 32) :=
    ulit_toNat' _ (by omega)
  have hrd : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 0 + UInt256.ofNat p).toNat 32) =
      UInt256.ofNat L := by rw [t0p, hLw]
  by_cases c3 : I.calldata.size - (p + 32) < L
  · simp [copy_dynamic_payload_from_with_input_len_Sol_CallData,
      checked_dynamic_payload_with_input_len_Sol_CallData, checked_frame_end_Sol,
      checked_dynamic_payload_after_head_Sol_CallData, CallData_word_at, tN, tp, c1, c2, c3,
      hsubNp, hp32, t32p, hsub2, tNp, hrd, tL, Sol_decode_error, revertEmpty,
      show ¬ UInt256.size ≤ p + 32 by omega, show ¬ I.calldata.size < p + 32 by omega]
    (try simp only [tL, t32p, t0p] at *); omega
  have hmx : (UInt256.ofNat 18446744073709551584).sub (UInt256.ofNat 32) =
      UInt256.ofNat 18446744073709551552 := sub' _ _ (by omega) (by omega)
  have tmx : (UInt256.ofNat 18446744073709551552).toNat = 18446744073709551552 := rfl
  have tmx' : (UInt256.ofNat 18446744073709551584).toNat = 18446744073709551584 := rfl
  by_cases c4 : 2 ^ 64 - 64 < L
  · have c4' : 18446744073709551552 < L := by omega
    simp [c4', copy_dynamic_payload_from_with_input_len_Sol_CallData,
      checked_dynamic_payload_with_input_len_Sol_CallData, checked_frame_end_Sol,
      checked_dynamic_payload_after_head_Sol_CallData, CallData_word_at, tN, tp, c1, c2, c3, c4,
      hsubNp, hp32, t32p, hsub2, tNp, hrd, tL, hmaxp, hmx, tmx, tmx', Sol_decode_error, revertEmpty, -MAX_PAYLOAD_LEN,
      show ¬ UInt256.size ≤ p + 32 by omega, show ¬ I.calldata.size < p + 32 by omega]
  have c4' : ¬ 18446744073709551552 < L := by omega
  have hL63 : UInt256.ofNat L + UInt256.ofNat 63 = UInt256.ofNat (L + 63) :=
    ofNat_add_ofNat (by omega)
  have hcapw : UInt256.ofNat (L + 63) &&&
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      UInt256.ofNat ((L + 63) / 32 * 32) := by
    apply u256_inj
    rw [show ∀ a b : UInt256, (a &&& b) = UInt256.land a b from fun _ _ => rfl, uland_toNat,
      ulit_toNat' _ (by omega), ulit_toNat' _ (by decide), ulit_toNat' _ (by omega),
      land_mask32 _ (by omega), show (L + 63) / 32 = (L + 63) / 32 from rfl]
  have tcap : (UInt256.ofNat ((L + 63) / 32 * 32)).toNat = (L + 63) / 32 * 32 :=
    ulit_toNat' _ (by omega)
  have h32L : UInt256.ofNat 32 + UInt256.ofNat L = UInt256.ofNat (32 + L) :=
    ofNat_add_ofNat (by omega)
  have t32L : (UInt256.ofNat (32 + L)).toNat = 32 + L := ulit_toNat' _ (by omega)
  have hc32 := sub' ((L + 63) / 32 * 32) 32 (by omega) (by omega)
  have tm : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ (by omega)
  have hpo : UInt256.ofNat w.memory.size + UInt256.ofNat ((L + 63) / 32 * 32 - 32) =
      UInt256.ofNat (w.memory.size + ((L + 63) / 32 * 32 - 32)) := ofNat_add_ofNat (by omega)
  have tpo : (UInt256.ofNat (w.memory.size + ((L + 63) / 32 * 32 - 32))).toNat =
      w.memory.size + ((L + 63) / 32 * 32 - 32) := ulit_toNat' _ (by omega)
  have hs32 : (I.calldata.readBytes p 32).size = 32 := by
    rw [readBytes32_extract _ hpN, ByteArray.size_extract]; omega
  have hw : I.calldata.extract p (p + 32) = wordOf L := by
    rw [← readBytes32_extract _ hpN, wordOf, ← hLw, toByteArray_uInt256OfByteArray_of_size32 hs32]
  have hmem := payload_memory w.memory I.calldata p L (by omega) hw
  simp [copy_dynamic_payload_from_with_input_len_Sol_CallData,
    checked_dynamic_payload_with_input_len_Sol_CallData, checked_frame_end_Sol,
    checked_dynamic_payload_after_head_Sol_CallData, CallData_word_at, copy_dynamic_bytes_CallData,
    copy_padded_payload_CallData, CallData_copy_to_memory_unchecked, alloc_bytes_unchecked,
    tN, tp, c1, c2, c3, c4', hsubNp, hp32, t32p, hsub2, tNp, hrd, tL, hmaxp, hmx, tmx, tmx',
    -MAX_PAYLOAD_LEN, show ¬ UInt256.size ≤ p + 32 by omega,
    show ¬ I.calldata.size < p + 32 by omega, hL63, hcapw, tcap, h32L, t32L, hc32, tm, hpo, tpo,
    show ¬ UInt256.size ≤ L + 63 by omega, show ¬ UInt256.size ≤ 32 + L by omega,
    show (UInt256.ofNat 63).toNat = 63 from rfl,
    show w.memory.size + (L + 63) / 32 * 32 < UInt256.size by omega,
    show ¬ (L + 63) / 32 * 32 < 32 by omega, word_to_usize, ptr_offset, store_word, cast_u8_u256,
    Bytes_from_validated_abi_tail, replicate_zeros]
  rw [if_pos ⟨hpN, by omega, by omega⟩]
  simp [Fe.EVM.calldatacopy, t0p, tm, t32L, hmem]

theorem decodeMsgBytes_eq (cd : CallData) (a b c : UInt256) :
    decode_msg_field_from_Sol_Bytes_CallData cd a b c =
      decode_field_from_prechecked_head_Sol_Bytes_CallData cd a b c := by
  simp [decode_msg_field_from_Sol_Bytes_CallData, Bytes_IS_DYNAMIC]

theorem decodeBounded_eq (cd : CallData) (p n : UInt256) :
    Bytes_decode_from_bounded_Sol_CallData cd p n = (do
      let r ← copy_dynamic_payload_from_with_input_len_Sol_CallData cd p n
      let l ← word_to_usize r.2.1
      let b ← Bytes_from_validated_abi_tail r.1 l r.2.2
      return b) := rfl

theorem decodePrechecked_eq (cd : CallData) (a b c : UInt256) :
    decode_field_from_prechecked_head_Sol_Bytes_CallData cd a b c = (do
      let off ← CallData_word_at cd b
      let p ← checked_tail_Sol a off
      Bytes_decode_from_bounded_Sol_CallData cd p c) := by
  simp [decode_field_from_prechecked_head_Sol_Bytes_CallData, Bytes_IS_DYNAMIC]

/-- A bind whose first step returns. -/
theorem exec_bind_ok {α β : Type} {m : FeM α} {k : α → FeM β} {a : α} {w' : World}
    (h : m.exec I w = some (.ok (a, w'))) : (m >>= k).exec I w = (k a).exec I w' := by
  rw [Fe.M.exec_bind, h]

/-- A bind whose first step fails. -/
theorem exec_bind_err {α β : Type} {m : FeM α} {k : α → FeM β} {e : Exit World}
    (h : m.exec I w = some (.error e)) : (m >>= k).exec I w = some (.error e) := by
  rw [Fe.M.exec_bind, h]

theorem prechecked_exec (cd : CallData) (a b c off : UInt256)
    (hw : (CallData_word_at cd b).exec I w = some (.ok (off, w))) :
    (decode_field_from_prechecked_head_Sol_Bytes_CallData cd a b c).exec I w =
      (checked_tail_Sol a off >>= fun p => Bytes_decode_from_bounded_Sol_CallData cd p c).exec I w := by
  rw [decodePrechecked_eq, exec_bind_ok I w hw]

theorem bounded_exec (cd : CallData) (p n : UInt256) :
    (Bytes_decode_from_bounded_Sol_CallData cd p n).exec I w =
      match (copy_dynamic_payload_from_with_input_len_Sol_CallData cd p n).exec I w with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (r, w')) => some (.ok (⟨r.1, r.2.1, r.2.2⟩, w')) := by
  rw [decodeBounded_eq]
  simp only [Fe.M.exec_bind, word_to_usize, Bytes_from_validated_abi_tail, Fe.M.exec_pure]
  rcases (copy_dynamic_payload_from_with_input_len_Sol_CallData cd p n).exec I w with
    _ | _ | ⟨r, w'⟩ <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Std's decoder of a `bytes` field of a message from call data, whose head word is at `head`
    of a message that starts at `base`: the value `bytesAt?` reads, in a fresh buffer at the end
    of memory that holds its ABI tail, or a revert with no data where `bytesAt?` reads none. -/
theorem decodeBytesField_exec (base head : Nat) (hb : base < 2 ^ 256) (hh : head < 2 ^ 256)
    (hfits : I.calldata.size < 2 ^ 64) (hroom : w.memory.size + 2 ^ 64 < UInt256.size) :
    (decode_msg_field_from_Sol_Bytes_CallData ⟨UInt256.ofNat 0⟩ (UInt256.ofNat base)
      (UInt256.ofNat head) (UInt256.ofNat I.calldata.size)).exec I w =
      match bytesAt? I.calldata base head with
      | none => some (.error (.revert ByteArray.empty))
      | some d => some (.ok (⟨UInt256.ofNat w.memory.size, UInt256.ofNat d.size,
          UInt256.ofNat ((d.size + 63) / 32 * 32)⟩, { w with memory := w.memory ++ abiBytesTail d })) := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have th : (UInt256.ofNat 0 + UInt256.ofNat head).toNat = head := by
    rw [uadd_toNat]
    show (0 + (UInt256.ofNat head).toNat) % _ = _
    rw [Nat.zero_add, ulit_toNat' _ (by omega)]
    exact Nat.mod_eq_of_lt (show head < UInt256.size by omega)
  have tb : (UInt256.ofNat base).toNat = base := ulit_toNat' _ (by omega)
  generalize hoff : uInt256OfByteArray (I.calldata.readBytes head 32) = off
  have hto := off.val.isLt
  change off.toNat < 2 ^ 256 at hto
  have hw : (CallData_word_at ⟨UInt256.ofNat 0⟩ (UInt256.ofNat head)).exec I w =
      some (.ok (off, w)) := by
    show (calldataload (UInt256.ofNat 0 + UInt256.ofNat head)).exec I w = _
    rw [exec_calldataload, th, hoff]
  rw [decodeMsgBytes_eq, prechecked_exec I w _ _ _ _ off hw]
  have hct := checkedTail_exec I w (UInt256.ofNat base) off
  rw [tb] at hct
  unfold bytesAt?
  simp only [hoff]
  by_cases h1 : UInt256.size - 1 - base < off.toNat
  · rw [if_pos h1] at hct
    rw [exec_bind_err I w hct, if_neg (by omega)]
  have hp : UInt256.ofNat base + off = UInt256.ofNat (base + off.toNat) := by
    rw [← ofNat_add_ofNat (by omega), u256_ofNat_toNat]
  rw [if_neg h1, hp] at hct
  rw [exec_bind_ok I w hct, bounded_exec,
    copyPayload_exec I w (base + off.toNat) (by omega) hfits hroom]
  generalize uInt256OfByteArray (I.calldata.readBytes (base + off.toNat) 32) = Lw
  by_cases hc : base + off.toNat + 32 ≤ I.calldata.size ∧
      base + off.toNat + 32 + Lw.toNat ≤ I.calldata.size ∧ Lw.toNat ≤ 2 ^ 64 - 64
  · have hd : (I.calldata.extract (base + off.toNat + 32) (base + off.toNat + 32 + Lw.toNat)).size =
        Lw.toNat := by rw [ByteArray.size_extract]; omega
    rw [if_pos hc, if_pos ⟨by omega, hc⟩]
    simp only [hd, u256_ofNat_toNat]
  · rw [if_neg hc, if_neg (fun h => hc h.2)]
