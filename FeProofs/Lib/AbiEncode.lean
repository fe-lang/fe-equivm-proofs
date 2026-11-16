import FeProofs.Lib.BytesCodec

/-!
# Std's ABI encoder of `bytes` fields, as exported

`encode_field_Sol_Bytes`, std's encoder of one `bytes` field of a tuple, is shared by every
tuple and by the single-value return encoder.  `encodeFieldBytes_exec` states it on a buffer
`T` at the end of memory: it writes the tail's offset in the head and copies the value's ABI tail
(`BytesHolds`: the `Bytes` value holds its ABI tail in memory) into the tail region.
-/

namespace FeProofs.Lib

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

/-- The `Bytes` value `b` holds the bytes `d` in memory `mem`: its pointer is at their ABI tail
    (length word, bytes, zeros to a whole word), its length is theirs, its size the tail's. -/
structure BytesHolds (b : Bytes) (d : ByteArray) (mem : ByteArray) : Prop where
  len : b.len.toNat = d.size
  size : b.size.toNat = (abiBytesTail d).size
  bound : b.data.toNat + (abiBytesTail d).size ≤ mem.size
  bytes : mem.extract b.data.toNat (b.data.toNat + (abiBytesTail d).size) = abiBytesTail d

theorem BytesHolds.append {b : Bytes} {d mem : ByteArray} (h : BytesHolds b d mem)
    (X : ByteArray) : BytesHolds b d (mem ++ X) := by
  refine ⟨h.len, h.size, by rw [ByteArray.size_append]; have := h.bound; omega, ?_⟩
  rw [extract_append_left _ _ _ _ h.bound, h.bytes]

/-- The value std's `bytes` decoder returns holds the bytes it read. -/
theorem bytesHolds_decoded (mem d : ByteArray)
    (hroom : mem.size + (abiBytesTail d).size < UInt256.size) :
    BytesHolds ⟨UInt256.ofNat mem.size, UInt256.ofNat d.size,
      UInt256.ofNat ((d.size + 63) / 32 * 32)⟩ d (mem ++ abiBytesTail d) := by
  have ht := abiBytesTail_size d
  refine ⟨ulit_toNat' _ (by omega), ?_, ?_, ?_⟩
  · show (UInt256.ofNat ((d.size + 63) / 32 * 32)).toNat = _
    rw [ulit_toNat' _ (by omega)]; omega
  · show (UInt256.ofNat mem.size).toNat + _ ≤ _
    rw [ulit_toNat' _ (by omega), ByteArray.size_append]
  · show (mem ++ abiBytesTail d).extract (UInt256.ofNat mem.size).toNat
      ((UInt256.ofNat mem.size).toNat + _) = _
    rw [ulit_toNat' _ (by omega), extract_append_right_window _ _ _ _ (le_refl _), Nat.sub_self,
      Nat.add_sub_cancel_left, byteArray_extract_self]

/-- `T` with the bytes `X` written `k` bytes into it. -/
def put (T : ByteArray) (k : Nat) (X : ByteArray) : ByteArray :=
  T.extract 0 k ++ X ++ T.extract (k + X.size) T.size

theorem put_size {T X : ByteArray} {k : Nat} (h : k + X.size ≤ T.size) :
    (put T k X).size = T.size := by
  simp only [put, ByteArray.size_append, ByteArray.size_extract]; omega

attribute [local simp] alloc mstore zeroMem mcopy

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Std's encoder of a `bytes` field of a tuple whose frame is the buffer `T` at the end of
    memory, its head word `h` bytes into the frame and the free tail `k` bytes into it: the offset
    `k` in the head, the value's ABI tail at `k`, and the tail frame past it. -/
theorem encodeFieldBytes_exec {b : Bytes} {d M T : ByteArray} (hb : BytesHolds b d M)
    (hmem : w.memory = M ++ T) {h k : Nat} (hh : h + 32 ≤ T.size)
    (hk : k + (abiBytesTail d).size ≤ T.size) (hroom : M.size + T.size < UInt256.size) :
    (encode_field_Sol_Bytes b ⟨UInt256.ofNat M.size, UInt256.ofNat T.size⟩ (UInt256.ofNat h)
        ⟨UInt256.ofNat (M.size + k), UInt256.ofNat (T.size - k)⟩).exec I w =
      some (.ok (⟨UInt256.ofNat (M.size + (k + (abiBytesTail d).size)),
          UInt256.ofNat (T.size - (k + (abiBytesTail d).size))⟩,
        { w with memory := M ++ put (put T h (wordOf k)) k (abiBytesTail d) })) := by
  have hsz : UInt256.size = 2 ^ 256 := rfl
  obtain ⟨p, l, c⟩ := b
  have hs := hb.size
  have hbd := hb.bound
  simp only at hs hbd
  have ht := abiBytesTail_size d
  generalize hS : (abiBytesTail d).size = s at hs hbd hk ht
  have hc : c = UInt256.ofNat s := by rw [← hs, u256_ofNat_toNat]
  subst hc
  have hMs : M.size + T.size ≤ w.memory.size := by rw [hmem, ByteArray.size_append]
  have tT : (UInt256.ofNat T.size).toNat = T.size := ulit_toNat' _ (by omega)
  have th : (UInt256.ofNat h).toNat = h := ulit_toNat' _ (by omega)
  have ts : (UInt256.ofNat s).toNat = s := ulit_toNat' _ (by omega)
  have tTk : (UInt256.ofNat (T.size - k)).toNat = T.size - k := ulit_toNat' _ (by omega)
  have hsubk : UInt256.ofNat T.size - UInt256.ofNat (T.size - k) = UInt256.ofNat k :=
    by rw [ofNat_sub_ofNat (by omega) (by omega), show T.size - (T.size - k) = k by omega]
  have hsubh : (UInt256.ofNat T.size - UInt256.ofNat h).toNat = T.size - h := by
    rw [ofNat_sub_ofNat (by omega) (by omega), ulit_toNat' _ (by omega)]
  have hsub0 : UInt256.ofNat (T.size - k) - UInt256.ofNat 0 = UInt256.ofNat (T.size - k) := by
    rw [ofNat_sub_ofNat (by omega) (by omega), Nat.sub_zero]
  have hsub0s : UInt256.ofNat s - UInt256.ofNat 0 = UInt256.ofNat s := by
    rw [ofNat_sub_ofNat (by omega) (by omega), Nat.sub_zero]
  have hsubs : UInt256.ofNat (T.size - k) - UInt256.ofNat s = UInt256.ofNat (T.size - (k + s)) := by
    rw [ofNat_sub_ofNat (by omega) (by omega), Nat.sub_sub]
  have hMh : UInt256.ofNat M.size + UInt256.ofNat h = UInt256.ofNat (M.size + h) :=
    ofNat_add_ofNat (by omega)
  have hMks : UInt256.ofNat (M.size + k) + UInt256.ofNat s = UInt256.ofNat (M.size + (k + s)) := by
    rw [ofNat_add_ofNat (by omega), Nat.add_assoc]
  have tMh : (UInt256.ofNat (M.size + h)).toNat = M.size + h := ulit_toNat' _ (by omega)
  have tMk : (UInt256.ofNat (M.size + k)).toNat = M.size + k := ulit_toNat' _ (by omega)
  have hw1 : (wordOf k).write 0 (M ++ T) (M.size + h) 32 = M ++ put T h (wordOf k) := by
    rw [write_tail _ _ _ 0 h 32 (by rfl) (by decide) (by rw [wordOf_size]) hh, put, wordOf_size,
      wordOf, toByteArray_extract_all]
  have hT1 : (put T h (wordOf k)).size = T.size := put_size (by rw [wordOf_size]; exact hh)
  have hw2 : (M ++ put T h (wordOf k)).write p.toNat (M ++ put T h (wordOf k)) (M.size + k) s =
      M ++ put (put T h (wordOf k)) k (abiBytesTail d) := by
    rw [write_tail _ _ _ p.toNat k s (by rfl) (by omega)
        (by rw [ByteArray.size_append]; omega) (by rw [hT1]; exact hk),
      extract_append_left _ _ _ _ hbd, ← hS, hb.bytes]
    rfl
  simp [encode_field_Sol_Bytes, Bytes_IS_DYNAMIC, Bytes_payload_size, Bytes_encoded_size,
    AbiFrame_len, AbiFrame_store_word, AbiFrame_slice, ptr_offset, word_to_usize, store_word,
    cast_u8_u256, Bytes_encode_Sol, Bytes_encoded_span, MemSlice_from_raw_parts_ref_u8,
    AbiFrame_copy_from, MemSlice_len_u8, MemSlice_ptr_u8, copy, copy_raw, AbiFrame_tail,
    tT, th, ts, tTk, hsubk, hsubh, hsub0, hsub0s, hsubs, hMh, hMks, tMh, tMk, toNat0, toNat32,
    Fe.EVM.add_zero, show ¬ T.size < h by omega, show ¬ T.size - h < 32 by omega,
    show ¬ T.size - k < s by omega, hmem]
  rw [← wordOf, hw1, hw2]

/-! ## The buffer of a tuple of `bytes`, field by field -/

theorem put_zeros {A B X : ByteArray} {m : Nat} (h : X.size ≤ m) :
    put (A ++ zeros m ++ B) A.size X = A ++ X ++ zeros (m - X.size) ++ B := by
  have hz := zeros_size' m
  unfold put
  rw [show A ++ zeros m ++ B = A ++ (zeros m ++ B) from ByteArray.append_assoc,
    extract_append_left _ _ _ _ (le_refl _), byteArray_extract_self,
    extract_append_right_window _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    ByteArray.size_append, ByteArray.size_append, Nat.add_sub_cancel_left,
    extract_append_span (zeros m) B X.size ((zeros m).size + B.size) (by omega) (by omega), hz,
    zeros_extract', Nat.min_self, Nat.add_sub_cancel_left, byteArray_extract_self]
  simp only [ByteArray.append_assoc]

theorem abiBytesHeads_size (ds : List ByteArray) (off : Nat) :
    (abiBytesHeads ds off).size = 32 * ds.length := by
  induction ds generalizing off with
  | nil => rfl
  | cons d ds ih => simp only [abiBytesHeads, ByteArray.size_append, wordOf_size, ih,
      List.length_cons]; ring

theorem abiBytesHeads_append (ds : List ByteArray) (d : ByteArray) (off : Nat) :
    abiBytesHeads (ds ++ [d]) off = abiBytesHeads ds off ++ wordOf (off + (abiBytesTails ds).size) := by
  induction ds generalizing off with
  | nil => simp [abiBytesHeads, abiBytesTails]
  | cons e ds ih =>
    simp only [List.cons_append, abiBytesHeads, ih, abiBytesTails, ByteArray.size_append,
      ByteArray.append_assoc, Nat.add_assoc]

theorem abiBytesTails_append (ds : List ByteArray) (d : ByteArray) :
    abiBytesTails (ds ++ [d]) = abiBytesTails ds ++ abiBytesTail d := by
  induction ds with
  | nil => simp [abiBytesTails]
  | cons e ds ih => simp only [List.cons_append, abiBytesTails, ih, ByteArray.append_assoc]

/-- A tuple's buffer after the fields `ds`: their offsets at `N`, the head's free words, their
    tails, and the tail region's free bytes. -/
def tupleBuf (ds : List ByteArray) (N a b : Nat) : ByteArray :=
  abiBytesHeads ds N ++ zeros a ++ (abiBytesTails ds ++ zeros b)

theorem tupleBuf_size (ds : List ByteArray) (N a b : Nat) :
    (tupleBuf ds N a b).size = 32 * ds.length + a + ((abiBytesTails ds).size + b) := by
  simp [tupleBuf, ByteArray.size_append, abiBytesHeads_size]

/-- One more field: its offset in the head's next word, its tail after the others. -/
theorem tupleBuf_step (ds : List ByteArray) (d : ByteArray) {N a b : Nat}
    (hN : 32 * ds.length + a = N) (ha : 32 ≤ a) (hb : (abiBytesTail d).size ≤ b) :
    put (put (tupleBuf ds N a b) (32 * ds.length) (wordOf (N + (abiBytesTails ds).size)))
        (N + (abiBytesTails ds).size) (abiBytesTail d) =
      tupleBuf (ds ++ [d]) N (a - 32) (b - (abiBytesTail d).size) := by
  have h1 := put_zeros (A := abiBytesHeads ds N) (B := abiBytesTails ds ++ zeros b)
    (X := wordOf (N + (abiBytesTails ds).size)) (m := a) (by rw [wordOf_size]; exact ha)
  rw [abiBytesHeads_size, wordOf_size] at h1
  unfold tupleBuf
  rw [h1]
  have h2 := put_zeros (A := abiBytesHeads ds N ++ wordOf (N + (abiBytesTails ds).size) ++
    zeros (a - 32) ++ abiBytesTails ds) (B := .empty) (X := abiBytesTail d) (m := b) hb
  have hs : (abiBytesHeads ds N ++ wordOf (N + (abiBytesTails ds).size) ++ zeros (a - 32) ++
      abiBytesTails ds).size = N + (abiBytesTails ds).size := by
    simp only [ByteArray.size_append, abiBytesHeads_size, wordOf_size, zeros_size']; omega
  rw [hs] at h2
  rw [show abiBytesHeads ds N ++ wordOf (N + (abiBytesTails ds).size) ++ zeros (a - 32) ++
      (abiBytesTails ds ++ zeros b) = abiBytesHeads ds N ++ wordOf (N + (abiBytesTails ds).size) ++
      zeros (a - 32) ++ abiBytesTails ds ++ zeros b ++ .empty by
    simp only [ByteArray.append_empty, ByteArray.append_assoc], h2, abiBytesHeads_append,
    abiBytesTails_append]
  simp only [ByteArray.append_empty, ByteArray.append_assoc]

theorem tupleBuf_nil (N a b : Nat) : tupleBuf [] N a b = zeros (a + b) := by
  simp only [tupleBuf, abiBytesHeads, abiBytesTails, ByteArray.empty_append]
  exact zeros_append a b

theorem tupleBuf_full (ds : List ByteArray) {N : Nat} (hN : 32 * ds.length = N) :
    tupleBuf ds N 0 0 = abiEncodeBytes ds := by
  have e : zeros 0 = .empty := rfl
  simp only [tupleBuf, abiEncodeBytes, e, ByteArray.append_empty, ← hN]

/-- `encodeFieldBytes_exec` on a tuple's buffer: the field after `ds`. -/
theorem encodeFieldStep_exec {b : Bytes} {d M : ByteArray} {ds : List ByteArray}
    {N a c n h k : Nat} (hb : BytesHolds b d M) (hmem : w.memory = M ++ tupleBuf ds N a c)
    (hn : (tupleBuf ds N a c).size = n) (hh : h = 32 * ds.length)
    (hk : k = N + (abiBytesTails ds).size) (hN : 32 * ds.length + a = N) (ha : 32 ≤ a)
    (hc : (abiBytesTail d).size ≤ c) (hroom : M.size + n < UInt256.size) :
    (encode_field_Sol_Bytes b ⟨UInt256.ofNat M.size, UInt256.ofNat n⟩ (UInt256.ofNat h)
        ⟨UInt256.ofNat (M.size + k), UInt256.ofNat (n - k)⟩).exec I w =
      some (.ok (⟨UInt256.ofNat (M.size + (k + (abiBytesTail d).size)),
          UInt256.ofNat (n - (k + (abiBytesTail d).size))⟩,
        { w with memory := M ++ tupleBuf (ds ++ [d]) N (a - 32) (c - (abiBytesTail d).size) })) := by
  have hs := tupleBuf_size ds N a c
  subst hn hh hk
  rw [encodeFieldBytes_exec I w hb hmem (by omega) (by omega) hroom, tupleBuf_step ds d hN ha hc]

/-! ## The tuple of five `bytes` -/

set_option maxRecDepth 10000 in
theorem abiFieldHeadBytes_eq : abi_field_head_size_Bytes = pure (UInt256.ofNat 32) := rfl

set_option maxRecDepth 10000 in
theorem tupleHead5_eq : tuple_HEAD_SIZE_Bytes_Bytes_Bytes_Bytes_Bytes = pure (UInt256.ofNat 160) :=
  rfl

theorem abiFrameTail_exec {P n k : Nat} (hroom : P + n < UInt256.size) (hk : k ≤ n) :
    (AbiFrame_tail ⟨UInt256.ofNat P, UInt256.ofNat n⟩ (UInt256.ofNat k)).exec I w =
      some (.ok (⟨UInt256.ofNat (P + k), UInt256.ofNat (n - k)⟩, w)) := by
  simp [AbiFrame_tail, ptr_offset, word_to_usize, ulit_toNat' n (by omega),
    ulit_toNat' k (by omega), show ¬ n < k by omega, ofNat_add_ofNat (show P + k < UInt256.size by omega),
    ofNat_sub_ofNat (show n < UInt256.size by omega) hk]

theorem tupleEncode5_eq (v0 : Bytes × Bytes × Bytes × Bytes × Bytes) (v1 : AbiFrame) :
    tuple_encode_Sol_Bytes_Bytes_Bytes_Bytes_Bytes v0 v1 = (do
      let r0 ← AbiFrame_tail v1 (UInt256.ofNat 160)
      let r1 ← encode_field_Sol_Bytes v0.1 v1 (UInt256.ofNat 0) r0
      let r2 ← encode_field_Sol_Bytes v0.2.1 v1 (UInt256.ofNat 32) r1
      let r3 ← encode_field_Sol_Bytes v0.2.2.1 v1 (UInt256.ofNat 64) r2
      let r4 ← encode_field_Sol_Bytes v0.2.2.2.1 v1 (UInt256.ofNat 96) r3
      let _ ← encode_field_Sol_Bytes v0.2.2.2.2 v1 (UInt256.ofNat 128) r4
      return ()) := by
  simp only [tuple_encode_Sol_Bytes_Bytes_Bytes_Bytes_Bytes,
    tuple_encode_Sol_Bytes_Bytes_Bytes_Bytes_Bytes_k1, tupleHead5_eq, abiFieldHeadBytes_eq,
    pure_bind, show UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 from rfl,
    show UInt256.ofNat 64 + UInt256.ofNat 32 = UInt256.ofNat 96 from rfl,
    show UInt256.ofNat 96 + UInt256.ofNat 32 = UInt256.ofNat 128 from rfl]

theorem abiEncodeBytes5_size (d0 d1 d2 d3 d4 : ByteArray) :
    (abiEncodeBytes [d0, d1, d2, d3, d4]).size = 160 + ((abiBytesTail d0).size +
      ((abiBytesTail d1).size + ((abiBytesTail d2).size + ((abiBytesTail d3).size +
        (abiBytesTail d4).size)))) := by
  simp [abiEncodeBytes, abiBytesHeads_size, abiBytesTails, ByteArray.size_append]

set_option maxHeartbeats 4000000 in
/-- Std's encoder of a tuple of five `bytes` into the zeroed buffer of its size at the end of
    memory: the buffer then holds the tuple's ABI encoding. -/
theorem tupleEncode5_exec {b0 b1 b2 b3 b4 : Bytes} {d0 d1 d2 d3 d4 M : ByteArray} {n : Nat}
    (h0 : BytesHolds b0 d0 M) (h1 : BytesHolds b1 d1 M) (h2 : BytesHolds b2 d2 M)
    (h3 : BytesHolds b3 d3 M) (h4 : BytesHolds b4 d4 M) (hmem : w.memory = M ++ zeros n)
    (hn : (abiEncodeBytes [d0, d1, d2, d3, d4]).size = n) (hroom : M.size + n < UInt256.size) :
    (tuple_encode_Sol_Bytes_Bytes_Bytes_Bytes_Bytes (b0, b1, b2, b3, b4)
        ⟨UInt256.ofNat M.size, UInt256.ofNat n⟩).exec I w =
      some (.ok ((), { w with memory := M ++ abiEncodeBytes [d0, d1, d2, d3, d4] })) := by
  rw [abiEncodeBytes5_size] at hn
  generalize hs0 : (abiBytesTail d0).size = s0 at hn
  generalize hs1 : (abiBytesTail d1).size = s1 at hn
  generalize hs2 : (abiBytesTail d2).size = s2 at hn
  generalize hs3 : (abiBytesTail d3).size = s3 at hn
  generalize hs4 : (abiBytesTail d4).size = s4 at hn
  have t1 : (abiBytesTails [d0]).size = s0 := by simp [abiBytesTails, hs0]
  have t2 : (abiBytesTails [d0, d1]).size = s0 + s1 := by
    simp [abiBytesTails, ByteArray.size_append, hs0, hs1]
  have t3 : (abiBytesTails [d0, d1, d2]).size = s0 + s1 + s2 := by
    simp [abiBytesTails, ByteArray.size_append, hs0, hs1, hs2]; omega
  have t4 : (abiBytesTails [d0, d1, d2, d3]).size = s0 + s1 + s2 + s3 := by
    simp [abiBytesTails, ByteArray.size_append, hs0, hs1, hs2, hs3]; omega
  have z0 : w.memory = M ++ tupleBuf [] 160 160 (n - 160) := by
    rw [hmem, tupleBuf_nil, show 160 + (n - 160) = n by omega]
  have st0 := encodeFieldStep_exec I w h0 z0 (by rw [tupleBuf_size]; simp [abiBytesTails]; omega)
    (h := 0) (k := 160) (by rfl) (by simp [abiBytesTails]) (by rfl) (by omega) (by omega) hroom
  simp only [List.nil_append, hs0] at st0
  have st1 := encodeFieldStep_exec I { w with memory := M ++ tupleBuf [d0] 160 128 (n - 160 - s0) }
    h1 rfl (by rw [tupleBuf_size]; simp [t1]; omega) (h := 32) (k := 160 + s0) (by rfl)
    (by rw [t1]) (by rfl) (by omega) (by omega) hroom
  simp only [List.cons_append, List.nil_append, hs1] at st1
  have st2 := encodeFieldStep_exec I
    { w with memory := M ++ tupleBuf [d0, d1] 160 96 (n - 160 - s0 - s1) }
    h2 rfl (by rw [tupleBuf_size]; simp [t2]; omega) (h := 64) (k := 160 + s0 + s1) (by rfl)
    (by rw [t2]; omega) (by rfl) (by omega) (by omega) hroom
  simp only [List.cons_append, List.nil_append, hs2] at st2
  have st3 := encodeFieldStep_exec I
    { w with memory := M ++ tupleBuf [d0, d1, d2] 160 64 (n - 160 - s0 - s1 - s2) }
    h3 rfl (by rw [tupleBuf_size]; simp [t3]; omega) (h := 96) (k := 160 + s0 + s1 + s2) (by rfl)
    (by rw [t3]; omega) (by rfl) (by omega) (by omega) hroom
  simp only [List.cons_append, List.nil_append, hs3] at st3
  have st4 := encodeFieldStep_exec I
    { w with memory := M ++ tupleBuf [d0, d1, d2, d3] 160 32 (n - 160 - s0 - s1 - s2 - s3) }
    h4 rfl (by rw [tupleBuf_size]; simp [t4]; omega) (h := 128) (k := 160 + s0 + s1 + s2 + s3)
    (by rfl) (by rw [t4]; omega) (by rfl) (by omega) (by omega) hroom
  simp only [List.cons_append, List.nil_append, hs4] at st4
  rw [tupleEncode5_eq, exec_bind_ok I w (abiFrameTail_exec I w hroom (by omega))]
  dsimp only
  rw [exec_bind_ok I w st0, exec_bind_ok I _ st1, exec_bind_ok I _ st2, exec_bind_ok I _ st3,
    exec_bind_ok I _ st4, Fe.M.exec_pure, show n - 160 - s0 - s1 - s2 - s3 - s4 = 0 by omega,
    show 32 - 32 = 0 from rfl, tupleBuf_full [d0, d1, d2, d3, d4] (N := 160) rfl]

/-! ## A fresh buffer, and the encoding of five `bytes` into it -/

/-- `MemBuffer::new(n)`: `n` fresh zero bytes at the end of memory, `Panic(0x41)` past
    `2 ^ 64 - 1` bytes, no end if memory would reach `2 ^ 256` bytes. -/
theorem memBufferNew_exec {n : Nat} (hn : n < UInt256.size) :
    (MemBuffer_new (UInt256.ofNat n)).exec I w =
      if 2 ^ 64 - 1 < n then some (.error (.panic 0x41))
      else if w.memory.size + n < UInt256.size then
        some (.ok (⟨UInt256.ofNat w.memory.size, UInt256.ofNat n, UInt256.ofNat n⟩,
          { w with memory := w.memory ++ zeros n }))
      else none := by
  have tn : (UInt256.ofNat n).toNat = n := ulit_toNat' _ hn
  have hmaxa : ¬ UInt256.size - 1 < 18446744073709551615 := by decide
  have tu : (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 := rfl
  by_cases h1 : 2 ^ 64 - 1 < n
  · simp [MemBuffer_new, MemBuffer_new_uninit, alloc_bytes, toNatMax, hmaxa, tu, tn, PANIC_OUT_OF_MEMORY,
      panicCode, show 18446744073709551615 < n by omega, show (UInt256.ofNat 65).toNat = 65 from rfl]
  by_cases h2 : w.memory.size + n < UInt256.size
  · have tm : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ (by omega)
    simp [MemBuffer_new, MemBuffer_new_uninit, alloc_bytes, toNatMax, hmaxa, tu, tn, h2,
      show ¬ 18446744073709551615 < n by omega, alloc, zero_bytes, zeroMem, tm]
    rw [replicate_zeros]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact byteArray_write_len_zero _ _ _ _
    · rw [write_tail _ _ _ 0 0 n (Nat.add_zero _).symm (by omega) (by rw [zeros_size']; omega)
        (by rw [zeros_size']; omega), zeros_extract', zeros_extract', zeros_extract', zeros_size',
        Nat.zero_add, Nat.min_self, Nat.sub_self, Nat.sub_zero,
        show min 0 n = 0 by omega, show zeros 0 = .empty from rfl, ByteArray.empty_append,
        ByteArray.append_empty, Nat.sub_zero]
  · simp [MemBuffer_new, MemBuffer_new_uninit, alloc_bytes, toNatMax, hmaxa, tu, tn, h2,
      show ¬ 18446744073709551615 < n by omega, alloc]

theorem allocationLen_exec {n : Nat} (hn : n < UInt256.size) :
    (allocation_len (UInt256.ofNat n)).exec I w = some (.ok (UInt256.ofNat n, w)) := by
  simp [allocation_len, usize_max, toNatMax, word_to_usize, ulit_toNat' _ hn,
    show ¬ UInt256.size - 1 < n by omega]

theorem payloadSize5_eq (v0 : Bytes × Bytes × Bytes × Bytes × Bytes) :
    abi_payload_size_tuple_Bytes_Bytes_Bytes_Bytes_Bytes v0 =
      pure (UInt256.ofNat 160 + v0.1.size + v0.2.1.size + v0.2.2.1.size + v0.2.2.2.1.size +
        v0.2.2.2.2.size) := by
  simp only [abi_payload_size_tuple_Bytes_Bytes_Bytes_Bytes_Bytes,
    tuple_payload_size_Bytes_Bytes_Bytes_Bytes_Bytes, tupleHead5_eq, dynamic_payload_size_Bytes,
    Bytes_IS_DYNAMIC, Bytes_payload_size, Bytes_encoded_size, pure_bind, ite_true, bind_pure]

theorem encodeAlloc5_eq (v0 : Bytes × Bytes × Bytes × Bytes × Bytes) :
    encode_abi_payload_tuple_Bytes_Bytes_Bytes_Bytes_Bytes v0 = (do
      let n ← abi_payload_size_tuple_Bytes_Bytes_Bytes_Bytes_Bytes v0
      let l ← allocation_len n
      let buf ← MemBuffer_new l
      let _ ← tuple_encode_Sol_Bytes_Bytes_Bytes_Bytes_Bytes v0 ⟨buf.ptr, n⟩
      return buf) := by
  simp only [encode_abi_payload_tuple_Bytes_Bytes_Bytes_Bytes_Bytes,
    encode_alloc_Sol_tuple_Bytes_Bytes_Bytes_Bytes_Bytes, Bytes_drop, dealloc_u8, cast_u8_u8,
    MemBuffer_ptr, AbiFrame_from_raw_parts, pure_bind, bind_pure]

set_option maxHeartbeats 4000000 in
/-- Std's ABI encoding of a tuple of five `bytes` values: a fresh buffer at the end of memory
    that holds the tuple's encoding, `Panic(0x41)` if it is `2 ^ 64` bytes or more. -/
theorem encodeBytes5_exec {b0 b1 b2 b3 b4 : Bytes} {d0 d1 d2 d3 d4 : ByteArray} {n : Nat}
    (hn : (abiEncodeBytes [d0, d1, d2, d3, d4]).size = n) (h0 : BytesHolds b0 d0 w.memory) (h1 : BytesHolds b1 d1 w.memory)
    (h2 : BytesHolds b2 d2 w.memory) (h3 : BytesHolds b3 d3 w.memory)
    (h4 : BytesHolds b4 d4 w.memory)
    (hfit : w.memory.size + n < UInt256.size) :
    (encode_abi_payload_tuple_Bytes_Bytes_Bytes_Bytes_Bytes (b0, b1, b2, b3, b4)).exec I w =
      if 2 ^ 64 - 1 < n then some (.error (.panic 0x41))
      else some (.ok (⟨UInt256.ofNat w.memory.size, UInt256.ofNat n, UInt256.ofNat n⟩,
        { w with memory := w.memory ++ abiEncodeBytes [d0, d1, d2, d3, d4] })) := by
  have hn5 := abiEncodeBytes5_size d0 d1 d2 d3 d4
  have hsz : ∀ {b : Bytes} {d : ByteArray}, BytesHolds b d w.memory →
      b.size = UInt256.ofNat (abiBytesTail d).size := fun h => by rw [← h.size, u256_ofNat_toNat]
  have hsum : UInt256.ofNat 160 + b0.size + b1.size + b2.size + b3.size + b4.size =
      UInt256.ofNat n := by
    rw [hsz h0, hsz h1, hsz h2, hsz h3, hsz h4, ofNat_add_ofNat (by omega),
      ofNat_add_ofNat (by omega), ofNat_add_ofNat (by omega), ofNat_add_ofNat (by omega),
      ofNat_add_ofNat (by omega)]
    congr 1
    omega
  rw [encodeAlloc5_eq, payloadSize5_eq, Fe.M.exec_bind, Fe.M.exec_pure]
  dsimp only
  rw [hsum, exec_bind_ok I w (allocationLen_exec I w (by omega)), Fe.M.exec_bind,
    memBufferNew_exec I w (by omega), ite_eq_left hfit]
  by_cases hp : 2 ^ 64 - 1 < n
  · rw [ite_eq_left hp, ite_eq_left hp]
  rw [ite_eq_right hp, ite_eq_right hp]
  dsimp only
  rw [exec_bind_ok I _ (tupleEncode5_exec I { w with memory := w.memory ++ zeros n } h0 h1 h2 h3
    h4 rfl hn hfit), Fe.M.exec_pure]

/-! ## A log, and a returned `bytes` value -/

/-- `log1` of a slice of memory: a log entry of the running contract with the topic and the
    slice's bytes.  Under a static call it fails. -/
theorem evmLog1_exec (sl : MemSlice_u8) (t : UInt256) :
    (Evm_log1 sl t).exec I w =
      if I.perm then
        some (.ok ((), { w with
          logs := w.logs.push ⟨I.codeOwner, #[t], w.memory.readWithPadding sl.ptr.toNat sl.len.toNat⟩ }))
      else some (.error .static) := by
  cases h : I.perm <;> simp [Evm_log1, MemSlice_ptr_u8, MemSlice_len_u8, logData, emit, h]

theorem singleRootBytes_eq (r0 : Bytes) :
    encode_single_root_alloc_Sol_Bytes r0 = (do
      let n ← checkedAdd (UInt256.ofNat 32) r0.size
      let l ← allocation_len n
      let buf ← MemBuffer_new l
      let t ← AbiFrame_tail ⟨buf.ptr, n⟩ (UInt256.ofNat 32)
      let _ ← encode_field_Sol_Bytes r0 ⟨buf.ptr, n⟩ (UInt256.ofNat 0) t
      return buf) := by
  simp only [encode_single_root_alloc_Sol_Bytes, abi_single_root_size_Bytes, abi_field_size_Bytes,
    Bytes_payload_size, Bytes_encoded_size, Bytes_IS_DYNAMIC, abi_single_root_head_size_Bytes,
    abiFieldHeadBytes_eq, Bytes_drop, dealloc_u8, cast_u8_u8, MemBuffer_ptr,
    AbiFrame_from_raw_parts, pure_bind, bind_pure, ite_true]

set_option maxHeartbeats 4000000 in
/-- Std's encoding of one `bytes` value as a call's whole return data: a fresh buffer that holds
    the ABI encoding of the one-field tuple, the offset word and the value's tail. -/
theorem singleRootBytes_exec {b : Bytes} {d : ByteArray} (hb : BytesHolds b d w.memory)
    (hfit : w.memory.size + (abiEncodeBytes [d]).size < UInt256.size) :
    (encode_single_root_alloc_Sol_Bytes b).exec I w =
      if 2 ^ 64 - 1 < (abiEncodeBytes [d]).size then some (.error (.panic 0x41))
      else some (.ok (⟨UInt256.ofNat w.memory.size, UInt256.ofNat (abiEncodeBytes [d]).size,
          UInt256.ofNat (abiEncodeBytes [d]).size⟩,
        { w with memory := w.memory ++ abiEncodeBytes [d] })) := by
  have hn : (abiEncodeBytes [d]).size = 32 + (abiBytesTail d).size := by
    simp [abiEncodeBytes, abiBytesHeads, abiBytesTails, ByteArray.size_append]
  rw [hn] at hfit ⊢
  generalize hs : (abiBytesTail d).size = s at hfit
  have hc : b.size = UInt256.ofNat s := by rw [← hs, ← hb.size, u256_ofNat_toNat]
  have hadd : (checkedAdd (UInt256.ofNat 32) b.size).exec I w =
      some (.ok (UInt256.ofNat (32 + s), w)) := by
    simp [checkedAdd, hc, toNat32, ulit_toNat' s (by omega), show ¬ UInt256.size ≤ 32 + s by omega,
      ofNat_add_ofNat (show 32 + s < UInt256.size by omega)]
  rw [singleRootBytes_eq, exec_bind_ok I w hadd,
    exec_bind_ok I w (allocationLen_exec I w (n := 32 + s) (by omega)), Fe.M.exec_bind,
    memBufferNew_exec I w (by omega), ite_eq_left (show w.memory.size + (32 + s) < UInt256.size from hfit)]
  by_cases hp : 2 ^ 64 - 1 < 32 + s
  · rw [ite_eq_left hp, ite_eq_left hp]
  rw [ite_eq_right hp, ite_eq_right hp]
  dsimp only
  have z0 : ({ w with memory := w.memory ++ zeros (32 + s) } : World).memory =
      w.memory ++ tupleBuf [] 32 32 s := by rw [tupleBuf_nil]
  have st := encodeFieldStep_exec I { w with memory := w.memory ++ zeros (32 + s) }
    hb z0 (n := 32 + s) (h := 0) (k := 32)
    (by rw [tupleBuf_size]; simp [abiBytesTails]) (by rfl) (by simp [abiBytesTails])
    (by rfl) (by omega) (by omega) (by omega)
  rw [exec_bind_ok I _ (abiFrameTail_exec I _ (by omega) (by omega)), exec_bind_ok I _ st,
    Fe.M.exec_pure]
  simp only [List.nil_append, hs, Nat.sub_self, show 32 - 32 = 0 from rfl,
    tupleBuf_full [d] (N := 32) rfl]

set_option maxHeartbeats 4000000 in
/-- `return_value` of a `bytes` value: the call ends with the ABI encoding of the one-field
    tuple, `Panic(0x41)` if it is `2 ^ 64` bytes or more.  It changes memory only. -/
theorem returnBytes_exec {b : Bytes} {d : ByteArray} (hb : BytesHolds b d w.memory)
    (hfit : w.memory.size + (abiEncodeBytes [d]).size < UInt256.size) :
    (Evm_return_value_Sol_Bytes b).exec I w =
      if 2 ^ 64 - 1 < (abiEncodeBytes [d]).size then some (.error (.panic 0x41))
      else some (.error (.stop (abiEncodeBytes [d])
        { w with memory := w.memory ++ abiEncodeBytes [d] })) := by
  simp only [Evm_return_value_Sol_Bytes, Bytes_IS_DYNAMIC, encode_return_alloc_Sol_Bytes,
    const_Bytes, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false, MemBuffer_span_ref,
    MemSlice_from_raw_parts_ref_u8, Evm_return_bytes, Evm_return_data, MemSlice_ptr_u8,
    MemSlice_len_u8, bind_pure]
  rw [Fe.M.exec_bind, singleRootBytes_exec I w hb hfit]
  by_cases hp : 2 ^ 64 - 1 < (abiEncodeBytes [d]).size
  · rw [ite_eq_left hp, ite_eq_left hp]
  rw [ite_eq_right hp, ite_eq_right hp]
  have hpos : 0 < (abiEncodeBytes [d]).size := by
    simp [abiEncodeBytes, abiBytesHeads, ByteArray.size_append]
  simp [returnData, ulit_toNat' w.memory.size (by omega),
    ulit_toNat' (abiEncodeBytes [d]).size (by omega)]
  rw [readWithPadding_tail w.memory (abiEncodeBytes [d]) 0 _ (Nat.add_zero _).symm hpos (by omega),
    Nat.zero_add, byteArray_extract_self]

end FeProofs.Lib
