import FeProofs.Precompiles.Ripemd160.Words
import FeProofs.Precompiles.Ripemd160.Hash
import FeProofs.Precompiles.Blake2F.Rounds
import FeProofs.Precompiles.Blake2F.Bytes

/-!
# Ripemd160: `padded_block`

On a buffer holding the message `d`, the exported `padded_block_MemBuffer` at block `i` of
`blocksOf d.size` returns block `i` of EVMLean's padded message (`padded_block_exec`): the
message bytes, `0x80` after them, zeros, and in the last block the bit count, little-endian.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ripemd160

open FeProofs.Precompiles
open Precompiles.Exported.Ripemd160
open FeProofs.Blake2F (getElem!_ofFn set!_ofFn replicate_ofFn has8 byte_get)

/-- The padded message's byte at `p` before the bit count is written. -/
def msgByte (d : ByteArray) (p : ℕ) : UInt8 :=
  if p < d.size then d[p]! else if p = d.size then 0x80 else 0

theorem lw32_byte (x : UInt8) : lw32 x.toUInt32 = UInt256.ofNat x.toNat := by
  simp [lw32]

theorem has64 (r : Range_Known_0_Known_64) {k : ℕ} (hk : k < 2 ^ 256) :
    Range_has_0_64 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 64)) := by
  simp only [Lib.Range_has_0_64, range_has_eq (lo := 0) (hi := 64) hk (by decide) (by decide),
    bind_pure]

theorem downcast_u8 (x : UInt256) :
    downcast_truncate_u64_u8 x = pure (UInt256.ofNat (x.toNat % 256)) := by
  simp only [Lib.downcast_truncate_u64_u8, Lib.u64_to_word, Lib.u8_IS_SIGNED, Lib.u8_MASK,
    Lib.U8_MASK, Lib.u8_from_word, truncate, pure_bind, Bool.false_eq_true, if_false]
  congr 2
  change (UInt256.land x _).toNat % 2 ^ 8 = _
  rw [uland_toNat, toNat_lit (by decide), show (255 : ℕ) = 2 ^ 8 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem downcast_u64 (x : UInt256) :
    downcast_unchecked_usize_u64 x = pure (UInt256.ofNat (x.toNat % 2 ^ 64)) := by
  simp only [Lib.downcast_unchecked_usize_u64, Lib.usize_to_word, Lib.u64_from_word, truncate,
    pure_bind]

theorem byte_of_low (N j : ℕ) (hj : j < 8) : N % 2 ^ 64 / 2 ^ (j * 8) % 256 = N / 2 ^ (8 * j) % 256 := by
  have e : 2 ^ 64 = 2 ^ (j * 8) * 2 ^ (64 - j * 8) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, show j * 8 = 8 * j by ring,
    Nat.mod_mod_of_dvd _ (show 256 ∣ 2 ^ (64 - 8 * j) from by
      rw [show 64 - 8 * j = 8 + (56 - 8 * j) by omega, pow_add]; exact dvd_mul_right _ _)]

/-- The loop writing the bit count `N` into bytes `56 …` of the last block, from byte `j`. -/
theorem bits_loop (b13 : Vector UInt256 64 → Range_Known_0_Known_64 → Range_Known_0_Known_8 →
      FeM (Vector UInt256 64)) (hb13 : ∀ r0 r1 r2, b13 r0 r1 r2 = pure r0) (N : ℕ) (g : ℕ → UInt8)
    r1 r2 :
    ∀ n j, j + n = 8 →
      padded_block_MemBuffer.loop.loop_1 b13 (UInt256.ofNat (N % 2 ^ 64))
          (Vector.ofFn fun k : Fin 64 => lw32 (if 56 ≤ k.val ∧ k.val < 56 + j then
            (N >>> (8 * (k.val - 56))).toUInt8 else g k).toUInt32) r1 r2 (UInt256.ofNat j) =
        pure (Vector.ofFn fun k : Fin 64 => lw32 (if 56 ≤ k.val then
          (N >>> (8 * (k.val - 56))).toUInt8 else g k).toUInt32)
  | 0, j, h => by
    subst h
    rw [padded_block_MemBuffer.loop.loop_1.eq_1]
    simp only [has8 _ (show 0 + 8 < 2 ^ 256 by decide), hb13]
    simp only [show ¬ (0 ≤ 0 + 8 ∧ 0 + 8 < 8) by omega, decide_false, pure_bind,
      Bool.false_eq_true, ↓reduceIte]
    congr 2
    funext k
    have := k.isLt
    by_cases hk : 56 ≤ k.val
    · rw [if_pos ⟨hk, by omega⟩, if_pos hk]
    · rw [if_neg (fun h => hk h.1), if_neg hk]
  | n + 1, j, h => by
    rw [padded_block_MemBuffer.loop.loop_1.eq_1]
    have hN : N % 2 ^ 64 < 2 ^ 256 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    simp only [has8 _ (show j < 2 ^ 256 by omega),
      decide_eq_true (show 0 ≤ j ∧ j < 8 from ⟨by omega, by omega⟩), ↓reduceIte,
      Lib.Range_at_0_8, Lib.Range_next_0_8, pure_bind,
      Fe.EVM.ofNat_mul_ofNat (show j < UInt256.size by unfold UInt256.size; omega)
        (show 8 < UInt256.size by decide) (show j * 8 < UInt256.size by unfold UInt256.size; omega),
      downcast_u64, toNat_lit (show j * 8 < 2 ^ 256 by omega),
      Nat.mod_eq_of_lt (show j * 8 < 2 ^ 64 by omega), ushr_eq hN (show j * 8 < 256 by omega),
      downcast_u8, toNat_lit (lt_of_le_of_lt (Nat.div_le_self _ _) hN), byte_of_low N j (by omega),
      Fe.EVM.ofNat_add_ofNat (show 56 + j < UInt256.size by unfold UInt256.size; omega),
      checkIndex_lit (show 56 + j < 64 by omega) (by decide), toNat_lit (show 56 + j < 2 ^ 256 by omega),
      set!_ofFn, next_eq (show j + 1 < 2 ^ 256 by omega)]
    have e : (fun k : Fin 64 => if k.val = 56 + j then UInt256.ofNat (N / 2 ^ (8 * j) % 256) else
        lw32 (if 56 ≤ k.val ∧ k.val < 56 + j then (N >>> (8 * (k.val - 56))).toUInt8
          else g k).toUInt32) =
        fun k : Fin 64 => lw32 (if 56 ≤ k.val ∧ k.val < 56 + (j + 1) then
          (N >>> (8 * (k.val - 56))).toUInt8 else g k).toUInt32 := by
      funext k
      by_cases hk : k.val = 56 + j
      · rw [if_pos hk, if_pos (by omega), lw32_byte, hk, Nat.add_sub_cancel_left]
        congr 1
        simp [Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
      · rw [if_neg hk]
        congr 3
        apply propext; omega
    rw [e]
    exact bits_loop b13 hb13 N g r1 r2 n (j + 1) (by omega)

theorem ofNat_eq_iff {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.ofNat a = UInt256.ofNat b ↔ a = b :=
  ⟨fun e => by have := congrArg UInt256.toNat e; rwa [toNat_lit ha, toNat_lit hb] at this,
   fun e => e ▸ rfl⟩

/-- The loop copying the message bytes and the `0x80` into block `i`, from byte `k`. -/
theorem msg_loop {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) {i Bl : ℕ} (hi : i * 64 + 64 < 2 ^ 256) r1 r2 :
    ∀ n k, k + n = 64 →
      (padded_block_MemBuffer.loop b (UInt256.ofNat 0) (UInt256.ofNat d.size) (UInt256.ofNat i)
          (UInt256.ofNat Bl) (UInt256.ofNat (i * 64))
          (Vector.ofFn fun k' : Fin 64 =>
            lw32 (if k'.val < k then msgByte d (i * 64 + k'.val) else 0).toUInt32)
          r1 r2 (UInt256.ofNat k)).exec I w =
        (padded_block_MemBuffer.loop b (UInt256.ofNat 0) (UInt256.ofNat d.size) (UInt256.ofNat i)
          (UInt256.ofNat Bl) (UInt256.ofNat (i * 64))
          (Vector.ofFn fun k' : Fin 64 => lw32 (msgByte d (i * 64 + k'.val)).toUInt32)
          r1 r2 (UInt256.ofNat 64)).exec I w
  | 0, k, hk => by
    subst hk
    congr 3
    funext k'
    rw [if_pos (by omega)]
  | n + 1, k, hk => by
    have hs := h.small
    have hb := h.bound
    have hds : d.size < 2 ^ 256 := by unfold UInt256.size at hs; omega
    have hp : i * 64 + k < 2 ^ 256 := by omega
    rw [padded_block_MemBuffer.loop.eq_1]
    simp only [has64 _ (show k < 2 ^ 256 by omega),
      decide_eq_true (show 0 ≤ k ∧ k < 64 from ⟨by omega, by omega⟩), ↓reduceIte,
      Lib.Range_at_0_64, Lib.Range_next_0_64, pure_bind,
      Fe.EVM.ofNat_add_ofNat (show i * 64 + k < UInt256.size by unfold UInt256.size; omega),
      Fe.EVM.ofNat_add_ofNat (show 0 + (i * 64 + k) < UInt256.size by unfold UInt256.size; omega),
      Nat.zero_add, toNat_lit hp, toNat_lit hds, next_eq (show k + 1 < 2 ^ 256 by omega),
      checkIndex_lit (show k < 64 by omega) (by decide), toNat_lit (show k < 2 ^ 256 by omega),
      ofNat_eq_iff hp hds, set!_ofFn]
    have ih := msg_loop (I := I) (Bl := Bl) h hi r1 r2 n (k + 1) (by omega)
    by_cases h1 : i * 64 + k < d.size
    · simp only [decide_eq_true h1, ↓reduceIte]
      rw [Fe.M.exec_bind, byte_exec h h1]
      dsimp only
      rw [← ih]
      congr 3
      funext k'
      by_cases e : k'.val = k
      · rw [if_pos e, if_pos (by omega), e, msgByte, if_pos h1, lw32_byte, byte_get]
      · rw [if_neg e]
        congr 3
        apply propext; omega
    · simp only [decide_eq_false h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : i * 64 + k = d.size
      · simp only [decide_eq_true h2, ↓reduceIte]
        rw [← ih]
        congr 3
        funext k'
        by_cases e : k'.val = k
        · rw [if_pos e, if_pos (by omega), e, msgByte, if_neg h1, if_pos h2]
          rfl
        · rw [if_neg e]
          congr 3
          apply propext; omega
      · simp only [decide_eq_false h2, Bool.false_eq_true, ↓reduceIte]
        rw [← ih]
        congr 3
        funext k'
        by_cases e : k'.val = k
        · rw [if_neg (by omega), if_pos (by omega), e, msgByte, if_neg h1, if_neg h2]
        · by_cases h3 : k'.val < k
          · rw [if_pos h3, if_pos (by omega)]
          · rw [if_neg h3, if_neg (by omega)]

theorem blocksOf_pos (n : ℕ) : 0 < blocksOf n := by unfold blocksOf; omega

/-- **`padded_block`**: block `i` of the padded message, for every block. -/
theorem padded_block_exec {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) (hn : d.size < 2 ^ 64) {i : ℕ} (hi : i < blocksOf d.size) :
    (padded_block_MemBuffer b (UInt256.ofNat 0) (UInt256.ofNat d.size) (UInt256.ofNat i)
        (UInt256.ofNat (blocksOf d.size))).exec I w = some (.ok (toBlk (blockB d i), w)) := by
  have hB : blocksOf d.size * 64 ≤ d.size + 72 := by unfold blocksOf; omega
  have hi64 : i * 64 + 64 < 2 ^ 256 := by omega
  have hBl : blocksOf d.size < 2 ^ 256 := by omega
  unfold padded_block_MemBuffer
  simp only [Lib.Range_start_0_64, pure_bind,
    Fe.EVM.ofNat_mul_ofNat (show i < UInt256.size by unfold UInt256.size; omega)
      (show 64 < UInt256.size by decide) (show i * 64 < UInt256.size by unfold UInt256.size; omega)]
  have e0 : Vector.replicate 64 (UInt256.ofNat 0) = Vector.ofFn fun k' : Fin 64 =>
      lw32 (if k'.val < 0 then msgByte d (i * 64 + k'.val) else 0).toUInt32 := by
    rw [replicate_ofFn]; rfl
  rw [e0, msg_loop h hi64 _ _ 64 0 rfl, padded_block_MemBuffer.loop.eq_1]
  simp only [has64 _ (show 64 < 2 ^ 256 by decide), show ¬ (0 ≤ 64 ∧ 64 < 64) by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hsub : UInt256.ofNat (blocksOf d.size) - UInt256.ofNat 1 =
      UInt256.ofNat (blocksOf d.size - 1) := by
    apply word_eq_of_toNat
    have := blocksOf_pos d.size
    change (UInt256.sub _ _).toNat = _
    rw [usub_toNat (by rw [toNat_lit hBl, toNat_lit (by decide)]; omega),
      toNat_lit hBl, toNat_lit (by decide), toNat_lit (by omega)]
  rw [hsub]
  by_cases hl : i = blocksOf d.size - 1
  · simp only [hl, decide_true, ↓reduceIte,
      Fe.EVM.ofNat_mul_ofNat (show d.size < UInt256.size by unfold UInt256.size; omega)
        (show 8 < UInt256.size by decide) (show d.size * 8 < UInt256.size by unfold UInt256.size; omega),
      downcast_u64, toNat_lit (show d.size * 8 < 2 ^ 256 by omega), Lib.Range_start_0_8, pure_bind]
    subst hl
    have e1 : (Vector.ofFn fun k' : Fin 64 =>
        lw32 (msgByte d ((blocksOf d.size - 1) * 64 + k'.val)).toUInt32) =
        Vector.ofFn fun k : Fin 64 => lw32 (if 56 ≤ k.val ∧ k.val < 56 + 0 then
          ((d.size * 8) >>> (8 * (k.val - 56))).toUInt8
          else msgByte d ((blocksOf d.size - 1) * 64 + k)).toUInt32 := by
      congr 1; funext k; rw [if_neg (by omega)]
    have hb := bits_loop (fun r0 _ _ => pure r0) (fun _ _ _ => rfl) (d.size * 8)
      (fun p => msgByte d ((blocksOf d.size - 1) * 64 + p)) ⟨(), ()⟩ ⟨(), ()⟩ 8 0 rfl
    simp only at hb
    rw [e1, hb, Fe.M.exec_pure]
    have hblk : toBlk (blockB d (blocksOf d.size - 1)) = Vector.ofFn fun k : Fin 64 =>
        lw32 (if 56 ≤ k.val then ((d.size * 8) >>> (8 * (k.val - 56))).toUInt8
          else msgByte d ((blocksOf d.size - 1) * 64 + k)).toUInt32 := by
      unfold toBlk
      congr 1
      funext k
      have := k.isLt
      have hB1 := blocksOf_pos d.size
      have hz := zeros_eq d.size
      simp only [blockB, padByte, msgByte,
        show 64 * (blocksOf d.size - 1) + k.val = (blocksOf d.size - 1) * 64 + k.val by ring]
      by_cases h56 : 56 ≤ k.val
      · rw [if_pos h56, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show (blocksOf d.size - 1) * 64 + k.val - (64 * blocksOf d.size - 8) = k.val - 56 by omega,
          Nat.mul_comm 8 d.size]
      · rw [if_neg h56]
        split_ifs <;> first | rfl | omega
    rw [hblk]
  · simp only [decide_eq_false (show ¬ UInt256.ofNat i = UInt256.ofNat (blocksOf d.size - 1) from
      fun e => hl ((ofNat_eq_iff (by omega) (by omega)).mp e)), Bool.false_eq_true, ↓reduceIte,
      Fe.M.exec_pure]
    have hblk : toBlk (blockB d i) = Vector.ofFn fun k : Fin 64 =>
        lw32 (msgByte d (i * 64 + k.val)).toUInt32 := by
      unfold toBlk
      congr 1
      funext k
      have := k.isLt
      have hlt : i * 64 + k.val < 64 * blocksOf d.size - 8 := by omega
      simp only [blockB, padByte, msgByte, show 64 * i + k.val = i * 64 + k.val by ring]
      split_ifs <;> rfl
    rw [hblk]

end FeProofs.Ripemd160
