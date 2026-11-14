import FeProofs.Precompiles.Buffer
import Ethereum.BLAKE2

/-!
# Blake2F: input words

EVMLean's `BLAKE2.word d j` is the little-endian number of the eight bytes of `d` from `j`
(`word_toNat`), which is what `MemBuffer_lane_at` returns at `j` (`lane_exec`, `lane_word`).
-/

namespace FeProofs.Blake2F

open FeProofs.Precompiles Reasoning.Theory

/-- The byte of a byte array at `i`, as `byteAt` reads it. -/
theorem byte_get (d : ByteArray) (i : ℕ) : d[i]!.toNat = byteAt d i := by
  unfold byteAt
  rw [byteArray_toList_eq, List.getD_eq_getElem?_getD]
  by_cases h : i < d.size
  · rw [getElem!_pos d i h, List.getElem?_eq_getElem (by simpa using h)]
    simp
    rfl
  · rw [getElem!_neg d i h, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem or_step (x : UInt64) (b : UInt8) {k : ℕ} (hk : k < 8) (hx : x.toNat < 2 ^ (8 * k)) :
    (x ||| b.toUInt64 <<< (UInt64.ofNat (8 * k))).toNat = x.toNat + b.toNat * 2 ^ (8 * k) := by
  have hb := b.toNat_lt
  have h8 : (UInt64.ofNat (8 * k)).toNat = 8 * k := by rw [UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h8, Nat.mod_eq_of_lt (show 8 * k < 64 by omega),
    UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  have hlt : b.toNat * 2 ^ (8 * k) < 2 ^ 64 := by
    calc b.toNat * 2 ^ (8 * k) < 2 ^ 8 * 2 ^ (8 * k) := Nat.mul_lt_mul_of_pos_right (by simpa using hb) (by positivity)
      _ = 2 ^ (8 * k + 8) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt hlt, Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  ring

/-- The little-endian number of the `n` bytes of `d` from `j`. -/
def leAt (d : ByteArray) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => leAt d j n + byteAt d (j + n) * 2 ^ (8 * n)

theorem word_toNat (d : ByteArray) (j : ℕ) :
    (Ethereum.BLAKE2.word d j).toNat = be8 (byteAt d (j + 7)) (byteAt d (j + 6)) (byteAt d (j + 5))
      (byteAt d (j + 4)) (byteAt d (j + 3)) (byteAt d (j + 2)) (byteAt d (j + 1)) (byteAt d j) := by
  have key : ∀ n ≤ 8, ((List.range n).foldl (init := (0 : UInt64)) fun w k =>
      w ||| (d[j + k]!.toUInt64 <<< (8 * k).toUInt64)).toNat = leAt d j n ∧ leAt d j n < 2 ^ (8 * n) := by
    intro n hn
    induction n with
    | zero => simp [leAt]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hb := byteAt_lt d (j + n)
      refine ⟨?_, ?_⟩
      · rw [show (8 * n).toUInt64 = UInt64.ofNat (8 * n) from rfl, or_step _ _ (by omega) (h1 ▸ h2), h1,
          byte_get, leAt]
      · rw [leAt, show 8 * (n + 1) = 8 * n + 8 by ring, pow_add]
        have : leAt d j n + byteAt d (j + n) * 2 ^ (8 * n) < 2 ^ (8 * n) * 256 := by
          have : byteAt d (j + n) * 2 ^ (8 * n) ≤ 255 * 2 ^ (8 * n) := Nat.mul_le_mul_right _ (by omega)
          omega
        simpa using this
  rw [Ethereum.BLAKE2.word, (key 8 le_rfl).1]
  simp only [leAt, be8]
  ring_nf

theorem lane_word (d : ByteArray) (j : ℕ) :
    Fe.EVM.IntTy.swapBytes (.u 64) (Ethereum.UInt256.ofNat (beAt d j 8)) =
      Ethereum.UInt256.ofNat (Ethereum.BLAKE2.word d j).toNat := by
  have e : beAt d j 8 = be8 (byteAt d j) (byteAt d (j + 1)) (byteAt d (j + 2))
      (byteAt d (j + 3)) (byteAt d (j + 4)) (byteAt d (j + 5)) (byteAt d (j + 6))
      (byteAt d (j + 7)) := by simp [beAt, be8]
  have h := byteAt_lt d
  rw [e, swap_be8 (h _) (h _) (h _) (h _) (h _) (h _) (h _) (h _), word_toNat]

end FeProofs.Blake2F
