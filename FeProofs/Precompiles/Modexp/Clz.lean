import FeProofs.Precompiles.Modexp.Ops

/-!
# Modexp: `leading_zeros` is EVMLean's `clz`

The exporter prints `leading_zeros` of a `u256` as `IntTy.leadingZeros (.u 256)` of the Fe
model: the length of the run of zero bits from the top.  `leadingZeros_eq_clz` shows it is
EVMLean's `UInt256.clz`, `255 - log2 x` for `x ≠ 0` and `256` for `0`, so that `Exponent::try_read`
(the exponent's top set bit) and `Small::r2` (the modulus's top bit) can use `clz`.  The fact is
about the Fe model and EVMLean together; EVMLean has no lemma relating its `clz` to a bit scan.
-/

open Ethereum Fe Fe.EVM

namespace FeProofs.Modexp

/-- The run of `p` from `s` over `range' s n` has length `k` when `p` holds below `s + k` and
    fails at `s + k`. -/
theorem takeWhile_range'_length (p : ℕ → Bool) :
    ∀ n s k, k ≤ n → (∀ i < k, p (s + i) = true) → (k < n → p (s + k) = false) →
      ((List.range' s n).takeWhile p).length = k
  | 0, s, k, hk, _, _ => by simp; omega
  | n + 1, s, k, hk, hlt, hstop => by
    rw [List.range'_succ]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have := hstop (by omega)
      simp only [Nat.add_zero] at this
      simp [this]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hs := hlt 0 (by omega)
      simp only [Nat.add_zero] at hs
      rw [List.takeWhile_cons, if_pos hs, List.length_cons]
      congr 1
      exact takeWhile_range'_length p n (s + 1) k' (by omega)
        (fun i hi => by rw [show s + 1 + i = s + (i + 1) by omega]; exact hlt _ (by omega))
        (fun h => by rw [show s + 1 + k' = s + (k' + 1) by omega]; exact hstop (by omega))

/-- **`leading_zeros` at `u256` is `clz`.** -/
theorem leadingZeros_eq_clz (x : UInt256) : IntTy.leadingZeros (.u 256) x = UInt256.clz x := by
  unfold IntTy.leadingZeros UInt256.clz
  congr 1
  simp only [IntTy.bits, IntTy.pattern]
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [Nat.mod_eq_of_lt hx, List.range_eq_range']
  split_ifs with h0
  · apply takeWhile_range'_length _ _ _ _ le_rfl
    · intro i hi; simp [h0]
    · intro h; omega
  · have hl : x.toNat.log2 < 256 := Nat.log2_lt h0 |>.mpr hx
    apply takeWhile_range'_length _ _ _ _ (by omega)
    · intro i hi
      simp only [Nat.zero_add, Bool.not_eq_true']
      apply Nat.testBit_eq_false_of_lt
      calc x.toNat < 2 ^ (x.toNat.log2 + 1) := Nat.lt_log2_self
        _ ≤ 2 ^ (256 - 1 - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · intro _
      simp only [Nat.zero_add, Bool.not_eq_false']
      rw [show 256 - 1 - (255 - x.toNat.log2) = x.toNat.log2 by omega]
      exact Nat.testBit_log2 h0

end FeProofs.Modexp
