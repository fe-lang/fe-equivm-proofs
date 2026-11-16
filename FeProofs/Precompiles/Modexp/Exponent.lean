import FeProofs.Precompiles.Modexp.Window
import FeProofs.Precompiles.Modexp.Clz
import FeProofs.Precompiles.LimbArray

/-!
# Modexp: the exponent in memory

`Exponent` holds the exponent's limbs (least significant first), its bit count `total` (eight
per byte of its length) and `top`, the index from the most significant end of its first set bit.
`ExpAt x e total top mem` says that `x` holds the exponent `e` so in the memory `mem`.

- `bit_exec`: `Exponent::bit(i)` reads limb `(total - 1 - i) / 64` raw and gives
  `bitOf e total i`.
- `window_exec`: `Exponent::window(i, width)` gives `win e total i width`: after a zero bit the
  step of one bit, otherwise the window `[i, j)` of at most `width` bits that ends in a set bit
  (`winEnd`), with the index `(d - 1) / 2` of its odd digit `d = digitOf e total i j` in the table
  of odd powers.  `win_odd` and `winEnd_bounds` are what the walks need of it.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- `x` holds the exponent `e` of `total` bits, whose first set bit is `top` from the most
    significant end (`total` when `e` is zero), with its limbs in `mem`. -/
structure ExpAt (x : Exponent) (e total top : ℕ) (mem : ByteArray) : Prop where
  limbs : ∃ ls, ArrayAt x.limbs ls mem ∧ val ls = e ∧ total ≤ 64 * ls.length
  total_eq : x.total = UInt256.ofNat total
  top_eq : x.top = UInt256.ofNat top
  total_lt : total < 2 ^ 64
  e_lt : e < 2 ^ total
  top_def : top = if e = 0 then total else total - 1 - e.log2

theorem ExpAt.top_le {x : Exponent} {e total top : ℕ} {mem : ByteArray}
    (h : ExpAt x e total top mem) : top ≤ total := by
  rw [h.top_def]; split_ifs <;> omega

/-- Below the top the exponent has no set bit. -/
theorem ExpAt.prefix_top {x : Exponent} {e total top : ℕ} {mem : ByteArray}
    (h : ExpAt x e total top mem) : prefixOf e total top = 0 := by
  apply prefixOf_zero
  rw [h.top_def]
  split_ifs with h0
  · rw [h0, Nat.sub_self, pow_zero]; norm_num
  · have hl : e.log2 < total := (Nat.log2_lt h0).mpr h.e_lt
    rw [show total - (total - 1 - e.log2) = e.log2 + 1 by omega]
    exact Nat.lt_log2_self

/-- The top bit is set. -/
theorem ExpAt.bit_top {x : Exponent} {e total top : ℕ} {mem : ByteArray}
    (h : ExpAt x e total top mem) (he : e ≠ 0) : bitOf e total top = 1 := by
  have hl : e.log2 < total := (Nat.log2_lt he).mpr h.e_lt
  rw [bitOf, h.top_def, if_neg he, show total - 1 - (total - 1 - e.log2) = e.log2 by omega]
  have h1 := Nat.lt_log2_self (n := e)
  have h2 := Nat.log2_self_le he
  have hd : e / 2 ^ e.log2 = 1 := Nat.div_eq_of_lt_le (by rw [Nat.one_mul]; exact h2)
    (by rw [show (1 + 1) * 2 ^ e.log2 = 2 ^ (e.log2 + 1) by ring]; exact h1)
  rw [hd]

/-! ## Word operations -/

theorem sub_lit {a b : ℕ} (ha : a < 2 ^ 256) (h : b ≤ a) :
    UInt256.ofNat a - UInt256.ofNat b = UInt256.ofNat (a - b) := by
  apply word_eq_of_toNat
  rw [show UInt256.ofNat a - UInt256.ofNat b = UInt256.sub _ _ from rfl,
    usub_toNat (by rw [toNat_lit ha, toNat_lit (by omega)]; exact h), toNat_lit ha,
    toNat_lit (by omega), toNat_lit (by omega)]

theorem and_lit (a : ℕ) {k : ℕ} (ha : a < 2 ^ 256) (hk : k < 256) :
    UInt256.ofNat a &&& UInt256.ofNat (2 ^ k - 1) = UInt256.ofNat (a % 2 ^ k) := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, toNat_lit ha, toNat_lit (by have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) hk; omega),
    Nat.and_two_pow_sub_one_eq_mod, toNat_lit (lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem shr_lit (a : ℕ) {k : ℕ} (ha : a < 2 ^ 256) (hk : k < 256) :
    UInt256.ofNat a >>> UInt256.ofNat k = UInt256.ofNat (a / 2 ^ k) := by
  apply word_eq_of_toNat
  rw [shiftRight_toNat _ hk, toNat_lit ha, toNat_lit (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem downcast_usize_u64 (a : ℕ) (ha : a < 2 ^ 256) :
    Lib.downcast_truncate_usize_u64 (UInt256.ofNat a) = pure (UInt256.ofNat (a % 2 ^ 64)) := by
  simp only [Lib.downcast_truncate_usize_u64, Lib.usize_to_word, Lib.u64_IS_SIGNED, Lib.u64_MASK,
    Lib.U64_MASK, Lib.u64_from_word, truncate, pure_bind, bind_pure_comp, Bool.false_eq_true,
    if_false, map_pure]
  rw [land_mask_toNat, Nat.mod_mod, toNat_lit ha]

theorem limb_shr (x : Limb) {k : ℕ} (hk : k < 256) :
    x.w >>> UInt256.ofNat k = UInt256.ofNat (x.val / 2 ^ k) :=
  shr_lit _ (lt_trans x.isLt (by norm_num)) hk

theorem and_one (a : ℕ) (ha : a < 2 ^ 256) : UInt256.ofNat a &&& UInt256.ofNat 1 = UInt256.ofNat (a % 2) :=
  and_lit a (k := 1) ha (by norm_num)

/-! ## A bit -/

/-- **`Exponent::bit(i)`**, `i < total`: bit `i` from the most significant end. -/
theorem bit_exec {x : Exponent} {e total top : ℕ} {w : World} (h : ExpAt x e total top w.memory)
    {i : ℕ} (hi : i < total) (I : Env) :
    (Exponent_bit x (UInt256.ofNat i)).exec I w = some (.ok (UInt256.ofNat (bitOf e total i), w)) := by
  obtain ⟨ls, ha, hv, hl⟩ := h.limbs
  have ht := h.total_lt
  have hs := ha.small
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hp : total - 1 - i < 64 * ls.length := by omega
  have hq : (total - 1 - i) / 64 < ls.length := by omega
  have hr : (total - 1 - i) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have haddr : x.limbs.ptr.toNat + 8 * ((total - 1 - i) / 64) < UInt256.size := by
    have := ha.addr_lt hq; omega
  have hld := load_exec ha.limbs hq hs I
  have hb : ls[(total - 1 - i) / 64].val / 2 ^ ((total - 1 - i) % 64) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans (Fin.isLt _) (by norm_num))
  simp only [Exponent_bit, h.total_eq, sub_lit (show total < 2 ^ 256 by omega) (show 1 ≤ total by omega),
    sub_lit (show total - 1 < 2 ^ 256 by omega) (show i ≤ total - 1 by omega),
    show UInt256.ofNat 63 = UInt256.ofNat (2 ^ 6 - 1) from rfl,
    and_lit _ (show total - 1 - i < 2 ^ 256 by omega) (show 6 < 256 by norm_num),
    show (2 : ℕ) ^ 6 = 64 from rfl,
    downcast_usize_u64 _ (show (total - 1 - i) % 64 < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt (show (total - 1 - i) % 64 < 2 ^ 64 by omega), Lib.MemArray_ptr_u64,
    shr_lit _ (show total - 1 - i < 2 ^ 256 by omega) (show 6 < 256 by norm_num),
    Exported.Modexp.limb, pure_bind, limb_eq _ haddr, Fe.M.exec_bind, Fe.M.exec_pure, hld,
    limb_shr _ (show (total - 1 - i) % 64 < 256 by omega), and_one _ hb, downcast_u64_usize]
  rw [← val_bit ls _ hp, hv]
  rfl

/-! ## A window -/

/-- The end of a window: from `k` down, the first end after a set bit. -/
def trimEnd (e total : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if bitOf e total k = 1 then k + 1 else trimEnd e total k

/-- The end of the window from `i` of at most `width` bits. -/
def winEnd (e total i width : ℕ) : ℕ :=
  trimEnd e total (if total - i < width then total else i + width)

/-- `Exponent::window(i, width)`. -/
def win (e total i width : ℕ) : Window :=
  if bitOf e total i = 0 then ⟨UInt256.ofNat (i + 1), UInt256.ofNat 0, false⟩
  else ⟨UInt256.ofNat (winEnd e total i width),
    UInt256.ofNat ((digitOf e total i (winEnd e total i width) - 1) / 2), true⟩

theorem bitOf_lt (e total i : ℕ) : bitOf e total i < 2 := Nat.mod_lt _ (by norm_num)

theorem trimEnd_spec (e total i : ℕ) (hb : bitOf e total i = 1) :
    ∀ k, i < k → i < trimEnd e total k ∧ trimEnd e total k ≤ k ∧
      bitOf e total (trimEnd e total k - 1) = 1
  | 0, h => absurd h (by omega)
  | k + 1, h => by
    rw [trimEnd]
    split_ifs with hk
    · exact ⟨h, le_rfl, by simpa using hk⟩
    · have hki : i < k := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
        · exact h'
        · subst h'; exact absurd hb hk
      obtain ⟨a, b, c⟩ := trimEnd_spec e total i hb k hki
      exact ⟨a, by omega, c⟩

/-- **The window's end**: past `i`, within `width` bits and the exponent, after a set bit. -/
theorem winEnd_bounds (e total i width : ℕ) (hi : i < total) (hw : 1 ≤ width)
    (hb : bitOf e total i = 1) :
    i < winEnd e total i width ∧ winEnd e total i width ≤ total ∧
      winEnd e total i width ≤ i + width ∧ bitOf e total (winEnd e total i width - 1) = 1 := by
  unfold winEnd
  split_ifs with h
  · obtain ⟨a, b, c⟩ := trimEnd_spec e total i hb total hi; exact ⟨a, b, by omega, c⟩
  · obtain ⟨a, b, c⟩ := trimEnd_spec e total i hb (i + width) (by omega); exact ⟨a, by omega, b, c⟩

/-- A digit, one bit longer. -/
theorem digit_succ (e total i k : ℕ) (hik : i ≤ k) (hk : k < total) :
    digitOf e total i (k + 1) = 2 * digitOf e total i k + bitOf e total k := by
  have hb := bitOf_lt e total k
  have hs := bit_step e total k hk
  unfold prefixOf at hs
  unfold digitOf
  rw [hs, show k + 1 - i = (k - i) + 1 by omega, pow_succ]
  generalize e / 2 ^ (total - k) = P
  generalize bitOf e total k = b at hb ⊢
  conv_lhs => rw [← Nat.div_add_mod P (2 ^ (k - i))]
  rw [show 2 * (2 ^ (k - i) * (P / 2 ^ (k - i)) + P % 2 ^ (k - i)) + b =
      (2 * (P % 2 ^ (k - i)) + b) + 2 ^ (k - i) * 2 * (P / 2 ^ (k - i)) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt P (show 0 < 2 ^ (k - i) by positivity)
  omega

/-- A window's digit is odd. -/
theorem digit_odd (e total i j : ℕ) (hij : i < j) (hj : j ≤ total) (hb : bitOf e total (j - 1) = 1) :
    digitOf e total i j % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [digit_succ e total i k (by omega) (by omega), Nat.add_comm, Nat.add_mul_mod_self_left]
  simp only [Nat.add_sub_cancel] at hb
  rw [hb]

theorem digit_lt (e total i j : ℕ) : digitOf e total i j < 2 ^ (j - i) := Nat.mod_lt _ (by positivity)

theorem digit_self (e total i : ℕ) : digitOf e total i i = 0 := by simp [digitOf, Nat.mod_one]

theorem ofNat_eq_iff {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (UInt256.ofNat a = UInt256.ofNat b) = (a = b) := by
  apply propext; constructor
  · intro e; have := congrArg UInt256.toNat e; rwa [toNat_lit ha, toNat_lit hb] at this
  · intro e; rw [e]

theorem shl_or_lit {d b : ℕ} (hd : 2 * d < 2 ^ 256) (hb : b < 2) :
    UInt256.ofNat d <<< UInt256.ofNat 1 ||| UInt256.ofNat b = UInt256.ofNat (2 * d + b) := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, shiftLeft_toNat _ (by norm_num) (by rw [toNat_lit (by omega)]; omega),
    toNat_lit (by omega), toNat_lit (by omega), toNat_lit (by omega), pow_one,
    ← Nat.two_pow_add_eq_or_of_lt (i := 1) (by simpa using hb), pow_one]

theorem has_uu {i j k : ℕ} (hi : i < 2 ^ 256) (hj : j < 2 ^ 256) (hk : k < 2 ^ 256) :
    Lib.Range_Unknown_Unknown_has ⟨UInt256.ofNat i, UInt256.ofNat j⟩ (UInt256.ofNat k) =
      pure (decide (i ≤ k ∧ k < j)) := by
  simp only [Lib.Range_Unknown_Unknown_has, range_has_eq hk hi hj, bind_pure]

/-- The digit loop of `Exponent::window`, from bit `k` of the window `[i, j)`. -/
theorem digit_loop {x : Exponent} {e total top : ℕ} {w : World} (h : ExpAt x e total top w.memory)
    (I : Env) {i j : ℕ} (hij : i < j) (hj : j ≤ total) (hw : j ≤ i + 64)
    (hb : bitOf e total (j - 1) = 1) :
    ∀ n k, k + n = j → i ≤ k →
      (Exponent_window.loop.loop_1 x (UInt256.ofNat j) (UInt256.ofNat (digitOf e total i k))
          ⟨UInt256.ofNat i, UInt256.ofNat j⟩ (UInt256.ofNat k)).exec I w =
        some (.ok (⟨UInt256.ofNat j, UInt256.ofNat ((digitOf e total i j - 1) / 2), true⟩, w))
  | 0, k, hk, hik => by
    have ht := h.total_lt
    rw [Nat.add_zero] at hk
    subst hk
    have hd := digit_lt e total i k
    have hodd := digit_odd e total i k (by omega) hj hb
    have h64 : 2 ^ (k - i) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Exponent_window.loop.loop_1.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) (show k < 2 ^ 256 by omega)
      (show k < 2 ^ 256 by omega), show (i ≤ k ∧ k < k) = False from
      eq_false (by omega), decide_false, Bool.false_eq_true, if_false, pure_bind,
      sub_lit (show digitOf e total i k < 2 ^ 256 by omega) (show 1 ≤ digitOf e total i k by omega),
      checkedDiv_lit (show digitOf e total i k - 1 < 2 ^ 256 by omega) (show 2 < 2 ^ 256 by norm_num)
        (by norm_num), Fe.M.exec_pure]
  | n + 1, k, hk, hik => by
    have ht := h.total_lt
    have hd := digit_lt e total i k
    have h64 : 2 ^ (k - i) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Exponent_window.loop.loop_1.eq_1]
    simp only [has_uu (show i < 2 ^ 256 by omega) (show j < 2 ^ 256 by omega)
      (show k < 2 ^ 256 by omega), show (i ≤ k ∧ k < j) = True from eq_true (by omega),
      decide_true, if_true, Lib.Range_Unknown_Unknown_at, Lib.Range_Unknown_Unknown_next,
      pure_bind, Fe.M.exec_bind, bit_exec h (show k < total by omega),
      shl_or_lit (show 2 * digitOf e total i k < 2 ^ 256 by omega) (bitOf_lt e total k),
      ← digit_succ e total i k hik (by omega), next_eq (show k + 1 < 2 ^ 256 by omega)]
    exact digit_loop h I hij hj hw hb n (k + 1) (by omega) (by omega)

/-- The loop of `Exponent::window` that trims the window's end to a set bit. -/
theorem trim_loop {x : Exponent} {e total top : ℕ} {w : World} (h : ExpAt x e total top w.memory)
    (I : Env) {i : ℕ} (hb : bitOf e total i = 1) (r1 : UInt256) (r2 : Lib.Range_Unknown_Unknown) :
    ∀ k, i < k → k ≤ total → k ≤ i + 64 →
      (Exponent_window.loop x (UInt256.ofNat i) (UInt256.ofNat k) r1 r2).exec I w =
        some (.ok (⟨UInt256.ofNat (trimEnd e total k),
          UInt256.ofNat ((digitOf e total i (trimEnd e total k) - 1) / 2), true⟩, w))
  | 0, hk, _, _ => absurd hk (by omega)
  | k + 1, hk, hkt, hkw => by
    have ht := h.total_lt
    rw [Exponent_window.loop.eq_1]
    simp only [sub_lit (show k + 1 < 2 ^ 256 by omega) (show 1 ≤ k + 1 by omega),
      Nat.add_sub_cancel, Fe.M.exec_bind, bit_exec h (show k < total by omega),
      ofNat_eq_iff (show bitOf e total k < 2 ^ 256 by have := bitOf_lt e total k; omega)
        (show 0 < 2 ^ 256 by norm_num), trimEnd]
    by_cases hk1 : bitOf e total k = 1
    · simp only [hk1, show (1 = 0) = False from eq_false (by omega), decide_false,
        Bool.false_eq_true, if_false, if_true, Lib.Range_Unknown_Unknown_start, pure_bind]
      rw [← digit_self e total i]
      exact digit_loop h I hk hkt hkw (by simpa using hk1) (k + 1 - i) i (by omega) le_rfl
    · have h0 : bitOf e total k = 0 := by have := bitOf_lt e total k; omega
      have hik : i < k := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h' | h'
        · exact h'
        · subst h'; exact absurd hb hk1
      simp only [h0, decide_true, if_true]
      exact trim_loop h I hb r1 r2 k hik (by omega) (by omega)

/-- **`Exponent::window(i, width)`**, for `i < total` and a width from 1 to 64. -/
theorem window_exec {x : Exponent} {e total top : ℕ} {w : World} (h : ExpAt x e total top w.memory)
    (I : Env) {i width : ℕ} (hi : i < total) (hw : 1 ≤ width ∧ width ≤ 64) :
    (Exponent_window x (UInt256.ofNat i) (UInt256.ofNat width)).exec I w =
      some (.ok (win e total i width, w)) := by
  have ht := h.total_lt
  simp only [Exponent_window, Fe.M.exec_bind, bit_exec h hi,
    ofNat_eq_iff (show bitOf e total i < 2 ^ 256 by have := bitOf_lt e total i; omega)
      (show 0 < 2 ^ 256 by norm_num), h.total_eq,
    sub_lit (show total < 2 ^ 256 by omega) hi.le, toNat_lit (show total - i < 2 ^ 256 by omega),
    toNat_lit (show width < 2 ^ 256 by omega), win]
  by_cases h0 : bitOf e total i = 0
  · simp only [h0, decide_true, if_true, Fe.EVM.ofNat_add_ofNat (show i + 1 < UInt256.size by
      unfold UInt256.size; omega), Fe.M.exec_pure]
  · have hb : bitOf e total i = 1 := by have := bitOf_lt e total i; omega
    simp only [h0, decide_false, Bool.false_eq_true, if_false]
    unfold winEnd
    by_cases hc : total - i < width
    · simp only [hc, decide_true, if_true]
      exact trim_loop h I hb _ _ total hi le_rfl (by omega)
    · simp only [hc, decide_false, Bool.false_eq_true, if_false, Fe.EVM.ofNat_add_ofNat
        (show i + width < UInt256.size by unfold UInt256.size; omega)]
      exact trim_loop h I hb _ _ (i + width) (by omega) (by omega) (by omega)

end FeProofs.Modexp
