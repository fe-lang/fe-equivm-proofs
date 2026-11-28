import Fe.Sonatina.Stage3.Place.Check
import Fe.Sonatina.Steps.SchemasPair
import Reasoning.Memory

/-!
# Words: H's operations and the machine's agree on the words of their operands

The machine IR computes on words, H on values whose word (`State.word`) depends on the address
words of their origins.  Where the proof has chosen H's address words equal to the machine's
(PLAN §6), the machine's result is the word of H's.  This file proves it for each operation the
translation check accepts (`Place/Lower.lean`):

- `binVal_word`: the word of `binVal st op x y` is `op.eval` at `x`'s width on the operands'
  words, whichever origin-keeping rule (`ptrBin`) H applies.
- `BinOp.okI1_eval`, `CmpOp.okI1_eval`: the operations accepted at `i1` do not depend on the
  width.
- `castVal_word`: a cast's word is its operand's low `k` bits, `k` as `castKeep` gives it (the
  alias at 256, the `and` mask below), and the result has the target type.
- `mallocSize_word`: the machine's `and (add n 31) -32` is `align32 n` when `n + 31` does not
  wrap.
- `shift_bytes`: the word of 32 bytes shifted right by `8 (32 - n)` is the big-endian number of
  its first `n` bytes (`evm_mload_bytes`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H

/-- `2 ^ 256`. -/
abbrev W : Nat := 2 ^ 256

theorem wrap_nat (bits n : Nat) : wrap bits (n : Int) = n % 2 ^ bits := by
  unfold wrap
  rw [show ((2 : Int) ^ bits) = ((2 ^ bits : Nat) : Int) by push_cast; rfl, ← Int.natCast_emod,
    Int.toNat_natCast]

theorem wrap_sub' (X k : Nat) : wrap 256 ((X : Int) - k) = (X + (W - k % W)) % W := by
  unfold wrap
  have hlt : k % W < W := Nat.mod_lt _ (by positivity)
  rw [← Int.toNat_natCast ((X + (W - k % W)) % W)]
  congr 1
  push_cast [Nat.cast_sub hlt.le]
  simp only [W] at *
  omega

theorem wrap_sub (A o k : Nat) :
    (A + (o + (W - k % W)) % W) % W = wrap 256 (((A + o) % W : Nat) - (k : Int)) := by
  rw [wrap_sub']
  simp only [W]
  omega

theorem wrap_add (A o k : Nat) :
    (A + (o + k) % W) % W = wrap 256 ((((A + o) % W : Nat) : Int) + (k : Int)) := by
  rw [← Nat.cast_add, wrap_nat]
  simp only [W]
  omega

theorem word_ptr (st : State) (b o : Nat) : st.word (.ptr b o) = (st.addrOf b + o) % W := rfl
theorem word_int (st : State) (bits n : Nat) : st.word (.int bits n) = n := rfl

/-- `binVal` with the pointer first. -/
theorem ptrBin_first_word (st : State) (op : BinOp) (b o k : Nat) :
    st.word ((ptrBin op b o k true).getD (.int 256 (op.eval 256 ((st.addrOf b + o) % W) k))) =
      op.eval 256 ((st.addrOf b + o) % W) k := by
  cases op <;> simp only [ptrBin, Option.getD_some, Option.getD_none, word_int, word_ptr]
  · exact wrap_add _ _ _
  · exact wrap_sub _ _ _
  all_goals first
    | rfl
    | (split
       · next hk => subst hk; simp only [Option.getD_some, word_ptr, BinOp.eval]
                    first | rw [Nat.or_zero] | rw [Nat.xor_zero]
                          | rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
       · rfl)

/-- `binVal` with the pointer second. -/
theorem ptrBin_second_word (st : State) (op : BinOp) (b o k : Nat) :
    st.word ((ptrBin op b o k false).getD (.int 256 (op.eval 256 k ((st.addrOf b + o) % W)))) =
      op.eval 256 k ((st.addrOf b + o) % W) := by
  cases op <;> simp only [ptrBin, Option.getD_some, Option.getD_none, word_int, word_ptr,
    Bool.false_eq_true, if_false]
  · show (st.addrOf b + (o + k) % W) % W = wrap 256 (((k + (st.addrOf b + o) % W : Nat)) : Int)
    rw [wrap_nat]; simp only [W]; omega
  all_goals first
    | rfl
    | (split
       · next hk => subst hk; simp only [Option.getD_some, word_ptr, BinOp.eval]
                    first | rw [Nat.zero_or] | rw [Nat.zero_xor]
                          | rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
       · rfl)

/-- The word of a binary operation's result is the operation on the operands' words, at the
    first operand's width. -/
theorem binVal_word {st : State} {op : BinOp} {x y v : H.Val} (h : binVal st op x y = some v) :
    st.word v = op.eval x.bits (st.word x) (st.word y) := by
  unfold binVal at h
  split at h
  · cases h
  · next hg =>
    match x, y, h with
    | .int bits a, .int _ b, h => cases h; rfl
    | .ptr b o, .int _ k, h => cases h; exact ptrBin_first_word st op b o k
    | .int bits k, .ptr b o, h =>
      have hb : bits = 256 := by
        simp only [H.Val.bits, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hg
        exact hg.2
      subst hb; cases h; exact ptrBin_second_word st op b o k
    | .ptr _ _, .ptr _ _, h => cases h; rfl

/-- The binary operations accepted at `i1` give the same at every width. -/
theorem BinOp.okI1_eval {op : BinOp} (h : op.okI1 = true) (n m a b : Nat) :
    op.eval n a b = op.eval m a b := by
  cases op <;> simp [BinOp.okI1] at h <;> rfl

/-- The comparisons accepted on `i1` give the same at every width. -/
theorem CmpOp.okI1_eval {op : CmpOp} (h : op.okI1 = true) (n m a b : Nat) :
    op.eval n a b = op.eval m a b := by
  cases op <;> simp [CmpOp.okI1] at h <;> rfl

theorem and_mask32 {x : Nat} (hx : x < W) : x &&& (2 ^ 256 - 32) = x / 32 * 32 := by
  have hm : (2 ^ 256 - 32 : Nat) = (2 ^ 251 - 1) <<< 5 := by norm_num
  have h32 : x / 32 * 32 = x >>> 5 <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [hm, h32]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h5 : 5 ≤ i
  · have : 5 + (i - 5) = i := by omega
    rw [this]
    by_cases h256 : i < 256
    · simp [h5, show i - 5 < 251 by omega]
    · have hb : x.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hb]
  · simp [h5]

theorem mallocSize_word {n : Nat} (h : n + 31 < W) :
    BinOp.eval .and 256 (BinOp.eval .add 256 n 31) (2 ^ 256 - 32) = align32 n := by
  simp only [BinOp.eval]
  rw [show ((n : Int) + ((31 : Nat) : Int)) = ((n + 31 : Nat) : Int) by push_cast; rfl, wrap_nat,
    Nat.mod_eq_of_lt h, and_mask32 h]
  rfl

theorem shift_bytes (l : List UInt8) (hl : l.length = 32) (n : Nat) :
    Ethereum.fromBytesBigEndian l >>> (8 * (32 - n)) = Ethereum.fromBytesBigEndian (l.take n) := by
  have hd : (l.drop n).length = 32 - n := by rw [List.length_drop, hl]
  conv_lhs => rw [← List.take_append_drop n l]
  rw [Nat.shiftRight_eq_div_pow, ← hd, Reasoning.Theory.fromBytesBigEndian_append_div]

theorem fits_lt {x : H.Val} {t : Ty} (h : x.fits t = true) (st : H.State) :
    st.word x < 2 ^ t.bits := by
  cases x with
  | int bits n =>
    cases t <;> simp only [H.Val.fits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.false_eq_true] at h
    all_goals exact h.2
  | ptr b o =>
    have hw : st.word (.ptr b o) < 2 ^ 256 := Nat.mod_lt _ (Nat.two_pow_pos _)
    cases t with
    | int n =>
      simp only [H.Val.fits, Bool.and_eq_true, beq_iff_eq] at h
      rw [← h.1] at hw; exact hw
    | ptr _ => exact hw
    | _ => simp [H.Val.fits] at h

theorem word_lt (st : H.State) (x : H.Val) (h : x.fits t = true) (ht : t.bits ≤ 256) :
    st.word x < W := lt_of_lt_of_le (fits_lt h st) (Nat.pow_le_pow_right (by norm_num) ht)

theorem fits_ptr {b o : Nat} {t : Ty} (h : (H.Val.ptr b o).fits t = true) :
    o < W ∧ t.bits = 256 := by
  cases t <;> simp_all [H.Val.fits, Ty.bits, W]

theorem fits_int {bits v : Nat} {t : Ty} (h : (H.Val.int bits v).fits t = true) :
    v < 2 ^ t.bits ∧ bits = t.bits := by
  cases t <;> simp_all [H.Val.fits, Ty.bits]

theorem value_bits {t : Ty} (h : Ty.value t = true) : 1 ≤ t.bits ∧ t.bits ≤ 256 := by
  cases t with
  | int n =>
    simp only [Ty.value, widths, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at h
    simp only [Ty.bits]; omega
  | ptr _ => simp [Ty.bits]
  | _ => simp [Ty.value] at h

/-- What a cast gives (other than `sext`): a value of the target type whose word is the
    operand's (a pointer kept, or an integer made a pointer-typed word), or the operand's word
    truncated to the target's width. -/
theorem castVal_cases {st : H.State} {op : CastOp} {x v : H.Val} {ta ty : Ty}
    (h : castVal st op x ty = some v) (hop : op ≠ .sext) (hx : x.fits ta = true)
    (hta : Ty.value ta = true) :
    Ty.value ty = true ∧ v.fits ty = true ∧
      ((st.word v = st.word x ∧ ty.bits = 256) ∨ st.word v = st.word x % 2 ^ ty.bits) := by
  have hlt := word_lt st x hx (value_bits hta).2
  unfold castVal at h
  split at h
  · cases h
  next hty =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hty
  refine ⟨hty, ?_⟩
  split at h <;> (simp only [Option.some.injEq] at h; subst h)
  · exact ⟨by simpa [H.Val.fits, W] using (fits_ptr hx).1, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨by simpa [H.Val.fits, W] using (fits_ptr hx).1, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨by simpa [H.Val.fits, W] using (fits_ptr hx).1, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨by simpa [H.Val.fits, W] using (fits_ptr hx).1, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨by simpa [H.Val.fits, W, word_int] using hlt, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨by simpa [H.Val.fits, W, word_int] using hlt, Or.inl ⟨rfl, rfl⟩⟩
  · have hb := value_bits hty
    have hev : op.eval x.bits (st.word x) ty.bits = st.word x % 2 ^ ty.bits := by
      cases op <;> simp only [CastOp.eval, wrap_nat]
      all_goals exact absurd rfl hop
    rw [word_int, hev]
    refine ⟨?_, Or.inr rfl⟩
    cases ty <;> simp_all [H.Val.fits, Ty.bits, Nat.mod_lt]

/-- The word of a cast's result is its operand's low `k` bits, `k` as `castKeep` gives it. -/
theorem castVal_word {st : H.State} {op : CastOp} {x v : H.Val} {ta ty : Ty} {k : Nat}
    (h : castVal st op x ty = some v) (hk : castKeep op ta ty = some k) (hx : x.fits ta = true)
    (hta : Ty.value ta = true) :
    st.word v = st.word x % 2 ^ k ∧ v.fits ty = true := by
  have hop : op ≠ .sext := by rintro rfl; simp [castKeep] at hk
  obtain ⟨hty, hfit, hw⟩ := castVal_cases h hop hx hta
  refine ⟨?_, hfit⟩
  have hlt := fits_lt hx st
  have ha := value_bits hta
  have hb := value_bits hty
  have hW : st.word x < W := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) ha.2)
  unfold castKeep at hk
  split at hk
  · cases hk
  split at hk <;> (simp only [Option.some.injEq] at hk; subst hk)
  · next h1 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rw [h1.1] at hlt
    simp only [Ty.bits, pow_one] at hlt
    have h2 : 2 ≤ 2 ^ ty.bits := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ ty.bits := Nat.pow_le_pow_right (by norm_num) hb.1
    rw [Nat.mod_eq_of_lt hW]
    rcases hw with ⟨hw, _⟩ | hw
    · exact hw
    · rw [hw, Nat.mod_eq_of_lt (by omega)]
  · have hm : st.word x % 2 ^ min ta.bits ty.bits = st.word x % 2 ^ ty.bits := by
      rcases Nat.le_total ta.bits ty.bits with hle | hle
      · rw [Nat.min_eq_left hle, Nat.mod_eq_of_lt hlt,
          Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hle))]
      · rw [Nat.min_eq_right hle]
    rw [hm]
    rcases hw with ⟨hw, h256⟩ | hw
    · rw [hw, h256, Nat.mod_eq_of_lt hW]
    · exact hw

end Fe.Sonatina.Stage3.Place
