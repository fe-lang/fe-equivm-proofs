import Fe.Sonatina.Stage3.Place.Check

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

end Fe.Sonatina.Stage3.Place
