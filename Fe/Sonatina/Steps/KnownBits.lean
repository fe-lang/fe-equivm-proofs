import Fe.Sonatina.Steps.SchemasWord

/-!
# Known bits

The fact of Sonatina's known-bits analysis (`analysis/known_bits.rs`) for an `i256` value: the
bits known zero (`kz`) and the bits known one (`ko`).  A word satisfies a fact (`KB.Sat`) when
it has a zero at every bit of `kz` and a one at every bit of `ko`.  A fact the analysis gives
has `kz &&& ko = 0` and both masks below `2 ^ 256` (`KB.valid`); soundness does not need it (a
fact no word satisfies makes a lemma vacuous), the checker checks it on exported facts.

- `transfer1`, `transfer2`, `transfer3`: the transfer function of each pure operation,
  mirroring `KnownBitsQuery::{unary,binary}_known_bits` for `i256` (every mask is normalized to
  256 bits, `KnownBits::normalized`); their soundness `transfer1_sound` … `transfer3_sound`.
- `KB.meet` (phis) and `meet_sound`; `KB.le`, the direction of a fact check (design §9 ruling
  8: a claimed fact is `le` the derived one) and `KB.Sat.le`.

Where the Rust takes a shift amount, sign-extension byte, or comparison operand only when it is
an immediate (`constant_shift(value_imm …)`, `exact_imm`), the Lean transfer takes it whenever
the operand's fact is exact (`KB.exactVal?`).  An immediate's fact is exact, so the Lean
transfer is at least as precise as the Rust on every input; a fact the Rust derives is `le` the
Lean one.
-/

namespace Fe.Sonatina.Steps.Schemas

/-- `n` low bits. -/
def lowMask (n : Nat) : Nat := 2 ^ n - 1

structure KB where
  /-- The bits known zero. -/
  kz : Nat
  /-- The bits known one. -/
  ko : Nat
  deriving DecidableEq, Repr, Inhabited

namespace KB

/-- No bit known. -/
def unknown : KB := ⟨0, 0⟩

/-- The fact of a word: every bit known (`KnownBits::from_imm`). -/
def exact (v : Nat) : KB := ⟨M ^^^ v, v⟩

/-- Both masks cut to 256 bits (`KnownBits::normalized` at `i256`). -/
def norm (f : KB) : KB := ⟨f.kz &&& M, f.ko &&& M⟩

/-- A word satisfies the fact. -/
def Sat (f : KB) (x : Nat) : Prop := x &&& f.kz = 0 ∧ x &&& f.ko = f.ko

instance (f : KB) (x : Nat) : Decidable (f.Sat x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The fact is one the analysis can give: no bit both known zero and known one, both masks
    within 256 bits. -/
def valid (f : KB) : Bool := f.kz &&& f.ko == 0 && f.kz < W && f.ko < W

/-- `c` knows no bit `d` does not know alike: every word satisfying `d` satisfies `c`.  A claimed
    fact must be `le` the derived one (design §9, ruling 8). -/
def le (c d : KB) : Bool := c.kz &&& d.kz == c.kz && c.ko &&& d.ko == c.ko

/-- The bits two facts agree on: the fact of a phi, from its incoming facts
    (`KnownBits::meet`). -/
def meet (a b : KB) : KB := norm ⟨a.kz &&& b.kz, a.ko &&& b.ko⟩

/-- The word the fact fixes, if it knows all 256 bits (`KnownBits::exact_imm`). -/
def exactVal? (f : KB) : Option Nat :=
  if (f.kz ||| f.ko) &&& M = M then some (f.ko &&& M) else none

/-- Every bit of `m` is known zero (`all_zero_in`). -/
def allZero (f : KB) (m : Nat) : Bool := f.kz &&& m == m

/-- Every bit of `m` is known one (`all_one_in`). -/
def allOne (f : KB) (m : Nat) : Bool := f.ko &&& m == m

/-- Some bit is known zero in one fact and known one in the other
    (`has_conflicting_known_bits`). -/
def conflict (a b : KB) : Bool := ((a.kz &&& b.ko) ||| (a.ko &&& b.kz)) &&& M != 0

/-- The fact of an unknown `i1` (`bool_shape`): every bit but bit 0 known zero. -/
def boolShape : KB := ⟨M ^^^ 1, 0⟩

/-- The fact of a known `i1` (`KnownBits::exact_bool`). -/
def exactBool (b : Bool) : KB := if b then ⟨M ^^^ 1, 1⟩ else ⟨M, 0⟩

end KB

open KB

/-! ## Transfer functions -/

/-- The bits at and above `256 - s`: where `shr s` and `sar s` shift in (`fill_mask`). -/
def fillMask (s : Nat) : Nat := M ^^^ lowMask (256 - s)

/-- The sign bit of an `i256`. -/
def signBit : Nat := 2 ^ 255

def tShl (s v : KB) : KB :=
  match s.exactVal? with
  | none => unknown
  | some n => if 256 ≤ n then exact 0 else norm ⟨(v.kz <<< n) ||| lowMask n, v.ko <<< n⟩

def tShr (s v : KB) : KB :=
  match s.exactVal? with
  | none => unknown
  | some n =>
    if 256 ≤ n then exact 0 else norm ⟨((v.kz &&& M) >>> n) ||| fillMask n, (v.ko &&& M) >>> n⟩

def tSar (s v : KB) : KB :=
  match s.exactVal? with
  | none => unknown
  | some n =>
    if 256 ≤ n then
      if v.allZero signBit then exact 0 else if v.allOne signBit then exact M else unknown
    else
      let kz := (v.kz &&& M) >>> n
      let ko := (v.ko &&& M) >>> n
      if v.allZero signBit then norm ⟨kz ||| fillMask n, ko⟩
      else if v.allOne signBit then norm ⟨kz, ko ||| fillMask n⟩
      else norm ⟨kz, ko⟩

/-- `evm_signextend_known_bits`. -/
def tSignextend (b v : KB) : KB :=
  match b.exactVal? with
  | none => unknown
  | some n =>
    if 32 ≤ n then norm v
    else if 256 ≤ (n + 1) * 8 then norm v
    else
      let low := lowMask ((n + 1) * 8)
      let high := M ^^^ low
      let sign := 2 ^ ((n + 1) * 8 - 1)
      if v.allZero sign then norm ⟨(v.kz &&& low) ||| high, v.ko &&& low⟩
      else if v.allOne sign then norm ⟨v.kz &&& low, (v.ko &&& low) ||| high⟩
      else norm ⟨v.kz &&& low, v.ko &&& low⟩

/-- `compare_known_bits`: exact operands give the exact result; `eq` of conflicting operands
    is false; otherwise an unknown `i1`. -/
def tCmp (o : Op2) (a b : KB) : KB :=
  match a.exactVal?, b.exactVal? with
  | some x, some y => exactBool (o.eval x y != 0)
  | _, _ => if o == .eq && conflict a b then exactBool false else boolShape

def transfer1 : Op1 → KB → KB
  | .not, a => norm ⟨a.ko, a.kz⟩
  | .isZero, a =>
    if a.allZero M then exactBool true
    else if a.ko &&& M != 0 then exactBool false
    else boolShape
  -- A count is at most 256, so only its low 9 bits can be set.
  | .clz, _ => norm ⟨M ^^^ lowMask 9, 0⟩

def transfer2 : Op2 → KB → KB → KB
  | .and, a, b => norm ⟨a.kz ||| b.kz, a.ko &&& b.ko⟩
  | .or, a, b => norm ⟨a.kz &&& b.kz, a.ko ||| b.ko⟩
  | .xor, a, b =>
    norm ⟨(a.kz &&& b.kz) ||| (a.ko &&& b.ko), (a.kz &&& b.ko) ||| (a.ko &&& b.kz)⟩
  | .shl, s, v => tShl s v
  | .shr, s, v => tShr s v
  | .sar, s, v => tSar s v
  -- BYTE gives at most eight bits.
  | .byte, _, _ => norm ⟨M ^^^ lowMask 8, 0⟩
  | .signextend, b, v => tSignextend b v
  | .lt, a, b => tCmp .lt a b
  | .gt, a, b => tCmp .gt a b
  | .slt, a, b => tCmp .slt a b
  | .sgt, a, b => tCmp .sgt a b
  | .eq, a, b => tCmp .eq a b
  | .add, _, _ | .sub, _, _ | .mul, _, _ | .udiv, _, _ | .sdiv, _, _ | .umod, _, _
  | .smod, _, _ | .exp, _, _ => unknown

/-- `evm_add_mod` and `evm_mul_mod` are `Opaque` to the analysis. -/
def transfer3 : Op3 → KB → KB → KB → KB
  | _, _, _, _ => unknown

/-! ## Bits of words -/

theorem testBit_M (i : Nat) : M.testBit i = decide (i < 256) := Nat.testBit_two_pow_sub_one _ _

theorem testBit_hi {x i : Nat} (hx : x < W) (hi : 256 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem testBit_lowMask (n i : Nat) : (lowMask n).testBit i = decide (i < n) :=
  Nat.testBit_two_pow_sub_one _ _

theorem lt_W_of_testBit {x : Nat} (h : ∀ i, 256 ≤ i → x.testBit i = false) : x < W :=
  Nat.lt_pow_two_of_testBit x h

theorem testBit_not {x i : Nat} (hx : x < W) (hi : i < 256) : (M - x).testBit i = !x.testBit i := by
  rw [show M - x = 2 ^ 256 - (x + 1) by simp only [M]; omega, Nat.testBit_two_pow_sub_succ hx]
  simp [hi]

theorem testBit_shrW {s y i : Nat} (hs : s < 256) : (shrW s y).testBit i = y.testBit (s + i) := by
  rw [shrW, if_neg (by omega), Nat.testBit_shiftRight]

theorem testBit_shlW {s y i : Nat} (hs : s < 256) (hi : i < 256) :
    (shlW s y).testBit i = (decide (s ≤ i) && y.testBit (i - s)) := by
  rw [shlW, if_neg (by omega), Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp [hi]

/-- `sar` by less than 256: the bit `s` above, or the sign bit past the top. -/
theorem testBit_sarW {s y i : Nat} (hy : y < W) (hs : s < 256) (hi : i < 256) :
    (sarW s y).testBit i = if s + i < 256 then y.testBit (s + i) else y.testBit 255 := by
  unfold sarW
  split
  · next hneg =>
    rw [testBit_shrW hs]
    split
    · rfl
    · rw [testBit_hi hy (by omega), Nat.testBit_lt_two_pow hneg]
  · next hneg =>
    have hlt : shrW s (M - y) < W := lt_of_le_of_lt (shrW_le _ _) (by simp only [M] at *; omega)
    rw [testBit_not hlt hi, testBit_shrW hs]
    have h255 : y.testBit 255 = true := by
      have : 2 ^ 255 ≤ y := by omega
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      have h1 : y / 2 ^ 255 = 1 := by
        apply Nat.div_eq_of_lt_le <;> simp only [W] at hy <;> omega
      omega
    split
    · next h => rw [testBit_not hy h]; simp
    · next h =>
      rw [h255]
      have : (M - y) < W := by simp only [M]; omega
      rw [testBit_hi this (by omega)]; rfl

theorem testBit_two_pow_sub_two_pow {n t i : Nat} (ht : t ≤ n) :
    (2 ^ n - 2 ^ t).testBit i = (decide (t ≤ i) && decide (i < n)) := by
  rw [show 2 ^ n - 2 ^ t = (2 ^ (n - t) - 1) <<< t by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel ht]]
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : t ≤ i <;> simp [h] <;> omega

/-- `signextend b` for `b ≤ 31`: the bits up to the sign bit `8 b + 7`, and the sign bit above. -/
theorem testBit_signextendW {b y i : Nat} (hy : y < W) (hb : b ≤ 31) (hi : i < 256) :
    (signextendW b y).testBit i = if i ≤ 8 * b + 7 then y.testBit i else y.testBit (8 * b + 7) := by
  unfold signextendW
  rw [if_pos hb]
  have hsign : (y &&& 2 ^ (8 * b + 7) ≠ 0) ↔ y.testBit (8 * b + 7) = true := by
    constructor
    · intro h
      by_contra h'
      apply h
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : 8 * b + 7 = j
      · subst hj; simpa using h'
      · simp [hj]
    · intro h h0
      have := congrArg (·.testBit (8 * b + 7)) h0
      simp [Nat.testBit_and, Nat.testBit_two_pow, h] at this
  split
  · next h =>
    have h1 := hsign.mp h
    rw [Nat.testBit_or, show W = 2 ^ 256 from rfl,
      testBit_two_pow_sub_two_pow (n := 256) (t := 8 * b + 7) (by omega)]
    split
    · next hle =>
      by_cases he : i = 8 * b + 7
      · subst he; simp [h1]
      · have : ¬ (8 * b + 7 ≤ i) := by omega
        simp [this]
    · next hle =>
      have : 8 * b + 7 ≤ i := by omega
      simp [h1, hi, this]
  · next h =>
    have h1 : y.testBit (8 * b + 7) = false := by
      by_contra h'; exact h (hsign.mpr (by simpa using h'))
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    split
    · next hle =>
      by_cases he : i = 8 * b + 7
      · subst he; simp [h1]
      · have : i < 8 * b + 7 := by omega
        simp [this]
    · next hle =>
      have : ¬ i < 8 * b + 7 := by omega
      simp [this, h1]

/-! ## Satisfying a fact, bit by bit -/

theorem sat_iff {f : KB} {x : Nat} :
    f.Sat x ↔ ∀ i, (f.kz.testBit i = true → x.testBit i = false) ∧
      (f.ko.testBit i = true → x.testBit i = true) := by
  constructor
  · rintro ⟨hz, ho⟩ i
    constructor
    · intro h
      have := congrArg (·.testBit i) hz
      simp only [Nat.testBit_and, Nat.zero_testBit, h, Bool.and_true] at this
      exact this
    · intro h
      have := congrArg (·.testBit i) ho
      simp only [Nat.testBit_and, h, Bool.and_true] at this
      exact this
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.zero_testBit]
      cases hk : f.kz.testBit i
      · simp
      · simp [(h i).1 hk]
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and]
      cases hk : f.ko.testBit i
      · simp
      · simp [(h i).2 hk]

theorem KB.Sat.zero {f : KB} {x i : Nat} (h : f.Sat x) (hi : f.kz.testBit i = true) :
    x.testBit i = false := ((sat_iff.mp h) i).1 hi

theorem KB.Sat.one {f : KB} {x i : Nat} (h : f.Sat x) (hi : f.ko.testBit i = true) :
    x.testBit i = true := ((sat_iff.mp h) i).2 hi

/-- A word satisfies a normalized fact if it satisfies it below bit 256. -/
theorem sat_norm {f : KB} {x : Nat}
    (h : ∀ i < 256, (f.kz.testBit i = true → x.testBit i = false) ∧
      (f.ko.testBit i = true → x.testBit i = true)) : f.norm.Sat x := by
  apply sat_iff.mpr; intro i
  simp only [KB.norm, Nat.testBit_and, testBit_M, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact (h i h2).1 h1
  · rintro ⟨h1, h2⟩; exact (h i h2).2 h1

theorem sat_unknown (x : Nat) : unknown.Sat x := by simp [KB.Sat, unknown]

theorem sat_exact {v : Nat} (hv : v < W) : (exact v).Sat v := by
  apply sat_iff.mpr; intro i
  simp only [KB.exact, Nat.testBit_xor, testBit_M]
  constructor
  · intro h
    by_cases hi : i < 256
    · simp only [hi, decide_true] at h; cases hb : v.testBit i <;> simp_all
    · exact testBit_hi hv (by omega)
  · exact id

theorem KB.Sat.le {c d : KB} {x : Nat} (hd : d.Sat x) (h : c.le d = true) : c.Sat x := by
  simp only [KB.le, Bool.and_eq_true, beq_iff_eq] at h
  apply sat_iff.mpr; intro i
  constructor
  · intro hc; apply hd.zero
    have := congrArg (·.testBit i) h.1; simp only [Nat.testBit_and, hc] at this
    simpa using this
  · intro hc; apply hd.one
    have := congrArg (·.testBit i) h.2; simp only [Nat.testBit_and, hc] at this
    simpa using this

theorem meet_sound {a b : KB} {x : Nat} (h : a.Sat x ∨ b.Sat x) : (meet a b).Sat x := by
  apply sat_norm; intro i _
  simp only [Nat.testBit_and, Bool.and_eq_true]
  rcases h with h | h
  · exact ⟨fun hk => h.zero hk.1, fun hk => h.one hk.1⟩
  · exact ⟨fun hk => h.zero hk.2, fun hk => h.one hk.2⟩

/-- A fact that fixes all 256 bits fixes the word. -/
theorem exactVal?_sat {f : KB} {n x : Nat} (h : f.exactVal? = some n) (hf : f.Sat x)
    (hx : x < W) : x = n := by
  unfold exactVal? at h
  split at h
  · next hall =>
    simp only [Option.some.injEq] at h; subst h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, testBit_M]
    by_cases hi : i < 256
    · simp only [hi, decide_true, Bool.and_true]
      have := congrArg (·.testBit i) hall
      simp only [Nat.testBit_and, Nat.testBit_or, testBit_M, hi, decide_true, Bool.and_true,
        Bool.or_eq_true] at this
      cases hk : f.ko.testBit i
      · rcases this with h1 | h1
        · exact hf.zero h1
        · simp_all
      · exact hf.one hk
    · simp only [hi, decide_false, Bool.and_false]; exact testBit_hi hx (by omega)
  · cases h

theorem exactVal?_lt {f : KB} {n : Nat} (h : f.exactVal? = some n) : n < W := by
  unfold exactVal? at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact Nat.and_lt_two_pow _ (by decide)
  · cases h

theorem sat_exactBool {b : Bool} : (exactBool b).Sat (ofBool b) := by
  cases b <;> decide

theorem sat_boolShape (b : Bool) : boolShape.Sat (ofBool b) := by
  cases b <;> decide

/-- A word below `2 ^ n` has none of the bits `M ^^^ lowMask n`. -/
theorem sat_low {v n : Nat} (hn : n ≤ 256) (hv : v < 2 ^ n) : (norm ⟨M ^^^ lowMask n, 0⟩).Sat v := by
  apply sat_norm; intro i hi
  simp only [Nat.testBit_xor, testBit_M, testBit_lowMask, hi, decide_true, Nat.zero_testBit]
  refine ⟨fun h => ?_, fun h => by cases h⟩
  have : ¬ i < n := by simpa using h
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))

/-! ## Soundness of the transfer functions -/

theorem ofBool_cases (b : Bool) : ofBool b = 0 ∨ ofBool b = 1 := by cases b <;> simp [ofBool]

theorem transfer1_sound (o : Op1) {a : KB} {x : Nat} (hx : x < W) (ha : a.Sat x) :
    (transfer1 o a).Sat (o.eval x) := by
  cases o with
  | not =>
    apply sat_norm; intro i hi
    simp only [Op1.eval, testBit_not hx hi]
    exact ⟨fun h => by simp [ha.one h], fun h => by simp [ha.zero h]⟩
  | isZero =>
    simp only [transfer1, Op1.eval]
    split
    · next h =>
      have hx0 : x = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.zero_testBit]
        by_cases hi : i < 256
        · apply ha.zero
          simp only [allZero, beq_iff_eq] at h
          have := congrArg (·.testBit i) h
          simp only [Nat.testBit_and, testBit_M, hi, decide_true, Bool.and_true] at this
          exact this
        · exact testBit_hi hx (by omega)
      subst hx0; exact sat_exactBool
    · split
      · next h =>
        have hx0 : x ≠ 0 := by
          intro hx0; subst hx0
          simp only [bne_iff_ne, ne_eq] at h
          apply h
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
          cases hk : a.ko.testBit i
          · simp
          · have := ha.one hk; simp at this
        have : (x == 0) = false := by simpa using hx0
        rw [this]; exact sat_exactBool
      · exact sat_boolShape _
  | clz =>
    apply sat_low (by decide)
    have := Op1.eval_lt .clz hx
    simp only [Op1.eval, clzW] at this ⊢
    split <;> omega

theorem sat_and_ofBool_eval {o : Op2} (h : o = .lt ∨ o = .gt ∨ o = .slt ∨ o = .sgt ∨ o = .eq)
    (x y : Nat) : ∃ b, o.eval x y = ofBool b := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem tCmp_sound {o : Op2} (ho : o = .lt ∨ o = .gt ∨ o = .slt ∨ o = .sgt ∨ o = .eq)
    {a b : KB} {x y : Nat} (hx : x < W) (hy : y < W) (ha : a.Sat x) (hb : b.Sat y) :
    (tCmp o a b).Sat (o.eval x y) := by
  obtain ⟨c, hc⟩ := sat_and_ofBool_eval ho x y
  unfold tCmp
  split
  · next n m hn hm =>
    rw [exactVal?_sat hn ha hx, exactVal?_sat hm hb hy] at hc ⊢
    rw [hc]
    cases c <;> simp [ofBool] <;> exact sat_exactBool (b := _)
  · split
    · next h =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hcf⟩ := h
      have hne : x ≠ y := by
        intro hxy; subst hxy
        simp only [conflict, bne_iff_ne, ne_eq] at hcf
        apply hcf
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, testBit_M]
        cases h1 : a.kz.testBit i <;> cases h2 : b.ko.testBit i <;>
          cases h3 : a.ko.testBit i <;> cases h4 : b.kz.testBit i <;> simp
        all_goals first
          | (have := ha.zero h1; have := hb.one h2; simp_all)
          | (have := ha.one h3; have := hb.zero h4; simp_all)
      have : Op2.eval .eq x y = ofBool false := by
        simp [Op2.eval, ofBool, hne]
      rw [this]; exact sat_exactBool
    · rw [hc]; exact sat_boolShape c

theorem tShl_sound {s v : KB} {x y : Nat} (hx : x < W) (hy : y < W) (hs : s.Sat x)
    (hv : v.Sat y) : (tShl s v).Sat (shlW x y) := by
  unfold tShl
  split
  · exact sat_unknown _
  · next n hn =>
    rw [← exactVal?_sat hn hs hx]
    split
    · next h => rw [shlW, if_pos h]; exact sat_exact (by decide)
    · next h =>
      apply sat_norm; intro i hi
      rw [testBit_shlW (by omega) hi]
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_lowMask, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | h1)
        · simp [hv.zero h2]
        · simp; omega
      · rintro ⟨h1, h2⟩; simp [h1, hv.one h2]

theorem tShr_sound {s v : KB} {x y : Nat} (hx : x < W) (hy : y < W) (hs : s.Sat x)
    (hv : v.Sat y) : (tShr s v).Sat (shrW x y) := by
  unfold tShr
  split
  · exact sat_unknown _
  · next n hn =>
    rw [← exactVal?_sat hn hs hx]
    split
    · next h => rw [shrW, if_pos h]; exact sat_exact (by decide)
    · next h =>
      apply sat_norm; intro i hi
      rw [testBit_shrW (by omega)]
      simp only [fillMask, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight,
        Nat.testBit_and, testBit_M, testBit_lowMask, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | h1)
        · exact hv.zero h1
        · have : 256 - x ≤ i := by
            revert h1; simp only [hi, decide_true]; cases hd : decide (i < 256 - x) <;> simp_all
          exact testBit_hi hy (by omega)
      · rintro ⟨h1, h2⟩; exact hv.one h1

theorem allZero_sign {v : KB} {y : Nat} (hv : v.Sat y) (h : v.allZero signBit = true) :
    y.testBit 255 = false := by
  apply hv.zero
  simp only [allZero, signBit, beq_iff_eq] at h
  have := congrArg (·.testBit 255) h
  simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at this
  exact this

theorem allOne_sign {v : KB} {y : Nat} (hv : v.Sat y) (h : v.allOne signBit = true) :
    y.testBit 255 = true := by
  apply hv.one
  simp only [allOne, signBit, beq_iff_eq] at h
  have := congrArg (·.testBit 255) h
  simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at this
  exact this

theorem lt_sign_iff {y : Nat} (hy : y < W) : y < 2 ^ 255 ↔ y.testBit 255 = false := by
  constructor
  · exact Nat.testBit_lt_two_pow
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases h' : i = 255
    · subst h'; exact h
    · exact testBit_hi hy (by omega)

theorem tSar_sound {s v : KB} {x y : Nat} (hx : x < W) (hy : y < W) (hs : s.Sat x)
    (hv : v.Sat y) : (tSar s v).Sat (sarW x y) := by
  unfold tSar
  split
  · exact sat_unknown _
  · next n hn =>
    rw [← exactVal?_sat hn hs hx]
    split
    · next h =>
      split
      · next hz =>
        have := (lt_sign_iff hy).mpr (allZero_sign hv hz)
        rw [sarW, if_pos this, shrW, if_pos h]; exact sat_exact (by decide)
      · split
        · next _ ho =>
          have : ¬ y < 2 ^ 255 := fun h' => by
            rw [lt_sign_iff hy, allOne_sign hv ho] at h'; cases h'
          rw [sarW, if_neg this, shrW, if_pos h, Nat.sub_zero]; exact sat_exact (by decide)
        · exact sat_unknown _
    · next h =>
      have key : ∀ i < 256, (sarW x y).testBit i =
          if x + i < 256 then y.testBit (x + i) else y.testBit 255 :=
        fun i hi => testBit_sarW hy (by omega) hi
      have hfill : ∀ i < 256, (fillMask x).testBit i = decide (256 ≤ x + i) := by
        intro i hi
        simp only [fillMask, Nat.testBit_xor, testBit_M, testBit_lowMask, hi, decide_true]
        by_cases h' : i < 256 - x <;> simp [h'] <;> omega
      have hsh : ∀ (m : Nat) i, i < 256 → ((m &&& M) >>> x).testBit i =
          (m.testBit (x + i) && decide (x + i < 256)) := by
        intro m i _
        simp only [Nat.testBit_shiftRight, Nat.testBit_and, testBit_M]
      split
      · next hz =>
        have h255 := allZero_sign hv hz
        apply sat_norm; intro i hi
        rw [key i hi]
        simp only [Nat.testBit_or, hfill i hi, hsh _ i hi, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq]
        constructor
        · rintro (⟨h1, h2⟩ | h1)
          · rw [if_pos h2]; exact hv.zero h1
          · rw [if_neg (by omega)]; exact h255
        · rintro ⟨h1, h2⟩; rw [if_pos h2]; exact hv.one h1
      · split
        · next _ ho =>
          have h255 := allOne_sign hv ho
          apply sat_norm; intro i hi
          rw [key i hi]
          simp only [Nat.testBit_or, hfill i hi, hsh _ i hi, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq]
          constructor
          · rintro ⟨h1, h2⟩; rw [if_pos h2]; exact hv.zero h1
          · rintro (⟨h1, h2⟩ | h1)
            · rw [if_pos h2]; exact hv.one h1
            · rw [if_neg (by omega)]; exact h255
        · apply sat_norm; intro i hi
          rw [key i hi]
          simp only [hsh _ i hi, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨fun ⟨h1, h2⟩ => by rw [if_pos h2]; exact hv.zero h1,
            fun ⟨h1, h2⟩ => by rw [if_pos h2]; exact hv.one h1⟩

theorem signextendW_of_ge {b y : Nat} (hb : 31 < b) : signextendW b y = y := by
  rw [signextendW, if_neg (by omega)]

theorem signextendW_31 {y : Nat} (hy : y < W) : signextendW 31 y = y := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 256
  · rw [testBit_signextendW hy (by decide) hi, if_pos (by omega)]
  · have h := Op2.eval_lt .signextend (x := 31) (by decide) hy
    simp only [Op2.eval] at h
    rw [testBit_hi hy (by omega), testBit_hi h (by omega)]

theorem tSignextend_sound {b v : KB} {x y : Nat} (hx : x < W) (hy : y < W) (hb : b.Sat x)
    (hv : v.Sat y) : (tSignextend b v).Sat (signextendW x y) := by
  have hnv : v.norm.Sat y := by
    apply sat_norm; intro i _; exact ⟨hv.zero, hv.one⟩
  unfold tSignextend
  split
  · exact sat_unknown _
  · next n hn =>
    rw [← exactVal?_sat hn hb hx]
    split
    · next h => rw [signextendW_of_ge (by omega)]; exact hnv
    · split
      · next _ h =>
        rw [show x = 31 by omega, signextendW_31 hy]; exact hnv
      · next h1 h2 =>
        have hsw : (x + 1) * 8 - 1 = 8 * x + 7 := by omega
        have key : ∀ i < 256, (signextendW x y).testBit i =
            if i ≤ 8 * x + 7 then y.testBit i else y.testBit (8 * x + 7) :=
          fun i hi => testBit_signextendW hy (by omega) hi
        have hlow : ∀ i, (lowMask ((x + 1) * 8)).testBit i = decide (i ≤ 8 * x + 7) := by
          intro i; rw [testBit_lowMask]; congr 1; apply propext; omega
        have hsign : ∀ (f : KB), f.Sat y → f.allZero (2 ^ ((x + 1) * 8 - 1)) = true →
            y.testBit (8 * x + 7) = false := by
          intro f hf h
          apply hf.zero
          simp only [allZero, beq_iff_eq, hsw] at h
          have := congrArg (·.testBit (8 * x + 7)) h
          simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
        have hsign1 : ∀ (f : KB), f.Sat y → f.allOne (2 ^ ((x + 1) * 8 - 1)) = true →
            y.testBit (8 * x + 7) = true := by
          intro f hf h
          apply hf.one
          simp only [allOne, beq_iff_eq, hsw] at h
          have := congrArg (·.testBit (8 * x + 7)) h
          simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
        dsimp only
        split
        · next hz =>
          have hs := hsign v hv hz
          apply sat_norm; intro i hi
          rw [key i hi]
          simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_M, hlow, hi,
            decide_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro (⟨h1, h2⟩ | h1)
            · rw [if_pos h2]; exact hv.zero h1
            · have : ¬ i ≤ 8 * x + 7 := by simpa using h1
              rw [if_neg this]; exact hs
          · rintro ⟨h1, h2⟩; rw [if_pos h2]; exact hv.one h1
        · split
          · next _ ho =>
            have hs := hsign1 v hv ho
            apply sat_norm; intro i hi
            rw [key i hi]
            simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_M, hlow, hi,
              decide_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨h1, h2⟩; rw [if_pos h2]; exact hv.zero h1
            · rintro (⟨h1, h2⟩ | h1)
              · rw [if_pos h2]; exact hv.one h1
              · have : ¬ i ≤ 8 * x + 7 := by simpa using h1
                rw [if_neg this]; exact hs
          · apply sat_norm; intro i hi
            rw [key i hi]
            simp only [Nat.testBit_and, hlow, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨fun ⟨h1, h2⟩ => by rw [if_pos h2]; exact hv.zero h1,
              fun ⟨h1, h2⟩ => by rw [if_pos h2]; exact hv.one h1⟩

theorem transfer2_sound (o : Op2) {a b : KB} {x y : Nat} (hx : x < W) (hy : y < W)
    (ha : a.Sat x) (hb : b.Sat y) : (transfer2 o a b).Sat (o.eval x y) := by
  cases o
  case and =>
    apply sat_norm; intro i _
    simp only [Op2.eval, Nat.testBit_and, Nat.testBit_or, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro (h | h)
      · simp [ha.zero h]
      · simp [hb.zero h]
    · rintro ⟨h1, h2⟩; simp [ha.one h1, hb.one h2]
  case or =>
    apply sat_norm; intro i _
    simp only [Op2.eval, Nat.testBit_and, Nat.testBit_or, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; simp [ha.zero h1, hb.zero h2]
    · rintro (h | h)
      · simp [ha.one h]
      · simp [hb.one h]
  case xor =>
    apply sat_norm; intro i _
    simp only [Op2.eval, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Bool.or_eq_true,
      Bool.and_eq_true]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · simp [ha.zero h1, hb.zero h2]
      · simp [ha.one h1, hb.one h2]
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · simp [ha.zero h1, hb.one h2]
      · simp [ha.one h1, hb.zero h2]
  case shl => exact tShl_sound hx hy ha hb
  case shr => exact tShr_sound hx hy ha hb
  case sar => exact tSar_sound hx hy ha hb
  case byte =>
    apply sat_low (by decide)
    simp only [Op2.eval, byteW]
    split
    · decide
    · exact Nat.and_lt_two_pow _ (by decide)
  case signextend => exact tSignextend_sound hx hy ha hb
  case lt => exact tCmp_sound (by simp) hx hy ha hb
  case gt => exact tCmp_sound (by simp) hx hy ha hb
  case slt => exact tCmp_sound (by simp) hx hy ha hb
  case sgt => exact tCmp_sound (by simp) hx hy ha hb
  case eq => exact tCmp_sound (by simp) hx hy ha hb
  all_goals exact sat_unknown _

theorem transfer3_sound (o : Op3) (a b c : KB) (x y z : Nat) :
    (transfer3 o a b c).Sat (o.eval x y z) := sat_unknown _

end Fe.Sonatina.Steps.Schemas
