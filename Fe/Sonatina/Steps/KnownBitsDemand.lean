import Fe.Sonatina.Steps.SchemasS

/-!
# Demanded bits

The backward functions of `analysis/demanded_bits.rs` for the pure operations of the machine IR:
given the bits `d` of an instruction's result that its uses read, the bits of each operand the
result depends on (`demand1`, `demand2`, `demand3`).  Their soundness, in the form the checker
needs (`demand1_sound` …): two operand tuples that agree on the demanded bits of each operand
(`Agree`) give results that agree on `d`.

The Rust propagates nothing from a result no use reads (`d = 0`), and masks every demand to 256
bits (`add_demand`); so do these.  Where the Rust reads a shift amount or sign-extension byte
only if the operand is an immediate (`constant_shift(func, lhs)`), these take `imm : Option Nat`,
the immediate's word if the first operand is one; the soundness lemma then asks that both
tuples have that word there.  `evm_add_mod` and `evm_mul_mod` are `Opaque` to Sonatina, so
external uses: they demand every bit of every operand whatever `d` is (design §3.3, review
L-2).
-/

namespace Fe.Sonatina.Steps.Schemas

open KB

/-- `x` and `y` agree on the bits of `m`. -/
def Agree (m x y : Nat) : Prop := x &&& m = y &&& m

theorem agree_iff {m x y : Nat} : Agree m x y ↔ ∀ i, m.testBit i = true → x.testBit i = y.testBit i := by
  constructor
  · intro h i hi
    have := congrArg (·.testBit i) h
    simpa [Nat.testBit_and, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and]
    cases hm : m.testBit i
    · simp
    · rw [h i hm]

theorem Agree.at {m x y i : Nat} (h : Agree m x y) (hi : m.testBit i = true) :
    x.testBit i = y.testBit i := agree_iff.mp h i hi

/-- Agreement on a mask gives agreement on any mask within it: a claimed demand that contains
    the one the backward function asks for (design §9, ruling 8) is enough. -/
theorem Agree.mono {m m' x y : Nat} (h : Agree m x y) (hm : m' &&& m = m') : Agree m' x y := by
  apply agree_iff.mpr; intro i hi
  apply h.at
  have := congrArg (·.testBit i) hm
  simp only [Nat.testBit_and, hi, Bool.true_and] at this
  exact this

theorem agree_full {x y : Nat} (hx : x < W) (hy : y < W) (h : Agree M x y) : x = y := by
  have := h; unfold Agree at this; rwa [and_M hx, and_M hy] at this

theorem agree_of_W {d x y : Nat} (hx : x < W) (hy : y < W) (h : Agree (d &&& M) x y) :
    Agree d x y := by
  apply agree_iff.mpr; intro i hi
  by_cases hi' : i < 256
  · exact h.at (by simp only [Nat.testBit_and, testBit_M, hi, hi', decide_true, Bool.and_self])
  · rw [testBit_hi hx (by omega), testBit_hi hy (by omega)]

/-- `propagate_unary`: `not` reads the bits it gives; `is_zero` and `clz` read every bit. -/
def demand1 (o : Op1) (d : Nat) : Nat :=
  if d &&& M = 0 then 0
  else match o with
    | .not => d &&& M
    | .isZero | .clz => M

/-- `propagate_binary` on a demand `D` already cut to 256 bits. -/
def demand2' (o : Op2) (imm : Option Nat) (D : Nat) : Nat × Nat :=
  if D = 0 then (0, 0)
  else match o, imm with
    | .and, _ | .or, _ | .xor, _ => (D, D)
    | .shl, some s => (M, if s < 256 then (D >>> s) &&& M else 0)
    | .shr, some s => (M, if s < 256 then (D <<< s) &&& M else 0)
    -- Wider shifts depend only on the sign bit.
    | .sar, some s =>
      (M, ((D <<< min s 256) &&& M) |||
        (if D &&& (M ^^^ lowMask (256 - min s 256)) != 0 then signBit else 0))
    | .signextend, some b =>
      (0, if 32 ≤ b then D
        else if 256 ≤ (b + 1) * 8 then D
        else (D &&& lowMask ((b + 1) * 8)) |||
          (if D &&& (M ^^^ lowMask ((b + 1) * 8)) != 0 then 2 ^ ((b + 1) * 8 - 1) else 0))
    | _, _ => (M, M)

/-- `propagate_binary`: the demands on the first and the second operand, from the demand `d` on
    the result.  `imm` is the immediate's word if the first operand is one (`constant_shift`). -/
def demand2 (o : Op2) (imm : Option Nat) (d : Nat) : Nat × Nat := demand2' o imm (d &&& M)

/-- `evm_add_mod`, `evm_mul_mod`: external uses, every bit of each operand. -/
def demand3 (_ : Op3) (_ : Nat) : Nat × Nat × Nat := (M, M, M)

theorem agree_zero_d {d x y : Nat} (hx : x < W) (hy : y < W) (h : d &&& M = 0) : Agree d x y := by
  apply agree_of_W hx hy; rw [h]; simp [Agree]

theorem testBit_of_and_M {d i : Nat} (h : (d &&& M).testBit i = true) : d.testBit i = true ∧ i < 256 := by
  simp only [Nat.testBit_and, testBit_M, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem demand1_sound (o : Op1) {d x x' : Nat} (hx : x < W) (hx' : x' < W)
    (h : Agree (demand1 o d) x x') : Agree d (o.eval x) (o.eval x') := by
  unfold demand1 at h
  split at h
  · next h0 => exact agree_zero_d (Op1.eval_lt o hx) (Op1.eval_lt o hx') h0
  · cases o
    · apply agree_of_W (Op1.eval_lt _ hx) (Op1.eval_lt _ hx')
      apply agree_iff.mpr; intro i hi
      have hi' := (testBit_of_and_M hi).2
      simp only [Op1.eval, testBit_not hx hi', testBit_not hx' hi', h.at hi]
    · rw [agree_full hx hx' h]; exact rfl
    · rw [agree_full hx hx' h]; exact rfl

section Cases

variable {D x y x' y' : Nat}

theorem dsound_full (o : Op2) (hx : x < W) (hy : y < W) (hx' : x' < W) (hy' : y' < W)
    (h1 : Agree M x x') (h2 : Agree M y y') : Agree D (o.eval x y) (o.eval x' y') := by
  rw [agree_full hx hx' h1, agree_full hy hy' h2]; exact rfl

theorem dsound_bit {o : Op2} {b : BitOp} (hb : o.bit? = some b) (h1 : Agree D x x')
    (h2 : Agree D y y') : Agree D (o.eval x y) (o.eval x' y') := by
  apply agree_iff.mpr; intro i hi
  rw [testBit_bit hb, testBit_bit hb, h1.at hi, h2.at hi]

theorem dsound_shl {s : Nat} (hy : y < W) (hy' : y' < W)
    (h : Agree (if s < 256 then (D >>> s) &&& M else 0) y y') :
    Agree D (Op2.eval .shl s y) (Op2.eval .shl s y') := by
  apply agree_iff.mpr; intro i hi
  simp only [Op2.eval]
  by_cases hi' : i < 256
  · rw [testBit_shlW' hi', testBit_shlW' hi']
    by_cases hs : s ≤ i
    · rw [if_pos (by omega)] at h
      have : ((D >>> s) &&& M).testBit (i - s) = true := by
        rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_M, show s + (i - s) = i by omega, hi,
          Bool.true_and, decide_eq_true_eq]; omega
      simp [hs, h.at this]
    · simp [hs]
  · rw [testBit_hi (shlW_lt _ _) (by omega), testBit_hi (shlW_lt _ _) (by omega)]

theorem dsound_shr {s : Nat} (hy : y < W) (hy' : y' < W)
    (h : Agree (if s < 256 then (D <<< s) &&& M else 0) y y') :
    Agree D (Op2.eval .shr s y) (Op2.eval .shr s y') := by
  apply agree_iff.mpr; intro i hi
  simp only [Op2.eval]
  rw [testBit_shrW' hy, testBit_shrW' hy']
  by_cases hs : s < 256
  · rw [if_pos hs] at h
    by_cases hsi : s + i < 256
    · have : ((D <<< s) &&& M).testBit (s + i) = true := by
        rw [Nat.testBit_and, Nat.testBit_shiftLeft, testBit_M, show s + i - s = i by omega, hi]
        simp [hsi]
      simp [hs, h.at this]
    · rw [testBit_hi hy (by omega), testBit_hi hy' (by omega)]
  · simp [hs]

theorem dsound_sar {s : Nat} (hy : y < W) (hy' : y' < W)
    (h : Agree (((D <<< min s 256) &&& M) |||
      (if D &&& (M ^^^ lowMask (256 - min s 256)) != 0 then signBit else 0)) y y') :
    Agree D (Op2.eval .sar s y) (Op2.eval .sar s y') := by
  apply agree_iff.mpr; intro i hi
  simp only [Op2.eval]
  by_cases hi' : i < 256
  · rw [testBit_sarW' hy hi', testBit_sarW' hy' hi']
    split
    · next hsi =>
      apply h.at
      have hmin : min s 256 = s := by omega
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_M, hmin,
        show s + i - s = i by omega, hi]
      simp [hsi]
    · next hsi =>
      apply h.at
      have hne : (D &&& (M ^^^ lowMask (256 - min s 256)) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0
        have := congrArg (·.testBit i) h0
        simp [Nat.testBit_and, Nat.testBit_xor, testBit_M, testBit_lowMask, hi, hi'] at this
        omega
      rw [hne, if_pos rfl]
      simp only [Nat.testBit_or, signBit, Nat.testBit_two_pow_self, Bool.or_true]
  · rw [testBit_hi (sarW_lt hy) (by omega), testBit_hi (sarW_lt hy') (by omega)]

theorem dsound_signextend {b : Nat} (hy : y < W) (hy' : y' < W)
    (h : Agree (if 32 ≤ b then D
        else if 256 ≤ (b + 1) * 8 then D
        else (D &&& lowMask ((b + 1) * 8)) |||
          (if D &&& (M ^^^ lowMask ((b + 1) * 8)) != 0 then 2 ^ ((b + 1) * 8 - 1) else 0)) y y') :
    Agree D (Op2.eval .signextend b y) (Op2.eval .signextend b y') := by
  simp only [Op2.eval]
  split at h
  · next hb => rw [signextendW_of_ge (by omega), signextendW_of_ge (by omega)]; exact h
  · split at h
    · next _ hb => rw [show b = 31 by omega, signextendW_31 hy, signextendW_31 hy']; exact h
    · next h32 hb =>
      apply agree_iff.mpr; intro i hi
      by_cases hi' : i < 256
      · rw [testBit_signextendW hy (by omega) hi', testBit_signextendW hy' (by omega) hi']
        split
        · next hle =>
          apply h.at
          have : i < (b + 1) * 8 := by omega
          simp only [Nat.testBit_or, Nat.testBit_and, testBit_lowMask, hi, this, decide_true,
            Bool.true_and, Bool.true_or]
        · next hle =>
          apply h.at
          have hne : (D &&& (M ^^^ lowMask ((b + 1) * 8)) != 0) = true := by
            simp only [bne_iff_ne, ne_eq]
            intro h0
            have := congrArg (·.testBit i) h0
            simp [Nat.testBit_and, Nat.testBit_xor, testBit_M, testBit_lowMask, hi, hi'] at this
            omega
          rw [hne, if_pos rfl, show (b + 1) * 8 - 1 = 8 * b + 7 by omega]
          simp only [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
      · have h1 := Op2.eval_lt .signextend (x := b) (by simp only [W]; omega) hy
        have h2 := Op2.eval_lt .signextend (x := b) (by simp only [W]; omega) hy'
        simp only [Op2.eval] at h1 h2
        rw [testBit_hi h1 (by omega), testBit_hi h2 (by omega)]

end Cases

theorem demand2_sound (o : Op2) (imm : Option Nat) {d x y x' y' : Nat} (hx : x < W) (hy : y < W)
    (hx' : x' < W) (hy' : y' < W) (himm : ∀ n, imm = some n → x = n ∧ x' = n)
    (h1 : Agree (demand2 o imm d).1 x x') (h2 : Agree (demand2 o imm d).2 y y') :
    Agree d (o.eval x y) (o.eval x' y') := by
  apply agree_of_W (Op2.eval_lt o hx hy) (Op2.eval_lt o hx' hy')
  unfold demand2 at h1 h2
  generalize d &&& M = D at h1 h2 ⊢
  unfold demand2' at h1 h2
  by_cases h0 : D = 0
  · subst h0; simp [Agree]
  · rw [if_neg h0] at h1 h2
    cases o <;> cases imm <;> dsimp only at h1 h2
    all_goals first
      | exact dsound_full _ hx hy hx' hy' h1 h2
      | exact dsound_bit rfl h1 h2
      | (obtain ⟨rfl, rfl⟩ := himm _ rfl
         first
           | exact dsound_shl hy hy' h2
           | exact dsound_shr hy hy' h2
           | exact dsound_sar hy hy' h2
           | exact dsound_signextend hy hy' h2)

theorem demand3_sound (o : Op3) {d x y z x' y' z' : Nat} (hx : x < W) (hy : y < W) (hz : z < W)
    (hx' : x' < W) (hy' : y' < W) (hz' : z' < W) (h1 : Agree (demand3 o d).1 x x')
    (h2 : Agree (demand3 o d).2.1 y y') (h3 : Agree (demand3 o d).2.2 z z') :
    Agree d (o.eval x y z) (o.eval x' y' z') := by
  rw [agree_full hx hx' h1, agree_full hy hy' h2, agree_full hz hz' h3]; exact rfl

end Fe.Sonatina.Steps.Schemas
