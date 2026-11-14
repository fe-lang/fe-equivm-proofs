import Fe.Sonatina.CheckBlock

/-!
# The machine IR's arithmetic on words

The interpreter computes an instruction on the values of its operands at their width
(`BinOp.eval`, `CmpOp.eval`); the checker gives it the value of its EVM opcode (`opEval`).  At
256 bits, on words, they agree: `bin_word` for every binary instruction `binOpcode` maps,
`cmp_word` for every comparison `cmpOpcode` maps (the signed ones through `signed`),
`isZero_word` and `not_word`.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

theorem eq_of_toNat {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨⟨a, ha⟩⟩ := a; obtain ⟨⟨b, hb⟩⟩ := b
  simp only [UInt256.toNat] at h; subst h; rfl

theorem size_eq : UInt256.size = 2 ^ 256 := rfl

theorem wrap_int (n : Int) : (wrap 256 n : Int) = n % UInt256.size := by
  simp only [wrap]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem add_word (x y : Nat) :
    UInt256.ofNat x + UInt256.ofNat y = UInt256.ofNat (wrap 256 (x + y)) := by
  apply eq_of_toNat
  show ((Fin.ofNat _ x + Fin.ofNat _ y : Fin _)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.val_add, Fin.val_ofNat]
  zify
  rw [wrap_int]
  simp [Int.add_emod, Int.emod_emod_of_dvd]

theorem mul_word (x y : Nat) :
    UInt256.mul (.ofNat x) (.ofNat y) = UInt256.ofNat (wrap 256 (x * y)) := by
  apply eq_of_toNat
  show ((Fin.ofNat _ x * Fin.ofNat _ y : Fin _)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.val_mul, Fin.val_ofNat]
  zify
  rw [wrap_int]
  simp [Int.mul_emod, Int.emod_emod_of_dvd]

theorem sub_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.sub (.ofNat x) (.ofNat y) = UInt256.ofNat (wrap 256 (x - y : Int)) := by
  apply eq_of_toNat
  show ((Fin.ofNat _ x - Fin.ofNat _ y : Fin _)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.sub_def, Fin.val_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  zify [show y ≤ UInt256.size by omega]
  rw [wrap_int]
  simp only [Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [show ((UInt256.size : Int) - y + x) = (x - y) + UInt256.size by ring, Int.add_emod_right]

theorem toNat_ofNat_lt {x : Nat} (hx : x < UInt256.size) : (UInt256.ofNat x).toNat = x :=
  Nat.mod_eq_of_lt hx

theorem ofNat_val {x : Nat} (hx : x < UInt256.size) : (UInt256.ofNat x).val.val = x :=
  Nat.mod_eq_of_lt hx

theorem wrap_nat (n : Nat) : wrap 256 n = n % UInt256.size := by
  zify; rw [wrap_int]

theorem fin_word {x : Nat} (hx : x < UInt256.size) : (Fin.ofNat UInt256.size x).val = x :=
  Nat.mod_eq_of_lt hx

theorem div_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.div (.ofNat x) (.ofNat y) = UInt256.ofNat (if y = 0 then 0 else x / y) := by
  apply eq_of_toNat
  show (Fin.ofNat _ x).val / (Fin.ofNat _ y).val = (Fin.ofNat _ _ : Fin _).val
  rw [fin_word hx, fin_word hy]
  split_ifs with h
  · simp [h]
  · rw [fin_word (lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem mod_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.mod (.ofNat x) (.ofNat y) = UInt256.ofNat (if y = 0 then 0 else x % y) := by
  unfold UInt256.mod
  by_cases h : y = 0
  · subst h; simp; rfl
  · have : ((UInt256.ofNat y).val == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h'
      have := congrArg Fin.val h'
      rw [ofNat_val hy] at this
      exact h this
    rw [this, if_neg h]
    apply eq_of_toNat
    show (Fin.ofNat _ x).val % (Fin.ofNat _ y).val = (Fin.ofNat _ _ : Fin _).val
    rw [fin_word hx, fin_word hy, fin_word (lt_of_le_of_lt (Nat.mod_le _ _) hx)]

theorem two_pow_256 : (2 : Nat) ^ 256 = UInt256.size := rfl

theorem and_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.land (.ofNat x) (.ofNat y) = UInt256.ofNat (x &&& y) := by
  apply eq_of_toNat
  show (Fin.land (Fin.ofNat _ x) (Fin.ofNat _ y)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.land]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

theorem or_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.lor (.ofNat x) (.ofNat y) = UInt256.ofNat (x ||| y) := by
  apply eq_of_toNat
  show (Fin.lor (Fin.ofNat _ x) (Fin.ofNat _ y)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.lor]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

theorem xor_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.xor (.ofNat x) (.ofNat y) = UInt256.ofNat (x ^^^ y) := by
  apply eq_of_toNat
  show (Fin.xor (Fin.ofNat _ x) (Fin.ofNat _ y)).val = (Fin.ofNat _ _ : Fin _).val
  simp only [Fin.xor]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rfl

theorem shl_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.shiftLeft (.ofNat y) (.ofNat x) =
      UInt256.ofNat (if x ≥ 256 then 0 else wrap 256 (y <<< x : Nat)) := by
  unfold UInt256.shiftLeft
  have h1 : ((UInt256.ofNat x).val ≥ 256) ↔ x ≥ 256 := by
    rw [ge_iff_le, Fin.le_def, ofNat_val hx]; rfl
  by_cases h : x ≥ 256
  · rw [if_pos (h1.mpr h), if_pos h]; rfl
  · rw [if_neg (mt h1.mp h), if_neg h]
    apply eq_of_toNat
    show (Fin.shiftLeft (Fin.ofNat _ y) (Fin.ofNat _ x)).val = (Fin.ofNat _ _ : Fin _).val
    simp only [Fin.shiftLeft, Fin.val_ofNat, wrap_nat, Nat.mod_mod, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hy]

theorem shr_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.shiftRight (.ofNat y) (.ofNat x) = UInt256.ofNat (if x ≥ 256 then 0 else y >>> x) := by
  unfold UInt256.shiftRight
  have h1 : ((UInt256.ofNat x).val ≥ 256) ↔ x ≥ 256 := by
    rw [ge_iff_le, Fin.le_def, ofNat_val hx]; rfl
  by_cases h : x ≥ 256
  · rw [if_pos (h1.mpr h), if_pos h]; rfl
  · rw [if_neg (mt h1.mp h), if_neg h]
    apply eq_of_toNat
    show (Fin.shiftRight (Fin.ofNat _ y) (Fin.ofNat _ x)).val = (Fin.ofNat _ _ : Fin _).val
    simp only [Fin.shiftRight, Fin.val_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem fromBool_eq (b : Bool) : UInt256.fromBool b = UInt256.ofNat (if b then 1 else 0) := by
  cases b <;> rfl

theorem lt_iff_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.ofNat x < UInt256.ofNat y ↔ x < y := by
  show (UInt256.ofNat x).val < (UInt256.ofNat y).val ↔ x < y
  rw [Fin.lt_def, ofNat_val hx, ofNat_val hy]

theorem lt_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.lt (.ofNat x) (.ofNat y) = UInt256.ofNat (if x < y then 1 else 0) := by
  rw [UInt256.lt, fromBool_eq]; simp [lt_iff_word hx hy]

theorem gt_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.gt (.ofNat x) (.ofNat y) = UInt256.ofNat (if x > y then 1 else 0) := by
  rw [UInt256.gt, fromBool_eq]; simp [gt_iff_lt, lt_iff_word hy hx]

theorem eq_word {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.eq (.ofNat x) (.ofNat y) = UInt256.ofNat (if x = y then 1 else 0) := by
  rw [UInt256.eq, fromBool_eq]
  by_cases h : x = y
  · subst h; simp
  · have : UInt256.ofNat x ≠ UInt256.ofNat y := fun h' => h (by
      simpa [toNat_ofNat_lt hx, toNat_ofNat_lt hy] using congrArg UInt256.toNat h')
    simp [h, this]

theorem isZero_word {x : Nat} (hx : x < UInt256.size) :
    UInt256.isZero (.ofNat x) = UInt256.ofNat (if x = 0 then 1 else 0) := by
  have := isZero_toNat (UInt256.ofNat x)
  rw [toNat_ofNat_lt hx] at this
  rw [UInt256.isZero, fromBool_eq]
  rw [UInt256.isZero, fromBool_toNat] at this
  rw [this]; simp

theorem not_word {x : Nat} (hx : x < UInt256.size) :
    UInt256.lnot (.ofNat x) = UInt256.ofNat (2 ^ 256 - 1 - x) := by
  rw [UInt256.lnot]
  show UInt256.sub _ _ = _
  rw [sub_word (by decide) hx]
  congr 1
  rw [size_eq] at hx
  zify [show x ≤ 2 ^ 256 - 1 by omega]
  rw [wrap_int, size_eq]
  push_cast
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem signed_lt {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.sltBool (.ofNat x) (.ofNat y) = decide (signed 256 x < signed 256 y) := by
  simp only [UInt256.sltBool, toNat_ofNat_lt hx, toNat_ofNat_lt hy, lt_iff_word hx hy, signed]
  rw [size_eq] at hx hy
  simp only [show (256 : Nat) - 1 = 255 from rfl]
  split_ifs <;> first
    | (simp only [decide_eq_decide]; omega)
    | (symm; simp only [decide_eq_true_eq]; omega)
    | (symm; simp only [decide_eq_false_iff_not]; omega)

theorem signed_gt {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.sgtBool (.ofNat x) (.ofNat y) = decide (signed 256 x > signed 256 y) := by
  simp only [UInt256.sgtBool, toNat_ofNat_lt hx, toNat_ofNat_lt hy, gt_iff_lt, lt_iff_word hy hx,
    signed]
  rw [size_eq] at hx hy
  simp only [show (256 : Nat) - 1 = 255 from rfl]
  split_ifs <;> first
    | (simp only [decide_eq_decide]; omega)
    | (symm; simp only [decide_eq_true_eq]; omega)
    | (symm; simp only [decide_eq_false_iff_not]; omega)

/-- A pure binary instruction of the class computes on words what its opcode does. -/
theorem bin_word {ee : ExecutionEnv} {op : BinOp} {opc : Operation} (h : binOpcode op = some opc)
    {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    opEval ee opc [.ofNat x, .ofNat y] = some (.ofNat (op.eval 256 x y)) := by
  cases op <;> simp only [binOpcode, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [opEval, evalOp, envOp, BinOp.eval]
  · rw [add_word]; rfl
  · rw [sub_word hx hy]; rfl
  · rw [mul_word]; rfl
  · rw [shl_word hx hy]; rfl
  · rw [shr_word hx hy]; rfl
  · rw [and_word hx hy]; rfl
  · rw [or_word hx hy]; rfl
  · rw [xor_word hx hy]; rfl
  · rw [div_word hx hy]; rfl
  · rw [mod_word hx hy]; rfl
  all_goals rw [Reasoning.Theory.u256_ofNat_toNat]; rfl

/-- A comparison of the class computes on words what its opcode does. -/
theorem cmp_word {ee : ExecutionEnv} {op : CmpOp} {opc : Operation} (h : cmpOpcode op = some opc)
    {x y : Nat} (hx : x < UInt256.size) (hy : y < UInt256.size) :
    opEval ee opc [.ofNat x, .ofNat y] = some (.ofNat (if op.eval 256 x y then 1 else 0)) := by
  cases op <;> simp only [cmpOpcode, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [opEval, evalOp, CmpOp.eval]
  · rw [lt_word hx hy]; simp
  · rw [gt_word hx hy]; simp
  · rw [UInt256.slt, signed_lt hx hy, fromBool_eq]; simp
  · rw [UInt256.sgt, signed_gt hx hy, fromBool_eq]; simp
  · rw [eq_word hx hy]; simp

end Fe.Sonatina.Check
