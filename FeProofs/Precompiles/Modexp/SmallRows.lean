import FeProofs.Precompiles.Modexp.SmallPure

/-!
# Modexp: what one CIOS row of `Small<L>` computes

For `L = 2, 3, 4`, `rowL m inv a b t top` adds `a b` (for one limb `b`) to the `L + 1`-limb
`T = t + βᴸ top`, then the multiple `q m` of the modulus whose low limb cancels, and shifts the
sum down a limb (`row2_spec` and the rest): `β T' = T + a b + q m`.  It needs only
`inv m0 ≡ -1 (mod β)` (`InvOk`); the top limb never wraps, since its carries are at most one.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- `inv = -m0⁻¹ mod β`. -/
def InvOk (m0 inv : Limb) : Prop := (m0.val * inv.val) % 2 ^ 64 = 2 ^ 64 - 1

/-- The multiple of the modulus that cancels a low limb `t0` leaves no low limb. -/
theorem macLo_cancel (m0 inv t0 : Limb) (h : InvOk m0 inv) :
    (macLo (mulLo t0 inv) m0 t0 0).val = 0 := by
  simp only [macLo, mulLo, InvOk] at *
  show (t0.val * inv.val % 2 ^ 64 * m0.val + t0.val + (0 : Limb).val) % 2 ^ 64 = 0
  rw [show ((0 : Limb).val) = 0 from rfl, Nat.add_zero, ← Nat.mod_add_mod, Nat.mod_mul_mod,
    Nat.mul_assoc, ← Nat.mul_mod_mod, Nat.mul_comm inv.val m0.val, h, Nat.mod_add_mod,
    show t0.val * (2 ^ 64 - 1) + t0.val = t0.val * 2 ^ 64 by
      rw [Nat.mul_sub, Nat.mul_one]; have := t0.isLt; omega]
  exact Nat.mul_mod_left _ _

theorem adcHi_le_one' (a b : Limb) : (adcHi a b 0).val ≤ 1 := adcHi_le_one (by decide)

theorem adcHi_zero_le (a c : Limb) : (adcHi a 0 c).val ≤ 1 := by
  have := a.isLt; have := c.isLt
  simp only [adcHi, show ((0 : Limb).val) = 0 from rfl]
  rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; omega

/-- **Row of two limbs.** -/
theorem row2_spec (m a t : L4) (inv b top : Limb) (h : InvOk m.l0 inv) :
    let x := row2 m inv a b t top
    x.1.l2 = 0 ∧ x.1.l3 = 0 ∧
    2 ^ 64 * (x.1.l0.val + 2 ^ 64 * x.1.l1.val + 2 ^ 128 * x.2.val) =
      t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * top.val + (a.l0.val + 2 ^ 64 * a.l1.val) * b.val +
      (mulLo (macLo a.l0 b t.l0 0) inv).val * (m.l0.val + 2 ^ 64 * m.l1.val) := by
  intro x
  refine ⟨rfl, rfl, ?_⟩
  simp only [x, row2]
  generalize hq : mulLo (macLo a.l0 b t.l0 0) inv = q
  have m1 := macLo_add_macHi a.l0 b t.l0 0
  have m2 := macLo_add_macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)
  have a3 := adcLo_add_adcHi top (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)) 0
  have m4 := macLo_add_macHi q m.l0 (macLo a.l0 b t.l0 0) 0
  have h4 := macLo_cancel m.l0 inv (macLo a.l0 b t.l0 0) h
  rw [hq] at h4
  have m5 := macLo_add_macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0))
    (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)
  have a6 := adcLo_add_adcHi (adcLo top (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)) 0) 0
    (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))
  have c6 := adcHi_zero_le (adcLo top (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)) 0)
    (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))
  have t3 := adcHi_le_one' top (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))
  rw [show (a.l0.val + 2 ^ 64 * a.l1.val) * b.val = a.l0.val * b.val + 2 ^ 64 * (a.l1.val * b.val) by
    ring, show q.val * (m.l0.val + 2 ^ 64 * m.l1.val) = q.val * m.l0.val + 2 ^ 64 * (q.val * m.l1.val)
    by ring]
  simp only [addMod, show ((0 : Limb).val) = 0 from rfl] at *
  omega

/-- **Row of 3 limbs.** -/
theorem row3_spec (m a t : L4) (inv b top : Limb) (h : InvOk m.l0 inv) :
    let x := row3 m inv a b t top
    x.1.l3 = 0 ∧
    2 ^ 64 * (x.1.l0.val + 2 ^ 64 * x.1.l1.val + 2 ^ 128 * x.1.l2.val + 2 ^ 192 * x.2.val) =
      t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * t.l2.val + 2 ^ 192 * top.val + (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val) * b.val +
      (mulLo (macLo a.l0 b t.l0 0) inv).val * (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val) := by
  intro x
  refine ⟨rfl, ?_⟩
  simp only [x, row3]
  generalize hq : mulLo (macLo a.l0 b t.l0 0) inv = q
  have m0 := macLo_add_macHi a.l0 b t.l0 0
  have m1 := macLo_add_macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)
  have m2 := macLo_add_macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))
  have aK := adcLo_add_adcHi top (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) 0
  have n0 := macLo_add_macHi q m.l0 (macLo a.l0 b t.l0 0) 0
  have n1 := macLo_add_macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)
  have n2 := macLo_add_macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))
  have aL := adcLo_add_adcHi (adcLo top (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) 0) 0 (macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)))
  have cL := adcHi_zero_le (adcLo top (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) 0) (macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)))
  have cK := adcHi_le_one' top (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))
  have h4 := macLo_cancel m.l0 inv (macLo a.l0 b t.l0 0) h
  rw [hq] at h4
  rw [show (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val) * b.val = (a.l0.val * b.val) + 2 ^ 64 * (a.l1.val * b.val) + 2 ^ 128 * (a.l2.val * b.val) by ring,
    show q.val * (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val) = (q.val * m.l0.val) + 2 ^ 64 * (q.val * m.l1.val) + 2 ^ 128 * (q.val * m.l2.val) by ring]
  simp only [addMod, show ((0 : Limb).val) = 0 from rfl] at *
  omega

/-- **Row of 4 limbs.** -/
theorem row4_spec (m a t : L4) (inv b top : Limb) (h : InvOk m.l0 inv) :
    let x := row4 m inv a b t top
    2 ^ 64 * (x.1.l0.val + 2 ^ 64 * x.1.l1.val + 2 ^ 128 * x.1.l2.val + 2 ^ 192 * x.1.l3.val + 2 ^ 256 * x.2.val) =
      t.l0.val + 2 ^ 64 * t.l1.val + 2 ^ 128 * t.l2.val + 2 ^ 192 * t.l3.val + 2 ^ 256 * top.val + (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val + 2 ^ 192 * a.l3.val) * b.val +
      (mulLo (macLo a.l0 b t.l0 0) inv).val * (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val + 2 ^ 192 * m.l3.val) := by
  intro x
  simp only [x, row4]
  generalize hq : mulLo (macLo a.l0 b t.l0 0) inv = q
  have m0 := macLo_add_macHi a.l0 b t.l0 0
  have m1 := macLo_add_macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)
  have m2 := macLo_add_macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))
  have m3 := macLo_add_macHi a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))
  have aK := adcLo_add_adcHi top (macHi a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) 0
  have n0 := macLo_add_macHi q m.l0 (macLo a.l0 b t.l0 0) 0
  have n1 := macLo_add_macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)
  have n2 := macLo_add_macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))
  have n3 := macLo_add_macHi q m.l3 (macLo a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) (macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0)))
  have aL := adcLo_add_adcHi (adcLo top (macHi a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) 0) 0 (macHi q m.l3 (macLo a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) (macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))))
  have cL := adcHi_zero_le (adcLo top (macHi a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) 0) (macHi q m.l3 (macLo a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0)))) (macHi q m.l2 (macLo a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))) (macHi q m.l1 (macLo a.l1 b t.l1 (macHi a.l0 b t.l0 0)) (macHi q m.l0 (macLo a.l0 b t.l0 0) 0))))
  have cK := adcHi_le_one' top (macHi a.l3 b t.l3 (macHi a.l2 b t.l2 (macHi a.l1 b t.l1 (macHi a.l0 b t.l0 0))))
  have h4 := macLo_cancel m.l0 inv (macLo a.l0 b t.l0 0) h
  rw [hq] at h4
  rw [show (a.l0.val + 2 ^ 64 * a.l1.val + 2 ^ 128 * a.l2.val + 2 ^ 192 * a.l3.val) * b.val = (a.l0.val * b.val) + 2 ^ 64 * (a.l1.val * b.val) + 2 ^ 128 * (a.l2.val * b.val) + 2 ^ 192 * (a.l3.val * b.val) by ring,
    show q.val * (m.l0.val + 2 ^ 64 * m.l1.val + 2 ^ 128 * m.l2.val + 2 ^ 192 * m.l3.val) = (q.val * m.l0.val) + 2 ^ 64 * (q.val * m.l1.val) + 2 ^ 128 * (q.val * m.l2.val) + 2 ^ 192 * (q.val * m.l3.val) by ring]
  simp only [addMod, show ((0 : Limb).val) = 0 from rfl] at *
  omega

end FeProofs.Modexp
