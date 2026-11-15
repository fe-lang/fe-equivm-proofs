import FeProofs.Precompiles.Modexp.SmallMul
import Mathlib.Data.Nat.ModEq

/-!
# Modexp: the Montgomery form of `Small<L>`

Limbs `x` stand for `a` in Montgomery form when `x < M` and `x ≡ a R (mod M)`, `R = 2 ^ (64 L)`
coprime to the odd `M`.  `smul` of two such stands for the product (`mrep_mul`), and `smul` by one
leaves the form (`mrep_out`): what `small_power` needs from the multiplication, whatever the
exponent walk.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- `x` stands for `a` modulo `nat4 m` in Montgomery form at `R`. -/
def MRep (R : ℕ) (m x : L4) (a : ℕ) : Prop := nat4 x < nat4 m ∧ nat4 x ≡ a * R [MOD nat4 m]

theorem mrep_mul (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m x y : L4) (inv : Limb) (a b : ℕ)
    (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ (64 * L))
    (hcop : Nat.Coprime (2 ^ (64 * L)) (nat4 m))
    (hx : MRep (2 ^ (64 * L)) m x a) (hy : MRep (2 ^ (64 * L)) m y b) :
    MRep (2 ^ (64 * L)) m (smul L m inv x y) (a * b) := by
  obtain ⟨hxl, hxa⟩ := hx
  obtain ⟨hyl, hyb⟩ := hy
  have hxy : nat4 x * nat4 y < 2 ^ (64 * L) * nat4 m :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hxl hyl.le (by omega))
      (Nat.mul_le_mul_right _ hm.le)
  obtain ⟨hc, hcr⟩ := smul_spec L hL m x y inv hinv hm (by omega) (by omega) hxy
  refine ⟨hc, ?_⟩
  have h1 : nat4 (smul L m inv x y) * 2 ^ (64 * L) ≡ (a * b * 2 ^ (64 * L)) * 2 ^ (64 * L)
      [MOD nat4 m] := by
    calc nat4 (smul L m inv x y) * 2 ^ (64 * L) ≡ nat4 x * nat4 y [MOD nat4 m] := hcr
      _ ≡ (a * 2 ^ (64 * L)) * (b * 2 ^ (64 * L)) [MOD nat4 m] := Nat.ModEq.mul hxa hyb
      _ = (a * b * 2 ^ (64 * L)) * 2 ^ (64 * L) := by ring
  exact Nat.ModEq.cancel_right_of_coprime (by
    rw [Nat.coprime_comm] at hcop; exact Nat.Coprime.gcd_eq_one hcop) h1

/-- One, the multiplier that leaves the form. -/
def one4 : L4 := ⟨1, 0, 0, 0⟩

theorem nat4_one4 : nat4 one4 = 1 := by simp [nat4, one4]

/-- **Out of the form**: `smul` by one of limbs that stand for `a` is `a mod M`. -/
theorem mrep_out (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m x : L4) (inv : Limb) (a : ℕ)
    (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ (64 * L)) (hm1 : 1 < nat4 m)
    (hcop : Nat.Coprime (2 ^ (64 * L)) (nat4 m)) (hx : MRep (2 ^ (64 * L)) m x a) :
    nat4 (smul L m inv x one4) = a % nat4 m := by
  obtain ⟨hxl, hxa⟩ := hx
  have hxy : nat4 x * nat4 one4 < 2 ^ (64 * L) * nat4 m := by
    rw [nat4_one4, Nat.mul_one]
    exact lt_of_lt_of_le hxl (Nat.le_mul_of_pos_left _ (by positivity))
  obtain ⟨hc, hcr⟩ := smul_spec L hL m x one4 inv hinv hm (by omega)
    (by rw [nat4_one4]; exact lt_of_lt_of_le hm1 hm.le) hxy
  rw [nat4_one4, Nat.mul_one] at hcr
  have h1 : nat4 (smul L m inv x one4) * 2 ^ (64 * L) ≡ a * 2 ^ (64 * L) [MOD nat4 m] :=
    hcr.trans hxa
  have h2 := Nat.ModEq.cancel_right_of_coprime (by
    rw [Nat.coprime_comm] at hcop; exact Nat.Coprime.gcd_eq_one hcop) h1
  rw [Nat.ModEq, Nat.mod_eq_of_lt hc] at h2
  exact h2

end FeProofs.Modexp
