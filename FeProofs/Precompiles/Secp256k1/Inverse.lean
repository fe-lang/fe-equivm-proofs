import FeProofs.Precompiles.Inverse.Invert256
import FeProofs.Precompiles.Secp256k1.Field

/-!
# Ecrecover: `Mont::inverse` at the two moduli

The constants of the two moduli for `Invert256.lean`: `SIGNED_62` and `INV62` (`modSpec_B`,
`modSpec_O`) and `R3` (`R3_B`, `R3_O`).  `Mont_inverse_Base_spec` and `Mont_inverse_Order_spec`:
every run diverges or returns a representation of `x⁻¹`, for every `x` (with `0⁻¹ = 0`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

open Precompiles.Exported.Shared Precompiles.Exported.Ecrecover

/-! ## The two moduli -/

/-- `SIGNED_62` of `Base`. -/
def mB : ℕ → ℤ
  | 0 => 4611686014132419631
  | 1 => 4611686018427387903
  | 2 => 4611686018427387903
  | 3 => 4611686018427387903
  | _ => 255

/-- `SIGNED_62` of `Order`. -/
def mO : ℕ → ℤ
  | 0 => 4598842128380346689
  | 1 => 3079181878673178862
  | 2 => 4611686018427387883
  | 3 => 4611686018427387903
  | _ => 255

theorem val5_mB : val5 mB = KB.p := by
  rw [KB_p]; simp only [val5, mB, Secp256k1.p]; norm_num

theorem val5_mO : val5 mO = KO.p := by
  rw [KO_p]; simp only [val5, mO, Secp256k1.n]; norm_num

theorem modSpec_B : ModSpec mB 2866531139136965327 := by
  refine modSpec_of val5_mB ?_ ?_ (by simp [mB]) (by rw [KB_p]; decide) (by decide)
  · intro i hi; interval_cases i <;> simp [mB]
  · intro i
    match i with
    | 0 | 1 | 2 | 3 => simp [mB]
    | _ + 4 => simp [mB]

theorem modSpec_O : ModSpec mO 3815112494326173377 := by
  refine modSpec_of val5_mO ?_ ?_ (by simp [mO]) (by rw [KO_p]; decide) (by decide)
  · intro i hi; interval_cases i <;> simp [mO]
  · intro i
    match i with
    | 0 | 1 | 2 | 3 => simp [mO]
    | _ + 4 => simp [mO]

instance : Fact KB.p.Prime := ⟨KB_p ▸ Secp256k1.p_prime⟩
instance : Fact KO.p.Prime := ⟨KO_p ▸ Secp256k1.n_prime⟩

theorem R3_B : 79228216581683516649686562417 = (2 ^ 256) ^ 3 % KB.p := by decide
theorem R3_O : 38611792656279623856209604949727965891812033543773964974832218758873530450413 =
    (2 ^ 256) ^ 3 % KO.p := by decide

instance : Fact (Nat.Prime Secp256k1.n) := ⟨Secp256k1.n_prime⟩

theorem Base_SIGNED_62_eq : Base_SIGNED_62 = pure (vec5 mB) := rfl
theorem Order_SIGNED_62_eq : Order_SIGNED_62 = pure (vec5 mO) := rfl
theorem Base_INV62_eq : Base_INV62 = pure (Limb.w 2866531139136965327) := rfl
theorem Order_INV62_eq : Order_INV62 = pure (Limb.w 3815112494326173377) := rfl

/-- `Mont::inverse` for `Base` (the field), partial: every run diverges or returns, with the
world unchanged, a representation of `x⁻¹` (`0` for `x = 0`). -/
theorem Mont_inverse_Base_spec {a : L4} {x : Fp} (ha : RepB a x) (env : Env) (w : World) :
    (Mont_inverse_Base (toB a)).exec env w = none ∨
      ∃ c, (Mont_inverse_Base (toB a)).exec env w = some (.ok (toB c, w)) ∧ RepB c x⁻¹ := by
  have hm := modSpec_B
  have hpm : (KB.p : ℤ) = val5 mB := val5_mB.symm
  have ha1 : (Mont.val a : ℤ) < val5 mB := by rw [← hpm]; exact_mod_cast ha.1
  simp only [Mont_inverse_Base, Base_SIGNED_62_eq, Base_INV62_eq, pure_bind, toB_l0, toB_l1,
    toB_l2, toB_l3]
  rw [Fe.M.exec_bind]
  rcases invert_256_spec hm (by rw [← hpm]; decide) a ha1
    (fun h => by rw [← hpm]; exact coprime_of_lt (Fact.out) h (by exact_mod_cast ha.1)) env w
    with h | ⟨c, h, hc, hinv⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    simp only [checkIndex, idx_lits, lt4, ite_true, pure_bind, vget4, mk_toB, Base_R3,
      raw_Base_eq, mul_Base, toNat_lit (show 79228216581683516649686562417 < 2 ^ 256 by decide),
      Fe.M.exec_pure]
    refine Or.inr ⟨_, rfl, ?_⟩
    rw [RepB, map_inv₀]
    exact inverse_rep KB_valid R3_B ha (by have := hc; rw [← hpm] at this; exact_mod_cast this) (by rw [hpm]; exact hinv)

/-- `Mont::inverse` for `Order` (the scalars), partial: every run diverges or returns, with the
world unchanged, a representation of `s⁻¹` (`0` for `s = 0`). -/
theorem Mont_inverse_Order_spec {a : L4} {s : Fn} (ha : RepO a s) (env : Env) (w : World) :
    (Mont_inverse_Order (toO a)).exec env w = none ∨
      ∃ c, (Mont_inverse_Order (toO a)).exec env w = some (.ok (toO c, w)) ∧ RepO c s⁻¹ := by
  have hm := modSpec_O
  have hpm : (KO.p : ℤ) = val5 mO := val5_mO.symm
  have ha1 : (Mont.val a : ℤ) < val5 mO := by rw [← hpm]; exact_mod_cast ha.1
  simp only [Mont_inverse_Order, Order_SIGNED_62_eq, Order_INV62_eq, pure_bind, toO_l0, toO_l1,
    toO_l2, toO_l3]
  rw [Fe.M.exec_bind]
  rcases invert_256_spec hm (by rw [← hpm]; decide) a ha1
    (fun h => by rw [← hpm]; exact coprime_of_lt (Fact.out) h (by exact_mod_cast ha.1)) env w
    with h | ⟨c, h, hc, hinv⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    simp only [checkIndex, idx_lits, lt4, ite_true, pure_bind, vget4, mk_toO, Order_R3,
      raw_Order_eq, mul_Order,
      toNat_lit (show 38611792656279623856209604949727965891812033543773964974832218758873530450413 <
        2 ^ 256 by decide), Fe.M.exec_pure]
    refine Or.inr ⟨_, rfl, ?_⟩
    rw [RepO, map_inv₀]
    exact inverse_rep KO_valid R3_O ha (by have := hc; rw [← hpm] at this; exact_mod_cast this) (by rw [hpm]; exact hinv)

end FeProofs.Ecrecover
