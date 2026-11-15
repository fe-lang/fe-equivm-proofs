import FeProofs.Precompiles.Inverse.Invert256
import FeProofs.Precompiles.Bn254.Field

/-!
# Bn254Add: `Mont::inverse`

The constants of `Bn254Base` for `Invert256.lean`: `SIGNED_62` and `INV62` (`modSpec_Bn`) and
`R3` (`R3_Bn`).  `Mont_inverse_Bn254Base_spec`: every run diverges or returns a representation
of `x⁻¹`, for every `x` (with `0⁻¹ = 0`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

set_option exponentiation.threshold 512

namespace FeProofs.Bn254Add

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Bn254Add

/-- `SIGNED_62` of `Bn254Base`. -/
def mBn : ℕ → ℤ
  | 0 => 4332616871279656263
  | 1 => 2163322412065040948
  | 2 => 361514372735272409
  | 3 => 1806960190875503214
  | _ => 48

theorem val5_mBn : val5 mBn = KBn.p := by
  rw [KBn_p]; simp only [val5, mBn, BN254.p]; norm_num

theorem modSpec_Bn : ModSpec mBn 4048164856291499127 := by
  refine modSpec_of val5_mBn ?_ ?_ (by simp [mBn]) (by rw [KBn_p]; decide) (by decide)
  · intro i hi; interval_cases i <;> simp [mBn]
  · intro i
    match i with
    | 0 | 1 | 2 | 3 => simp [mBn]
    | _ + 4 => simp [mBn]

instance : Fact KBn.p.Prime := ⟨KBn_p ▸ BN254.p_prime⟩

theorem R3_Bn : 14921786541159648185948152738563080959093619838510245177710943249661917737183 =
    (2 ^ 256) ^ 3 % KBn.p := by decide

theorem Bn254Base_SIGNED_62_eq : Bn254Base_SIGNED_62 = pure (vec5 mBn) := rfl
theorem Bn254Base_INV62_eq : Bn254Base_INV62 = pure (Limb.w 4048164856291499127) := rfl

/-- `Mont::inverse` for `Bn254Base`, partial: every run diverges or returns, with the world
unchanged, a representation of `x⁻¹` (`0` for `x = 0`). -/
theorem Mont_inverse_Bn254Base_spec {a : L4} {x : Fq} (ha : RepBn a x) (env : Env) (w : World) :
    (Mont_inverse_Bn254Base (toBn a)).exec env w = none ∨
      ∃ c, (Mont_inverse_Bn254Base (toBn a)).exec env w = some (.ok (toBn c, w)) ∧
        RepBn c x⁻¹ := by
  have hm := modSpec_Bn
  have hpm : (KBn.p : ℤ) = val5 mBn := val5_mBn.symm
  have ha1 : (Mont.val a : ℤ) < val5 mBn := by rw [← hpm]; exact_mod_cast ha.1
  simp only [Mont_inverse_Bn254Base, Bn254Base_SIGNED_62_eq, Bn254Base_INV62_eq, pure_bind,
    toBn_l0, toBn_l1, toBn_l2, toBn_l3]
  rw [Fe.M.exec_bind]
  rcases invert_256_spec hm (by rw [← hpm]; decide) a ha1
    (fun h => by rw [← hpm]; exact coprime_of_lt (Fact.out) h (by exact_mod_cast ha.1)) env w
    with h | ⟨c, h, hc, hinv⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    simp only [checkIndex, idx_lits, lt4, ite_true, pure_bind, vget4, mk_toBn, Bn254Base_R3,
      raw_Bn254Base_eq, mul_Bn254Base,
      toNat_lit (show 14921786541159648185948152738563080959093619838510245177710943249661917737183 <
        2 ^ 256 by decide), Fe.M.exec_pure]
    refine Or.inr ⟨_, rfl, ?_⟩
    show Mont.Rep KBn _ (FBn.toK x⁻¹)
    rw [map_inv₀]
    exact inverse_rep KBn_valid R3_Bn ha (by have := hc; rw [← hpm] at this; exact_mod_cast this)
      (by rw [hpm]; exact hinv)

end FeProofs.Bn254Add
