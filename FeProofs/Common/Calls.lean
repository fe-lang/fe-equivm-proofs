import Reasoning.EVMWord
import Reasoning.Stepping

/-!
# External calls

Fe checks a call's return data with `RETURNDATASIZE < 32`; these are that comparison's outcomes.
-/

open Ethereum Reasoning.Theory

namespace FeProofs

theorem lt32_size_word {n : ℕ} (hn : 32 ≤ n) (hb : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) = UInt256.ofNat 0 := by
  have hw : ¬ (UInt256.ofNat n < UInt256.ofNat 32) := by
    rw [ofNat_lt_ofNat hb (by decide)]; omega
  simp only [UInt256.lt, decide_eq_false hw]; decide

theorem lt32_size_word_ne {n : ℕ} (hn : n < 32) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) ≠ UInt256.ofNat 0 := by
  have hw : UInt256.ofNat n < UInt256.ofNat 32 :=
    (ofNat_lt_ofNat (lt_trans hn (by decide)) (by decide)).mpr hn
  simp only [UInt256.lt, decide_eq_true hw]; decide

end FeProofs
