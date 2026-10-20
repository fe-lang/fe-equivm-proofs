import FeProofs.Deposit.DepositHead
import FeProofs.Deposit.DepositChecks
import FeProofs.Deposit.DepositDecode
import Reasoning.WordArithmetic
import Reasoning.EVMWord
import Reasoning.Solc

/-!
# FeDeposit decode bridge

Under the calldata-size precondition `size < 2^64`, the word-level decoder checks of
`DepositHead`/`DepositRoutine` coincide with the modern decoder's acceptance (`dArgsOk`), except
that Fe additionally caps lengths at `2^64 - 64`; an accepted argument longer than that fails the
body's length `require` anyway.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

theorem gt_zero_iff (a b : UInt256) : UInt256.gt a b = UInt256.ofNat 0 ↔ a.toNat ≤ b.toNat :=
  ⟨ugt_eq_zero_to_le, ugt_zero⟩

theorem lt_zero_iff (a b : UInt256) : UInt256.lt a b = UInt256.ofNat 0 ↔ b.toNat ≤ a.toNat :=
  ⟨ult_eq_zero_to_le, ult_zero⟩

theorem cds_toNat (I : ExecutionEnv) (hsize : I.calldata.size < UInt256.size) :
    (hCds I).toNat = I.calldata.size := ulit_toNat' _ hsize

theorem hWord_toNat (I : ExecutionEnv) (i : Nat) (hi : 4 + 32 * i < UInt256.size) :
    (hWord I i).toNat = dWord I.calldata (32 * i) := by
  simp only [hWord, dWord, calldataWord, ulit_toNat' _ hi]

theorem lnot4_toNat : (UInt256.lnot (UInt256.ofNat 4)).toNat = 2 ^ 256 - 5 := by
  unfold UInt256.lnot; decide

theorem hPos_toNat (I : ExecutionEnv) (i : Nat)
    (hw : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0) :
    (hPos I i).toNat = 4 + (hWord I i).toNat := by
  have h := ugt_eq_zero_to_le hw
  rw [lnot4_toNat] at h
  rw [hPos, uadd_toNat, ulit_toNat' 4 (by decide), Nat.mod_eq_of_lt (by unfold UInt256.size; omega)]

theorem rLen_toNat (I : ExecutionEnv) (i : Nat)
    (hw : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0) :
    (rLen I (hPos I i)).toNat = dWord I.calldata (hWord I i).toNat := by
  simp only [rLen, dWord, calldataWord, hPos_toNat I i hw]

theorem rAlloc_ge (I : ExecutionEnv) (p : UInt256)
    (h6 : (rLen I p).toNat ≤ 18446744073709551552) :
    32 ≤ (rAlloc I p).toNat := by
  have h63 : (UInt256.ofNat 63).toNat = 63 := by decide
  rw [rAlloc, show UInt256.lnot (UInt256.ofNat 31) = UInt256.lnot ⟨31⟩ from rfl, uland_toNat,
    lnot31_toNat, uadd_toNat, h63, Nat.mod_eq_of_lt (by unfold UInt256.size; omega), Nat.and_comm,
    nat_land_mask _ (by omega)]
  omega

/-- The decoder's checks for argument `i`, as natural-number facts. -/
theorem rOk_iff (I : ExecutionEnv) (i : Nat) (hsmall : I.calldata.size < 2 ^ 64)
    (hw : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0) :
    rOk I (hPos I i) (hCds I) ↔
      (dBytesOk I.calldata (hWord I i).toNat ∧
        dWord I.calldata (hWord I i).toNat ≤ 18446744073709551552) := by
  have hS := cds_toNat I (by unfold UInt256.size; omega)
  have hP := hPos_toNat I i hw
  have hL := rLen_toNat I i hw
  have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
  have hmax : (UInt256.ofNat 18446744073709551552).toNat = 18446744073709551552 := by decide
  unfold rOk dBytesOk
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    rw [gt_zero_iff, hS, hP] at h1
    rw [gt_zero_iff, h32, usub_toNat (by rw [hS, hP]; omega), hS, hP] at h2
    rw [gt_zero_iff, hL, hmax] at h6
    have hp32 : (hPos I i + UInt256.ofNat 32).toNat = 4 + (hWord I i).toNat + 32 := by
      rw [uadd_toNat, hP, h32, Nat.mod_eq_of_lt (by unfold UInt256.size; omega)]
    rw [gt_zero_iff, hL, usub_toNat (by rw [hS, hp32]; omega), hS, hp32] at h5
    exact ⟨⟨by omega, by omega⟩, h6⟩
  · rintro ⟨⟨hb1, hb2⟩, h6⟩
    have hp32 : (hPos I i + UInt256.ofNat 32).toNat = 4 + (hWord I i).toNat + 32 := by
      rw [uadd_toNat, hP, h32, Nat.mod_eq_of_lt (by unfold UInt256.size; omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gt_zero_iff, hS, hP]; omega
    · rw [gt_zero_iff, h32, usub_toNat (by rw [hS, hP]; omega), hS, hP]; omega
    · rw [lt_zero_iff, hp32, hP]; omega
    · rw [lt_zero_iff, hp32, hS]; omega
    · rw [gt_zero_iff, hL, usub_toNat (by rw [hS, hp32]; omega), hS, hp32]; omega
    · rw [gt_zero_iff, hL, hmax]; exact h6
    · rw [ult_zero (by rw [h32]; exact rAlloc_ge I _ (by rw [hL]; exact h6))]; decide

/-- The length of `bytes` argument `i`. -/
abbrev dLen (cd : ByteArray) (i : Nat) : Nat := dWord cd (dWord cd (32 * i))

theorem headCheck_iff (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 64) :
    UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 128) =
      UInt256.ofNat 0 ↔ 132 ≤ I.calldata.size := by
  constructor
  · intro h
    by_contra hlt
    have h1 := solcCalldataStaticLenCheckShort (words := 4) hsz (by omega)
      (by unfold UInt256.size; omega) (by norm_num)
    have hc : (⟨1⟩ : UInt256) = UInt256.ofNat 0 := h1.symm.trans h
    exact absurd hc (by decide)
  · intro h
    exact solcCalldataStaticLenCheckOk (words := 4) (by omega) (by omega)
      (by unfold UInt256.size; omega)

theorem hw_of_bound (I : ExecutionEnv) (i : Nat) (hsmall : I.calldata.size < 2 ^ 64)
    (hb : 4 + (hWord I i).toNat + 32 ≤ I.calldata.size) :
    UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 := by
  rw [gt_zero_iff, lnot4_toNat]; omega

/-- Fe's decoder accepts exactly when the modern decoder does and every length is at most
    `2^64 - 64`. -/
theorem hOk_iff (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 64) :
    hOk I ↔ (dArgsOk I.calldata ∧ dLen I.calldata 0 ≤ 18446744073709551552 ∧
      dLen I.calldata 1 ≤ 18446744073709551552 ∧ dLen I.calldata 2 ≤ 18446744073709551552) := by
  have hw0 := hWord_toNat I 0 (by decide)
  have hw1 := hWord_toNat I 1 (by decide)
  have hw2 := hWord_toNat I 2 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one] at hw0 hw1 hw2
  rw [show 32 * 2 = 64 from rfl] at hw2
  unfold hOk dArgsOk dLen
  simp only [Nat.mul_zero, Nat.mul_one, show 32 * 2 = 64 from rfl]
  constructor
  · rintro ⟨hh, hg0, hr0, hg1, hr1, hg2, hr2⟩
    rw [rOk_iff I 0 hsmall hg0, hw0] at hr0
    rw [rOk_iff I 1 hsmall hg1, hw1] at hr1
    rw [rOk_iff I 2 hsmall hg2, hw2] at hr2
    exact ⟨⟨(headCheck_iff I hsz hsmall).mp hh, hr0.1, hr1.1, hr2.1⟩, hr0.2, hr1.2, hr2.2⟩
  · rintro ⟨⟨hn, hb0, hb1, hb2⟩, hc0, hc1, hc2⟩
    have hg0 := hw_of_bound I 0 hsmall (by rw [hw0]; exact hb0.1)
    have hg1 := hw_of_bound I 1 hsmall (by rw [hw1]; exact hb1.1)
    have hg2 := hw_of_bound I 2 hsmall (by rw [hw2]; exact hb2.1)
    refine ⟨(headCheck_iff I hsz hsmall).mpr hn, hg0, ?_, hg1, ?_, hg2, ?_⟩
    · rw [rOk_iff I 0 hsmall hg0, hw0]; exact ⟨hb0, hc0⟩
    · rw [rOk_iff I 1 hsmall hg1, hw1]; exact ⟨hb1, hc1⟩
    · rw [rOk_iff I 2 hsmall hg2, hw2]; exact ⟨hb2, hc2⟩

/-- On acceptance, the decoded lengths on the EVM stack are the Stele argument lengths. -/
theorem hLen_toNat (I : ExecutionEnv) (i : Nat) (hi : 4 + 32 * i < UInt256.size)
    (hg : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0) :
    (rLen I (hPos I i)).toNat = dLen I.calldata i := by
  rw [rLen_toNat I i hg, hWord_toNat I i hi]

end FeProofs.Deposit
