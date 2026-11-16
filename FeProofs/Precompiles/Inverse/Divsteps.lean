import FeProofs.Precompiles.Inverse.Signed

/-!
# Precompiles: `divsteps`

`divsteps` runs 62 divsteps of Bernstein and Yang on the low words `f0, g0` of `f, g` and
returns the transition matrix `[u v; q r]`, scaled by `2 ^ 62`.  Its state is `DS`: the matrix,
the running `f` and `g` as `u64` limbs, the count `left` of divsteps to go, and `eta`.  One pass
of the exported loop is `DS.shift` (remove the trailing zeros of `g`, up to `left`), then, when
divsteps remain, `DS.swap` if `eta < 0` and `DS.cancel` (add the multiple of `f` that clears up
to six or four low bits of `g`), in `b1_step`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

open Precompiles.Exported.Shared

/-- The state of the loop of `divsteps`. -/
structure DS where
  u : Limb
  v : Limb
  q : Limb
  r : Limb
  f : Limb
  g : Limb
  left : Limb
  eta : ℤ

/-- The exported loop at a state; its last argument, the bit mask, is overwritten before use. -/
abbrev DS.run (s : DS) (bits : UInt256) : FeM (UInt256 × Transition) :=
  divsteps.loop s.u.w s.v.w s.q.w s.r.w s.f.w s.g.w (I s.eta) s.left.w bits

/-- The number of zeros `shift` removes: the trailing zeros of `g`, at most `left`. -/
def DS.zeros (s : DS) : Limb := (s.g ||| Limb.shl 18446744073709551615 s.left.val).tz

/-- Remove `zeros` trailing zeros of `g`, doubling `u` and `v` as often. -/
def DS.shift (s : DS) : DS :=
  { s with g := s.g.shr s.zeros.val, u := s.u.shl s.zeros.val, v := s.v.shl s.zeros.val,
           eta := (s.eta - s.zeros.sgn).bmod (2 ^ 64), left := s.left - s.zeros }

/-- For `eta < 0`: negate `eta` and replace `(f, g)` with `(g, -f)`, and the rows likewise. -/
def DS.swap (s : DS) : DS :=
  { s with eta := (0 - s.eta).bmod (2 ^ 64), f := s.g, g := 0 - s.f, u := s.q, q := 0 - s.u,
           v := s.r, r := 0 - s.v }

/-- How many low bits of `g` `cancel` clears: `bits` masks six (`63`) or four (`15`). -/
def DS.mask (s : DS) (bits : Limb) : Limb :=
  let room := Limb.ofInt ((s.eta + 1).bmod (2 ^ 64))
  let limit := if room.val < s.left.val then room else s.left
  Limb.shr 18446744073709551615 (64 - limit).val &&& bits

/-- The multiple of `f` that clears the masked low bits of `g`. -/
def DS.mult (s : DS) (bits : Limb) : Limb :=
  if bits = 63 then s.f * s.g * (s.f * s.f - 2) &&& s.mask bits
  else (0 - (s.f + Limb.shl ((s.f + 1) &&& 4) 1)) * s.g &&& s.mask bits

/-- Add `mult` times `f` to `g`, and the first row to the second as often. -/
def DS.cancel (s : DS) (bits : Limb) : DS :=
  { s with g := s.g + s.f * s.mult bits, q := s.q + s.u * s.mult bits,
           r := s.r + s.v * s.mult bits }

/-- What `divsteps` returns from a state with no divsteps left. -/
def DS.out (s : DS) : UInt256 × Transition :=
  (I s.eta, ⟨I s.u.sgn, I s.v.sgn, I s.q.sgn, I s.r.sgn⟩)

theorem bmod_range (x : ℤ) : -2 ^ 255 ≤ x.bmod (2 ^ 64) ∧ x.bmod (2 ^ 64) < 2 ^ 255 := by
  have h1 := Int.le_bmod (x := x) (m := 2 ^ 64) (by decide)
  have h2 := Int.bmod_lt (x := x) (m := 2 ^ 64) (by decide)
  simp only [Nat.reducePow] at h1 h2 ⊢
  constructor <;> omega

theorem lit_max : UInt256.ofNat 18446744073709551615 = Limb.w 18446744073709551615 := rfl
theorem lit_64 : UInt256.ofNat 64 = Limb.w 64 := rfl
theorem lit_63 : UInt256.ofNat 63 = Limb.w 63 := rfl
theorem lit_15 : UInt256.ofNat 15 = Limb.w 15 := rfl
theorem lit_4 : UInt256.ofNat 4 = Limb.w 4 := rfl
theorem lit_2 : UInt256.ofNat 2 = Limb.w 2 := rfl
theorem lit_1 : UInt256.ofNat 1 = Limb.w 1 := rfl
theorem lit_0 : UInt256.ofNat 0 = Limb.w 0 := rfl

theorem I_zero : Limb.w 0 = I 0 := rfl
theorem I_one : Limb.w 1 = I 1 := rfl

theorem subW_i64 (x y : ℤ) :
    IntTy.subW (.i 64) (I (x.bmod (2 ^ 64))) (I (y.bmod (2 ^ 64))) =
      I ((x.bmod (2 ^ 64) - y.bmod (2 ^ 64)).bmod (2 ^ 64)) :=
  subW_i 64 (by decide) (bmod_range x).1 (bmod_range x).2 (bmod_range y).1 (bmod_range y).2

theorem subW_i64_zero (x : ℤ) :
    IntTy.subW (.i 64) (Limb.w 0) (I (x.bmod (2 ^ 64))) = I ((0 - x.bmod (2 ^ 64)).bmod (2 ^ 64)) := by
  rw [I_zero]
  exact subW_i 64 (by decide) (by norm_num) (by norm_num) (bmod_range x).1 (bmod_range x).2

theorem addW_i64_one (x : ℤ) :
    IntTy.addW (.i 64) (I (x.bmod (2 ^ 64))) (Limb.w 1) = I ((x.bmod (2 ^ 64) + 1).bmod (2 ^ 64)) := by
  rw [I_one]
  exact addW_i 64 (by decide) (bmod_range x).1 (bmod_range x).2 (by norm_num) (by norm_num)

theorem sltBool_i64 (x : ℤ) :
    UInt256.sltBool (I (x.bmod (2 ^ 64))) (Limb.w 0) = decide (x.bmod (2 ^ 64) < 0) := by
  rw [show Limb.w 0 = UInt256.ofNat 0 from rfl]
  exact sltBool_I_zero (bmod_range x).1 (bmod_range x).2

/-- One pass of the exported loop. -/
theorem b1_step (s : DS) (bits : UInt256) (he : s.eta.bmod (2 ^ 64) = s.eta) :
    s.run bits =
      if s.shift.left = 0 then pure s.shift.out
      else if s.shift.eta < 0 then (s.shift.swap.cancel 63).run (Limb.w 63)
      else (s.shift.cancel 15).run (Limb.w 15) := by
  rw [DS.run, divsteps.loop.eq_1, ← he]
  simp only [lit_max, lit_64, lit_63, lit_15, lit_4, lit_2, lit_1, lit_0, shl_w, shr_w, lor_w, tz_w, land_w, addW_w, subW_w, mulW_w,
    downcast_u64_i64_w, Limb.sgn, pure_bind, subW_i64, subW_i64_zero, addW_i64_one, sltBool_i64,
    downcast_i64_u64_I, Limb.toNat_w, Limb.w_inj, decide_true, if_true]
  have h15 : ((15 : Limb) = 63) = False := by decide
  simp only [DS.shift, DS.swap, DS.cancel, DS.mult, DS.mask, DS.out, DS.run, DS.zeros, Limb.sgn,
    he, decide_eq_true_eq, h15, if_true, if_false]
  split_ifs <;> rfl

end FeProofs.Precompiles
