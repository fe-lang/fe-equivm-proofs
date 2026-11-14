import FeProofs.Precompiles.Field.Words

/-!
# Precompiles: the Montgomery arithmetic as pure functions

`montgomery.fe` implements `Mont<M>` for a modulus `M` given by constants: the limbs `P0 … P3`
of the modulus, `INV = -p⁻¹ mod 2 ^ 64` and `R2 = 2 ^ 512 mod p`.  The exporter prints one copy
of each method per modulus, `Mont_mul_Base` and `Mont_mul_Order` and so on.  This file writes
each method once, as a pure function of the constants (`Modulus`) on four limbs (`L4`),
following the Fe code step by step: each curve's `Purify.lean` shows that each exported copy is
`pure` of its instance, and `MontCorrect.lean` what the functions compute.
-/

namespace FeProofs.Precompiles

/-- The constants of a modulus that the Montgomery arithmetic reads. -/
structure Modulus where
  P0 : Limb
  P1 : Limb
  P2 : Limb
  P3 : Limb
  INV : Limb
  R2 : ℕ

/-- Four little-endian limbs: the fields of `Mont<M>`. -/
structure L4 where
  l0 : Limb
  l1 : Limb
  l2 : Limb
  l3 : Limb

namespace Mont

variable (K : Modulus)

/-- The four limbs of a word, as `raw` cuts it. -/
def raw (v : ℕ) : L4 :=
  ⟨⟨v % 2 ^ 64, Nat.mod_lt _ (by decide)⟩, ⟨v / 2 ^ 64 % 2 ^ 64, Nat.mod_lt _ (by decide)⟩,
   ⟨v / 2 ^ 128 % 2 ^ 64, Nat.mod_lt _ (by decide)⟩,
   ⟨v / 2 ^ 192 % 2 ^ 64, Nat.mod_lt _ (by decide)⟩⟩

/-- `shift_reduced`: `s` plus the multiple of `p` that clears its low limb, shifted down one
limb, in two carry chains. -/
def shiftReduced (s0 s1 s2 s3 s4 s5 : Limb) : L4 × Limb :=
  let m := mulLo s0 K.INV
  let k0 := mulLo m K.P0
  let j0 := mulHi m K.P0
  let ca := adcHi s0 k0 0
  let u1 := adcLo s1 j0 0
  let cb := adcHi s1 j0 0
  let k1 := mulLo m K.P1
  let j1 := mulHi m K.P1
  let u1' := adcLo u1 k1 ca
  let ca := adcHi u1 k1 ca
  let u2 := adcLo s2 j1 cb
  let cb := adcHi s2 j1 cb
  let k2 := mulLo m K.P2
  let j2 := mulHi m K.P2
  let u2' := adcLo u2 k2 ca
  let ca := adcHi u2 k2 ca
  let u3 := adcLo s3 j2 cb
  let cb := adcHi s3 j2 cb
  let k3 := mulLo m K.P3
  let j3 := mulHi m K.P3
  let u3' := adcLo u3 k3 ca
  let ca := adcHi u3 k3 ca
  let u4 := adcLo s4 j3 cb
  let cb := adcHi s4 j3 cb
  let u4' := adcLo u4 0 ca
  let ca := adcHi u4 0 ca
  let u5 := adcLo s5 cb ca
  (⟨u1', u2', u3', u4'⟩, u5)

/-- `first_row`: `a * b` for one limb `b`, then reduced. -/
def firstRow (a : L4) (b : Limb) : L4 × Limb :=
  let s0 := mulLo b a.l0
  let h0 := mulHi b a.l0
  let l1 := mulLo b a.l1
  let h1 := mulHi b a.l1
  let s1 := adcLo h0 l1 0
  let c := adcHi h0 l1 0
  let l2 := mulLo b a.l2
  let h2 := mulHi b a.l2
  let s2 := adcLo h1 l2 c
  let c := adcHi h1 l2 c
  let l3 := mulLo b a.l3
  let h3 := mulHi b a.l3
  let s3 := adcLo h2 l3 c
  let c := adcHi h2 l3 c
  let s4 := adcLo h3 0 c
  shiftReduced K s0 s1 s2 s3 s4 0

/-- `row`: `t + a * b` for one limb `b`, then reduced. -/
def row (a : L4) (b : Limb) (t : L4) (top : Limb) : L4 × Limb :=
  let l0 := mulLo b a.l0
  let h0 := mulHi b a.l0
  let s0 := adcLo t.l0 l0 0
  let ca := adcHi t.l0 l0 0
  let s1 := adcLo t.l1 h0 0
  let cb := adcHi t.l1 h0 0
  let l1 := mulLo b a.l1
  let h1 := mulHi b a.l1
  let s1' := adcLo s1 l1 ca
  let ca := adcHi s1 l1 ca
  let s2 := adcLo t.l2 h1 cb
  let cb := adcHi t.l2 h1 cb
  let l2 := mulLo b a.l2
  let h2 := mulHi b a.l2
  let s2' := adcLo s2 l2 ca
  let ca := adcHi s2 l2 ca
  let s3 := adcLo t.l3 h2 cb
  let cb := adcHi t.l3 h2 cb
  let l3 := mulLo b a.l3
  let h3 := mulHi b a.l3
  let s3' := adcLo s3 l3 ca
  let ca := adcHi s3 l3 ca
  let s4 := adcLo top h3 cb
  let cb := adcHi top h3 cb
  let s4' := adcLo s4 0 ca
  let ca := adcHi s4 0 ca
  let s5 := adcLo cb 0 ca
  shiftReduced K s0 s1' s2' s3' s4' s5

/-- `reduce`: subtract `p` when the value, with `top` above the four limbs, is at least `p`. -/
def reduce (a : L4) (top : Limb) : L4 :=
  let d0 := sbbLo a.l0 K.P0 0
  let b := sbbHi a.l0 K.P0 0
  let d1 := sbbLo a.l1 K.P1 b
  let b := sbbHi a.l1 K.P1 b
  let d2 := sbbLo a.l2 K.P2 b
  let b := sbbHi a.l2 K.P2 b
  let d3 := sbbLo a.l3 K.P3 b
  let b := sbbHi a.l3 K.P3 b
  let b := sbbHi top 0 b
  if b = 1 then a else ⟨d0, d1, d2, d3⟩

/-- `mul`: Montgomery multiplication, `a * b * 2 ^ -256 mod p`. -/
def mul (a b : L4) : L4 :=
  let (t, top) := firstRow K a b.l0
  let (t, top) := row K a b.l1 t top
  let (t, top) := row K a b.l2 t top
  let (t, top) := row K a b.l3 t top
  reduce K t top

/-- `add`. -/
def add (a b : L4) : L4 :=
  let s0 := adcLo a.l0 b.l0 0
  let c := adcHi a.l0 b.l0 0
  let s1 := adcLo a.l1 b.l1 c
  let c := adcHi a.l1 b.l1 c
  let s2 := adcLo a.l2 b.l2 c
  let c := adcHi a.l2 b.l2 c
  let s3 := adcLo a.l3 b.l3 c
  let c := adcHi a.l3 b.l3 c
  reduce K ⟨s0, s1, s2, s3⟩ c

/-- `sub`: the difference, with `p` added back on a borrow. -/
def sub (a b : L4) : L4 :=
  let d0 := sbbLo a.l0 b.l0 0
  let bw := sbbHi a.l0 b.l0 0
  let d1 := sbbLo a.l1 b.l1 bw
  let bw := sbbHi a.l1 b.l1 bw
  let d2 := sbbLo a.l2 b.l2 bw
  let bw := sbbHi a.l2 b.l2 bw
  let d3 := sbbLo a.l3 b.l3 bw
  let bw := sbbHi a.l3 b.l3 bw
  let s0 := adcLo d0 K.P0 0
  let c := adcHi d0 K.P0 0
  let s1 := adcLo d1 K.P1 c
  let c := adcHi d1 K.P1 c
  let s2 := adcLo d2 K.P2 c
  let c := adcHi d2 K.P2 c
  let s3 := adcLo d3 K.P3 c
  if bw = 1 then ⟨s0, s1, s2, s3⟩ else ⟨d0, d1, d2, d3⟩

/-- `zero`. -/
def zero : L4 := ⟨0, 0, 0, 0⟩

/-- `new` of a canonical `v < p`: `v * R2` reduced, `v * 2 ^ 256 mod p`. -/
def new (v : ℕ) : L4 := mul K (raw v) (raw K.R2)

/-- `value`: the canonical integer, `a * 1` reduced. -/
def value (a : L4) : ℕ :=
  let v := mul K a (raw 1)
  v.l0.val + 2 ^ 64 * v.l1.val + 2 ^ 128 * v.l2.val + 2 ^ 192 * v.l3.val

/-- `is_zero`. -/
def isZero (a : L4) : Bool := a.l0 = 0 && a.l1 = 0 && a.l2 = 0 && a.l3 = 0

/-- `equals`. -/
def equals (a b : L4) : Bool := a.l0 = b.l0 && a.l1 = b.l1 && a.l2 = b.l2 && a.l3 = b.l3

end Mont

end FeProofs.Precompiles
