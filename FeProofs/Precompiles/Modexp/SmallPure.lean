import FeProofs.Precompiles.Modexp.Ops
import FeProofs.Precompiles.Field.MontPure

/-!
# Modexp: Montgomery multiplication in registers, as pure functions

`modexp.fe`'s `Small<L>` multiplies modulo an odd modulus of `L ≤ 4` limbs held in a `Wide` (four
limbs, those from `L` on zero) with `R = 2 ^ (64 L)`.  The exporter prints one copy of each method
per `L`, `Small_mul_1` … `Small_mul_4`, the text of each the same but for the constant `L` its
`if L == …` branches test.  This file writes each method once as a pure function on four limbs
(`L4`), following the Fe code step by step, with `L` a parameter where the code branches on it:
`row2`, `row3`, `row4` (one CIOS row), `smul`, `sdouble`.  `Small.lean` shows that each exported
copy is `pure` of its instance.
-/

namespace FeProofs.Modexp

open FeProofs.Precompiles

/-- The four limbs of a `Wide`. -/
def toW (a : L4) : Precompiles.Exported.Modexp.Wide := ⟨a.l0.w, a.l1.w, a.l2.w, a.l3.w⟩

def Z4 : L4 := ⟨0, 0, 0, 0⟩

/-- `row2`: `t + a b` for one limb `b`, plus the multiple of the modulus that clears the low
    limb, shifted down a limb; `top` is limb `L` of `t`. -/
def row2 (m : L4) (inv : Limb) (a : L4) (b : Limb) (t : L4) (top : Limb) : L4 × Limb :=
  let t0 := macLo a.l0 b t.l0 0
  let c := macHi a.l0 b t.l0 0
  let t1 := macLo a.l1 b t.l1 c
  let c := macHi a.l1 b t.l1 c
  let t2 := adcLo top c 0
  let t3 := adcHi top c 0
  let q := mulLo t0 inv
  let c := macHi q m.l0 t0 0
  let r0 := macLo q m.l1 t1 c
  let c := macHi q m.l1 t1 c
  let r1 := adcLo t2 0 c
  let c := adcHi t2 0 c
  (⟨r0, r1, 0, 0⟩, addMod t3 c)

def row3 (m : L4) (inv : Limb) (a : L4) (b : Limb) (t : L4) (top : Limb) : L4 × Limb :=
  let t0 := macLo a.l0 b t.l0 0
  let c := macHi a.l0 b t.l0 0
  let t1 := macLo a.l1 b t.l1 c
  let c := macHi a.l1 b t.l1 c
  let t2 := macLo a.l2 b t.l2 c
  let c := macHi a.l2 b t.l2 c
  let t3 := adcLo top c 0
  let t4 := adcHi top c 0
  let q := mulLo t0 inv
  let c := macHi q m.l0 t0 0
  let r0 := macLo q m.l1 t1 c
  let c := macHi q m.l1 t1 c
  let r1 := macLo q m.l2 t2 c
  let c := macHi q m.l2 t2 c
  let r2 := adcLo t3 0 c
  let c := adcHi t3 0 c
  (⟨r0, r1, r2, 0⟩, addMod t4 c)

def row4 (m : L4) (inv : Limb) (a : L4) (b : Limb) (t : L4) (top : Limb) : L4 × Limb :=
  let t0 := macLo a.l0 b t.l0 0
  let c := macHi a.l0 b t.l0 0
  let t1 := macLo a.l1 b t.l1 c
  let c := macHi a.l1 b t.l1 c
  let t2 := macLo a.l2 b t.l2 c
  let c := macHi a.l2 b t.l2 c
  let t3 := macLo a.l3 b t.l3 c
  let c := macHi a.l3 b t.l3 c
  let t4 := adcLo top c 0
  let t5 := adcHi top c 0
  let q := mulLo t0 inv
  let c := macHi q m.l0 t0 0
  let r0 := macLo q m.l1 t1 c
  let c := macHi q m.l1 t1 c
  let r1 := macLo q m.l2 t2 c
  let c := macHi q m.l2 t2 c
  let r2 := macLo q m.l3 t3 c
  let c := macHi q m.l3 t3 c
  let r3 := adcLo t4 0 c
  let c := adcHi t4 0 c
  (⟨r0, r1, r2, r3⟩, addMod t5 c)

/-- The final subtraction of `smul`: `t - m` unless that borrows, over `L` limbs and `top`. -/
def ssub (L : ℕ) (m t : L4) (top : Limb) : L4 :=
  let d0 := sbbLo t.l0 m.l0 0
  let b := sbbHi t.l0 m.l0 0
  let d1 := sbbLo t.l1 m.l1 b
  let b' := sbbHi t.l1 m.l1 b
  if L = 2 then (if sbbHi top 0 b' = 1 then t else ⟨d0, d1, 0, 0⟩) else
  let d2 := sbbLo t.l2 m.l2 b'
  let b'' := sbbHi t.l2 m.l2 b'
  if L = 3 then (if sbbHi top 0 b'' = 1 then t else ⟨d0, d1, d2, 0⟩) else
  let d3 := sbbLo t.l3 m.l3 b''
  let b''' := sbbHi t.l3 m.l3 b''
  if sbbHi top 0 b''' = 1 then t else ⟨d0, d1, d2, d3⟩

/-- `Small::mul` for one limb: `a b / R mod m` with `u128` arithmetic. -/
def smul1 (m : L4) (inv : Limb) (a b : L4) : L4 :=
  let t := mulD a.l0 b.l0
  let low := loD t
  let q := mulLo low inv
  let p := mulD q m.l0
  let s := addD (addD (L2D (hiD t)) (L2D (hiD p))) (L2D (if low = 0 then 0 else 1))
  let r := if m.l0.val ≤ s.val then subD s (L2D m.l0) else s
  ⟨loD r, 0, 0, 0⟩

/-- `Small::mul`: `a b / R mod m`, for `a, b < m` or one of them below `R`. -/
def smul (L : ℕ) (m : L4) (inv : Limb) (a b : L4) : L4 :=
  if L = 1 then smul1 m inv a b
  else if L = 2 then
    let x := row2 m inv a b.l0 Z4 0
    let x := row2 m inv a b.l1 x.1 x.2
    ssub 2 m x.1 x.2
  else if L = 3 then
    let x := row3 m inv a b.l0 Z4 0
    let x := row3 m inv a b.l1 x.1 x.2
    let x := row3 m inv a b.l2 x.1 x.2
    ssub 3 m x.1 x.2
  else
    let x := row4 m inv a b.l0 Z4 0
    let x := row4 m inv a b.l1 x.1 x.2
    let x := row4 m inv a b.l2 x.1 x.2
    let x := row4 m inv a b.l3 x.1 x.2
    ssub 4 m x.1 x.2

/-- `Small::double`: `2 x mod m` for `x < m`, over four limbs and the top bit. -/
def sdouble (m x : L4) : L4 :=
  let s0 := dblL x.l0
  let s1 := shl1 x.l1 x.l0
  let s2 := shl1 x.l2 x.l1
  let s3 := shl1 x.l3 x.l2
  let d0 := sbbLo s0 m.l0 0
  let b := sbbHi s0 m.l0 0
  let d1 := sbbLo s1 m.l1 b
  let b := sbbHi s1 m.l1 b
  let d2 := sbbLo s2 m.l2 b
  let b := sbbHi s2 m.l2 b
  let d3 := sbbLo s3 m.l3 b
  let b := sbbHi s3 m.l3 b
  if sbbHi (hib x.l3) 0 b = 1 then ⟨s0, s1, s2, s3⟩ else ⟨d0, d1, d2, d3⟩

end FeProofs.Modexp
