import Ethereum.RIPEMD160
import Mathlib.Tactic.Basic

/-!
# Ripemd160: the unrolled compression function

fevm's `ripemd_compress` writes out both lines' 80 steps with the working words renamed instead
of moved.  `compressFe` is that text over `UInt32`, and `compressFe_eq` shows it is EVMLean's
`RIPEMD160.compress`: the state of each line after step `j` is a window of the renamed words
(`stL`, `stR`), checked step by step with the tables evaluated.
-/

namespace FeProofs.Ripemd160

open Ethereum

/-- `f0` to `f4` of the Fe code. -/
def F0 (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
def F1 (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~x &&& z)
def F2 (x y z : UInt32) : UInt32 := (x ||| ~~~y) ^^^ z
def F3 (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~z)
def F4 (x y z : UInt32) : UInt32 := x ^^^ (y ||| ~~~z)

open RIPEMD160 (State rol) in
/-- `ripemd_compress` of the Fe code, over `UInt32`. -/
def compressFe (h : State) (X : Nat → UInt32) : State :=
  let w0 := X 0
  let w1 := X 1
  let w2 := X 2
  let w3 := X 3
  let w4 := X 4
  let w5 := X 5
  let w6 := X 6
  let w7 := X 7
  let w8 := X 8
  let w9 := X 9
  let w10 := X 10
  let w11 := X 11
  let w12 := X 12
  let w13 := X 13
  let w14 := X 14
  let w15 := X 15
  let la := h.h₀
  let lb := h.h₁
  let lc := h.h₂
  let ld := h.h₃
  let le := h.h₄
  let ra := la
  let rb := lb
  let rc := lc
  let rd := ld
  let re := le
  let l0 := rol (la + (F0 lb lc ld) + w0) 11 + le
  let lr0 := rol (lc) 10
  let l1 := rol (le + (F0 l0 lb lr0) + w1) 14 + ld
  let lr1 := rol (lb) 10
  let l2 := rol (ld + (F0 l1 l0 lr1) + w2) 15 + lr0
  let lr2 := rol (l0) 10
  let l3 := rol (lr0 + (F0 l2 l1 lr2) + w3) 12 + lr1
  let lr3 := rol (l1) 10
  let l4 := rol (lr1 + (F0 l3 l2 lr3) + w4) 5 + lr2
  let lr4 := rol (l2) 10
  let l5 := rol (lr2 + (F0 l4 l3 lr4) + w5) 8 + lr3
  let lr5 := rol (l3) 10
  let l6 := rol (lr3 + (F0 l5 l4 lr5) + w6) 7 + lr4
  let lr6 := rol (l4) 10
  let l7 := rol (lr4 + (F0 l6 l5 lr6) + w7) 9 + lr5
  let lr7 := rol (l5) 10
  let l8 := rol (lr5 + (F0 l7 l6 lr7) + w8) 11 + lr6
  let lr8 := rol (l6) 10
  let l9 := rol (lr6 + (F0 l8 l7 lr8) + w9) 13 + lr7
  let lr9 := rol (l7) 10
  let l10 := rol (lr7 + (F0 l9 l8 lr9) + w10) 14 + lr8
  let lr10 := rol (l8) 10
  let l11 := rol (lr8 + (F0 l10 l9 lr10) + w11) 15 + lr9
  let lr11 := rol (l9) 10
  let l12 := rol (lr9 + (F0 l11 l10 lr11) + w12) 6 + lr10
  let lr12 := rol (l10) 10
  let l13 := rol (lr10 + (F0 l12 l11 lr12) + w13) 7 + lr11
  let lr13 := rol (l11) 10
  let l14 := rol (lr11 + (F0 l13 l12 lr13) + w14) 9 + lr12
  let lr14 := rol (l12) 10
  let l15 := rol (lr12 + (F0 l14 l13 lr14) + w15) 8 + lr13
  let lr15 := rol (l13) 10
  let l16 := rol (lr13 + (F1 l15 l14 lr15) + w7 + UInt32.ofNat 1518500249) 7 + lr14
  let lr16 := rol (l14) 10
  let l17 := rol (lr14 + (F1 l16 l15 lr16) + w4 + UInt32.ofNat 1518500249) 6 + lr15
  let lr17 := rol (l15) 10
  let l18 := rol (lr15 + (F1 l17 l16 lr17) + w13 + UInt32.ofNat 1518500249) 8 + lr16
  let lr18 := rol (l16) 10
  let l19 := rol (lr16 + (F1 l18 l17 lr18) + w1 + UInt32.ofNat 1518500249) 13 + lr17
  let lr19 := rol (l17) 10
  let l20 := rol (lr17 + (F1 l19 l18 lr19) + w10 + UInt32.ofNat 1518500249) 11 + lr18
  let lr20 := rol (l18) 10
  let l21 := rol (lr18 + (F1 l20 l19 lr20) + w6 + UInt32.ofNat 1518500249) 9 + lr19
  let lr21 := rol (l19) 10
  let l22 := rol (lr19 + (F1 l21 l20 lr21) + w15 + UInt32.ofNat 1518500249) 7 + lr20
  let lr22 := rol (l20) 10
  let l23 := rol (lr20 + (F1 l22 l21 lr22) + w3 + UInt32.ofNat 1518500249) 15 + lr21
  let lr23 := rol (l21) 10
  let l24 := rol (lr21 + (F1 l23 l22 lr23) + w12 + UInt32.ofNat 1518500249) 7 + lr22
  let lr24 := rol (l22) 10
  let l25 := rol (lr22 + (F1 l24 l23 lr24) + w0 + UInt32.ofNat 1518500249) 12 + lr23
  let lr25 := rol (l23) 10
  let l26 := rol (lr23 + (F1 l25 l24 lr25) + w9 + UInt32.ofNat 1518500249) 15 + lr24
  let lr26 := rol (l24) 10
  let l27 := rol (lr24 + (F1 l26 l25 lr26) + w5 + UInt32.ofNat 1518500249) 9 + lr25
  let lr27 := rol (l25) 10
  let l28 := rol (lr25 + (F1 l27 l26 lr27) + w2 + UInt32.ofNat 1518500249) 11 + lr26
  let lr28 := rol (l26) 10
  let l29 := rol (lr26 + (F1 l28 l27 lr28) + w14 + UInt32.ofNat 1518500249) 7 + lr27
  let lr29 := rol (l27) 10
  let l30 := rol (lr27 + (F1 l29 l28 lr29) + w11 + UInt32.ofNat 1518500249) 13 + lr28
  let lr30 := rol (l28) 10
  let l31 := rol (lr28 + (F1 l30 l29 lr30) + w8 + UInt32.ofNat 1518500249) 12 + lr29
  let lr31 := rol (l29) 10
  let l32 := rol (lr29 + (F2 l31 l30 lr31) + w3 + UInt32.ofNat 1859775393) 11 + lr30
  let lr32 := rol (l30) 10
  let l33 := rol (lr30 + (F2 l32 l31 lr32) + w10 + UInt32.ofNat 1859775393) 13 + lr31
  let lr33 := rol (l31) 10
  let l34 := rol (lr31 + (F2 l33 l32 lr33) + w14 + UInt32.ofNat 1859775393) 6 + lr32
  let lr34 := rol (l32) 10
  let l35 := rol (lr32 + (F2 l34 l33 lr34) + w4 + UInt32.ofNat 1859775393) 7 + lr33
  let lr35 := rol (l33) 10
  let l36 := rol (lr33 + (F2 l35 l34 lr35) + w9 + UInt32.ofNat 1859775393) 14 + lr34
  let lr36 := rol (l34) 10
  let l37 := rol (lr34 + (F2 l36 l35 lr36) + w15 + UInt32.ofNat 1859775393) 9 + lr35
  let lr37 := rol (l35) 10
  let l38 := rol (lr35 + (F2 l37 l36 lr37) + w8 + UInt32.ofNat 1859775393) 13 + lr36
  let lr38 := rol (l36) 10
  let l39 := rol (lr36 + (F2 l38 l37 lr38) + w1 + UInt32.ofNat 1859775393) 15 + lr37
  let lr39 := rol (l37) 10
  let l40 := rol (lr37 + (F2 l39 l38 lr39) + w2 + UInt32.ofNat 1859775393) 14 + lr38
  let lr40 := rol (l38) 10
  let l41 := rol (lr38 + (F2 l40 l39 lr40) + w7 + UInt32.ofNat 1859775393) 8 + lr39
  let lr41 := rol (l39) 10
  let l42 := rol (lr39 + (F2 l41 l40 lr41) + w0 + UInt32.ofNat 1859775393) 13 + lr40
  let lr42 := rol (l40) 10
  let l43 := rol (lr40 + (F2 l42 l41 lr42) + w6 + UInt32.ofNat 1859775393) 6 + lr41
  let lr43 := rol (l41) 10
  let l44 := rol (lr41 + (F2 l43 l42 lr43) + w13 + UInt32.ofNat 1859775393) 5 + lr42
  let lr44 := rol (l42) 10
  let l45 := rol (lr42 + (F2 l44 l43 lr44) + w11 + UInt32.ofNat 1859775393) 12 + lr43
  let lr45 := rol (l43) 10
  let l46 := rol (lr43 + (F2 l45 l44 lr45) + w5 + UInt32.ofNat 1859775393) 7 + lr44
  let lr46 := rol (l44) 10
  let l47 := rol (lr44 + (F2 l46 l45 lr46) + w12 + UInt32.ofNat 1859775393) 5 + lr45
  let lr47 := rol (l45) 10
  let l48 := rol (lr45 + (F3 l47 l46 lr47) + w1 + UInt32.ofNat 2400959708) 11 + lr46
  let lr48 := rol (l46) 10
  let l49 := rol (lr46 + (F3 l48 l47 lr48) + w9 + UInt32.ofNat 2400959708) 12 + lr47
  let lr49 := rol (l47) 10
  let l50 := rol (lr47 + (F3 l49 l48 lr49) + w11 + UInt32.ofNat 2400959708) 14 + lr48
  let lr50 := rol (l48) 10
  let l51 := rol (lr48 + (F3 l50 l49 lr50) + w10 + UInt32.ofNat 2400959708) 15 + lr49
  let lr51 := rol (l49) 10
  let l52 := rol (lr49 + (F3 l51 l50 lr51) + w0 + UInt32.ofNat 2400959708) 14 + lr50
  let lr52 := rol (l50) 10
  let l53 := rol (lr50 + (F3 l52 l51 lr52) + w8 + UInt32.ofNat 2400959708) 15 + lr51
  let lr53 := rol (l51) 10
  let l54 := rol (lr51 + (F3 l53 l52 lr53) + w12 + UInt32.ofNat 2400959708) 9 + lr52
  let lr54 := rol (l52) 10
  let l55 := rol (lr52 + (F3 l54 l53 lr54) + w4 + UInt32.ofNat 2400959708) 8 + lr53
  let lr55 := rol (l53) 10
  let l56 := rol (lr53 + (F3 l55 l54 lr55) + w13 + UInt32.ofNat 2400959708) 9 + lr54
  let lr56 := rol (l54) 10
  let l57 := rol (lr54 + (F3 l56 l55 lr56) + w3 + UInt32.ofNat 2400959708) 14 + lr55
  let lr57 := rol (l55) 10
  let l58 := rol (lr55 + (F3 l57 l56 lr57) + w7 + UInt32.ofNat 2400959708) 5 + lr56
  let lr58 := rol (l56) 10
  let l59 := rol (lr56 + (F3 l58 l57 lr58) + w15 + UInt32.ofNat 2400959708) 6 + lr57
  let lr59 := rol (l57) 10
  let l60 := rol (lr57 + (F3 l59 l58 lr59) + w14 + UInt32.ofNat 2400959708) 8 + lr58
  let lr60 := rol (l58) 10
  let l61 := rol (lr58 + (F3 l60 l59 lr60) + w5 + UInt32.ofNat 2400959708) 6 + lr59
  let lr61 := rol (l59) 10
  let l62 := rol (lr59 + (F3 l61 l60 lr61) + w6 + UInt32.ofNat 2400959708) 5 + lr60
  let lr62 := rol (l60) 10
  let l63 := rol (lr60 + (F3 l62 l61 lr62) + w2 + UInt32.ofNat 2400959708) 12 + lr61
  let lr63 := rol (l61) 10
  let l64 := rol (lr61 + (F4 l63 l62 lr63) + w4 + UInt32.ofNat 2840853838) 9 + lr62
  let lr64 := rol (l62) 10
  let l65 := rol (lr62 + (F4 l64 l63 lr64) + w0 + UInt32.ofNat 2840853838) 15 + lr63
  let lr65 := rol (l63) 10
  let l66 := rol (lr63 + (F4 l65 l64 lr65) + w5 + UInt32.ofNat 2840853838) 5 + lr64
  let lr66 := rol (l64) 10
  let l67 := rol (lr64 + (F4 l66 l65 lr66) + w9 + UInt32.ofNat 2840853838) 11 + lr65
  let lr67 := rol (l65) 10
  let l68 := rol (lr65 + (F4 l67 l66 lr67) + w7 + UInt32.ofNat 2840853838) 6 + lr66
  let lr68 := rol (l66) 10
  let l69 := rol (lr66 + (F4 l68 l67 lr68) + w12 + UInt32.ofNat 2840853838) 8 + lr67
  let lr69 := rol (l67) 10
  let l70 := rol (lr67 + (F4 l69 l68 lr69) + w2 + UInt32.ofNat 2840853838) 13 + lr68
  let lr70 := rol (l68) 10
  let l71 := rol (lr68 + (F4 l70 l69 lr70) + w10 + UInt32.ofNat 2840853838) 12 + lr69
  let lr71 := rol (l69) 10
  let l72 := rol (lr69 + (F4 l71 l70 lr71) + w14 + UInt32.ofNat 2840853838) 5 + lr70
  let lr72 := rol (l70) 10
  let l73 := rol (lr70 + (F4 l72 l71 lr72) + w1 + UInt32.ofNat 2840853838) 12 + lr71
  let lr73 := rol (l71) 10
  let l74 := rol (lr71 + (F4 l73 l72 lr73) + w3 + UInt32.ofNat 2840853838) 13 + lr72
  let lr74 := rol (l72) 10
  let l75 := rol (lr72 + (F4 l74 l73 lr74) + w8 + UInt32.ofNat 2840853838) 14 + lr73
  let lr75 := rol (l73) 10
  let l76 := rol (lr73 + (F4 l75 l74 lr75) + w11 + UInt32.ofNat 2840853838) 11 + lr74
  let lr76 := rol (l74) 10
  let l77 := rol (lr74 + (F4 l76 l75 lr76) + w6 + UInt32.ofNat 2840853838) 8 + lr75
  let lr77 := rol (l75) 10
  let l78 := rol (lr75 + (F4 l77 l76 lr77) + w15 + UInt32.ofNat 2840853838) 5 + lr76
  let lr78 := rol (l76) 10
  let l79 := rol (lr76 + (F4 l78 l77 lr78) + w13 + UInt32.ofNat 2840853838) 6 + lr77
  let lr79 := rol (l77) 10
  let r0 := rol (ra + (F4 rb rc rd) + w5 + UInt32.ofNat 1352829926) 8 + re
  let rr0 := rol (rc) 10
  let r1 := rol (re + (F4 r0 rb rr0) + w14 + UInt32.ofNat 1352829926) 9 + rd
  let rr1 := rol (rb) 10
  let r2 := rol (rd + (F4 r1 r0 rr1) + w7 + UInt32.ofNat 1352829926) 9 + rr0
  let rr2 := rol (r0) 10
  let r3 := rol (rr0 + (F4 r2 r1 rr2) + w0 + UInt32.ofNat 1352829926) 11 + rr1
  let rr3 := rol (r1) 10
  let r4 := rol (rr1 + (F4 r3 r2 rr3) + w9 + UInt32.ofNat 1352829926) 13 + rr2
  let rr4 := rol (r2) 10
  let r5 := rol (rr2 + (F4 r4 r3 rr4) + w2 + UInt32.ofNat 1352829926) 15 + rr3
  let rr5 := rol (r3) 10
  let r6 := rol (rr3 + (F4 r5 r4 rr5) + w11 + UInt32.ofNat 1352829926) 15 + rr4
  let rr6 := rol (r4) 10
  let r7 := rol (rr4 + (F4 r6 r5 rr6) + w4 + UInt32.ofNat 1352829926) 5 + rr5
  let rr7 := rol (r5) 10
  let r8 := rol (rr5 + (F4 r7 r6 rr7) + w13 + UInt32.ofNat 1352829926) 7 + rr6
  let rr8 := rol (r6) 10
  let r9 := rol (rr6 + (F4 r8 r7 rr8) + w6 + UInt32.ofNat 1352829926) 7 + rr7
  let rr9 := rol (r7) 10
  let r10 := rol (rr7 + (F4 r9 r8 rr9) + w15 + UInt32.ofNat 1352829926) 8 + rr8
  let rr10 := rol (r8) 10
  let r11 := rol (rr8 + (F4 r10 r9 rr10) + w8 + UInt32.ofNat 1352829926) 11 + rr9
  let rr11 := rol (r9) 10
  let r12 := rol (rr9 + (F4 r11 r10 rr11) + w1 + UInt32.ofNat 1352829926) 14 + rr10
  let rr12 := rol (r10) 10
  let r13 := rol (rr10 + (F4 r12 r11 rr12) + w10 + UInt32.ofNat 1352829926) 14 + rr11
  let rr13 := rol (r11) 10
  let r14 := rol (rr11 + (F4 r13 r12 rr13) + w3 + UInt32.ofNat 1352829926) 12 + rr12
  let rr14 := rol (r12) 10
  let r15 := rol (rr12 + (F4 r14 r13 rr14) + w12 + UInt32.ofNat 1352829926) 6 + rr13
  let rr15 := rol (r13) 10
  let r16 := rol (rr13 + (F3 r15 r14 rr15) + w6 + UInt32.ofNat 1548603684) 9 + rr14
  let rr16 := rol (r14) 10
  let r17 := rol (rr14 + (F3 r16 r15 rr16) + w11 + UInt32.ofNat 1548603684) 13 + rr15
  let rr17 := rol (r15) 10
  let r18 := rol (rr15 + (F3 r17 r16 rr17) + w3 + UInt32.ofNat 1548603684) 15 + rr16
  let rr18 := rol (r16) 10
  let r19 := rol (rr16 + (F3 r18 r17 rr18) + w7 + UInt32.ofNat 1548603684) 7 + rr17
  let rr19 := rol (r17) 10
  let r20 := rol (rr17 + (F3 r19 r18 rr19) + w0 + UInt32.ofNat 1548603684) 12 + rr18
  let rr20 := rol (r18) 10
  let r21 := rol (rr18 + (F3 r20 r19 rr20) + w13 + UInt32.ofNat 1548603684) 8 + rr19
  let rr21 := rol (r19) 10
  let r22 := rol (rr19 + (F3 r21 r20 rr21) + w5 + UInt32.ofNat 1548603684) 9 + rr20
  let rr22 := rol (r20) 10
  let r23 := rol (rr20 + (F3 r22 r21 rr22) + w10 + UInt32.ofNat 1548603684) 11 + rr21
  let rr23 := rol (r21) 10
  let r24 := rol (rr21 + (F3 r23 r22 rr23) + w14 + UInt32.ofNat 1548603684) 7 + rr22
  let rr24 := rol (r22) 10
  let r25 := rol (rr22 + (F3 r24 r23 rr24) + w15 + UInt32.ofNat 1548603684) 7 + rr23
  let rr25 := rol (r23) 10
  let r26 := rol (rr23 + (F3 r25 r24 rr25) + w8 + UInt32.ofNat 1548603684) 12 + rr24
  let rr26 := rol (r24) 10
  let r27 := rol (rr24 + (F3 r26 r25 rr26) + w12 + UInt32.ofNat 1548603684) 7 + rr25
  let rr27 := rol (r25) 10
  let r28 := rol (rr25 + (F3 r27 r26 rr27) + w4 + UInt32.ofNat 1548603684) 6 + rr26
  let rr28 := rol (r26) 10
  let r29 := rol (rr26 + (F3 r28 r27 rr28) + w9 + UInt32.ofNat 1548603684) 15 + rr27
  let rr29 := rol (r27) 10
  let r30 := rol (rr27 + (F3 r29 r28 rr29) + w1 + UInt32.ofNat 1548603684) 13 + rr28
  let rr30 := rol (r28) 10
  let r31 := rol (rr28 + (F3 r30 r29 rr30) + w2 + UInt32.ofNat 1548603684) 11 + rr29
  let rr31 := rol (r29) 10
  let r32 := rol (rr29 + (F2 r31 r30 rr31) + w15 + UInt32.ofNat 1836072691) 9 + rr30
  let rr32 := rol (r30) 10
  let r33 := rol (rr30 + (F2 r32 r31 rr32) + w5 + UInt32.ofNat 1836072691) 7 + rr31
  let rr33 := rol (r31) 10
  let r34 := rol (rr31 + (F2 r33 r32 rr33) + w1 + UInt32.ofNat 1836072691) 15 + rr32
  let rr34 := rol (r32) 10
  let r35 := rol (rr32 + (F2 r34 r33 rr34) + w3 + UInt32.ofNat 1836072691) 11 + rr33
  let rr35 := rol (r33) 10
  let r36 := rol (rr33 + (F2 r35 r34 rr35) + w7 + UInt32.ofNat 1836072691) 8 + rr34
  let rr36 := rol (r34) 10
  let r37 := rol (rr34 + (F2 r36 r35 rr36) + w14 + UInt32.ofNat 1836072691) 6 + rr35
  let rr37 := rol (r35) 10
  let r38 := rol (rr35 + (F2 r37 r36 rr37) + w6 + UInt32.ofNat 1836072691) 6 + rr36
  let rr38 := rol (r36) 10
  let r39 := rol (rr36 + (F2 r38 r37 rr38) + w9 + UInt32.ofNat 1836072691) 14 + rr37
  let rr39 := rol (r37) 10
  let r40 := rol (rr37 + (F2 r39 r38 rr39) + w11 + UInt32.ofNat 1836072691) 12 + rr38
  let rr40 := rol (r38) 10
  let r41 := rol (rr38 + (F2 r40 r39 rr40) + w8 + UInt32.ofNat 1836072691) 13 + rr39
  let rr41 := rol (r39) 10
  let r42 := rol (rr39 + (F2 r41 r40 rr41) + w12 + UInt32.ofNat 1836072691) 5 + rr40
  let rr42 := rol (r40) 10
  let r43 := rol (rr40 + (F2 r42 r41 rr42) + w2 + UInt32.ofNat 1836072691) 14 + rr41
  let rr43 := rol (r41) 10
  let r44 := rol (rr41 + (F2 r43 r42 rr43) + w10 + UInt32.ofNat 1836072691) 13 + rr42
  let rr44 := rol (r42) 10
  let r45 := rol (rr42 + (F2 r44 r43 rr44) + w0 + UInt32.ofNat 1836072691) 13 + rr43
  let rr45 := rol (r43) 10
  let r46 := rol (rr43 + (F2 r45 r44 rr45) + w4 + UInt32.ofNat 1836072691) 7 + rr44
  let rr46 := rol (r44) 10
  let r47 := rol (rr44 + (F2 r46 r45 rr46) + w13 + UInt32.ofNat 1836072691) 5 + rr45
  let rr47 := rol (r45) 10
  let r48 := rol (rr45 + (F1 r47 r46 rr47) + w8 + UInt32.ofNat 2053994217) 15 + rr46
  let rr48 := rol (r46) 10
  let r49 := rol (rr46 + (F1 r48 r47 rr48) + w6 + UInt32.ofNat 2053994217) 5 + rr47
  let rr49 := rol (r47) 10
  let r50 := rol (rr47 + (F1 r49 r48 rr49) + w4 + UInt32.ofNat 2053994217) 8 + rr48
  let rr50 := rol (r48) 10
  let r51 := rol (rr48 + (F1 r50 r49 rr50) + w1 + UInt32.ofNat 2053994217) 11 + rr49
  let rr51 := rol (r49) 10
  let r52 := rol (rr49 + (F1 r51 r50 rr51) + w3 + UInt32.ofNat 2053994217) 14 + rr50
  let rr52 := rol (r50) 10
  let r53 := rol (rr50 + (F1 r52 r51 rr52) + w11 + UInt32.ofNat 2053994217) 14 + rr51
  let rr53 := rol (r51) 10
  let r54 := rol (rr51 + (F1 r53 r52 rr53) + w15 + UInt32.ofNat 2053994217) 6 + rr52
  let rr54 := rol (r52) 10
  let r55 := rol (rr52 + (F1 r54 r53 rr54) + w0 + UInt32.ofNat 2053994217) 14 + rr53
  let rr55 := rol (r53) 10
  let r56 := rol (rr53 + (F1 r55 r54 rr55) + w5 + UInt32.ofNat 2053994217) 6 + rr54
  let rr56 := rol (r54) 10
  let r57 := rol (rr54 + (F1 r56 r55 rr56) + w12 + UInt32.ofNat 2053994217) 9 + rr55
  let rr57 := rol (r55) 10
  let r58 := rol (rr55 + (F1 r57 r56 rr57) + w2 + UInt32.ofNat 2053994217) 12 + rr56
  let rr58 := rol (r56) 10
  let r59 := rol (rr56 + (F1 r58 r57 rr58) + w13 + UInt32.ofNat 2053994217) 9 + rr57
  let rr59 := rol (r57) 10
  let r60 := rol (rr57 + (F1 r59 r58 rr59) + w9 + UInt32.ofNat 2053994217) 12 + rr58
  let rr60 := rol (r58) 10
  let r61 := rol (rr58 + (F1 r60 r59 rr60) + w7 + UInt32.ofNat 2053994217) 5 + rr59
  let rr61 := rol (r59) 10
  let r62 := rol (rr59 + (F1 r61 r60 rr61) + w10 + UInt32.ofNat 2053994217) 15 + rr60
  let rr62 := rol (r60) 10
  let r63 := rol (rr60 + (F1 r62 r61 rr62) + w14 + UInt32.ofNat 2053994217) 8 + rr61
  let rr63 := rol (r61) 10
  let r64 := rol (rr61 + (F0 r63 r62 rr63) + w12) 8 + rr62
  let rr64 := rol (r62) 10
  let r65 := rol (rr62 + (F0 r64 r63 rr64) + w15) 5 + rr63
  let rr65 := rol (r63) 10
  let r66 := rol (rr63 + (F0 r65 r64 rr65) + w10) 12 + rr64
  let rr66 := rol (r64) 10
  let r67 := rol (rr64 + (F0 r66 r65 rr66) + w4) 9 + rr65
  let rr67 := rol (r65) 10
  let r68 := rol (rr65 + (F0 r67 r66 rr67) + w1) 12 + rr66
  let rr68 := rol (r66) 10
  let r69 := rol (rr66 + (F0 r68 r67 rr68) + w5) 5 + rr67
  let rr69 := rol (r67) 10
  let r70 := rol (rr67 + (F0 r69 r68 rr69) + w8) 14 + rr68
  let rr70 := rol (r68) 10
  let r71 := rol (rr68 + (F0 r70 r69 rr70) + w7) 6 + rr69
  let rr71 := rol (r69) 10
  let r72 := rol (rr69 + (F0 r71 r70 rr71) + w6) 8 + rr70
  let rr72 := rol (r70) 10
  let r73 := rol (rr70 + (F0 r72 r71 rr72) + w2) 13 + rr71
  let rr73 := rol (r71) 10
  let r74 := rol (rr71 + (F0 r73 r72 rr73) + w13) 6 + rr72
  let rr74 := rol (r72) 10
  let r75 := rol (rr72 + (F0 r74 r73 rr74) + w14) 5 + rr73
  let rr75 := rol (r73) 10
  let r76 := rol (rr73 + (F0 r75 r74 rr75) + w0) 15 + rr74
  let rr76 := rol (r74) 10
  let r77 := rol (rr74 + (F0 r76 r75 rr76) + w3) 13 + rr75
  let rr77 := rol (r75) 10
  let r78 := rol (rr75 + (F0 r77 r76 rr77) + w9) 11 + rr76
  let rr78 := rol (r76) 10
  let r79 := rol (rr76 + (F0 r78 r77 rr78) + w11) 11 + rr77
  let rr79 := rol (r77) 10
  ⟨h.h₁ + l78 + rr79, h.h₂ + lr79 + rr78, h.h₃ + lr78 + rr77, h.h₄ + lr77 + r79, h.h₀ + l79 + r78⟩

/-- Step `j` of the left line. -/
def stL (X : Array UInt32) (j : Nat) (a : RIPEMD160.State) : RIPEMD160.State :=
  RIPEMD160.step a (RIPEMD160.f j a.h₁ a.h₂ a.h₃) X[RIPEMD160.r[j]!]! RIPEMD160.K[j / 16]!
    RIPEMD160.s[j]!

/-- Step `j` of the right line. -/
def stR (X : Array UInt32) (j : Nat) (b : RIPEMD160.State) : RIPEMD160.State :=
  RIPEMD160.step b (RIPEMD160.f (79 - j) b.h₁ b.h₂ b.h₃) X[RIPEMD160.r'[j]!]! RIPEMD160.K'[j / 16]!
    RIPEMD160.s'[j]!

theorem fold_pair {α : Type} (F G : Nat → α → α) :
    ∀ (l : List Nat) (a b : α), l.foldl (fun p j => (F j p.1, G j p.2)) (a, b) =
      (l.foldl (fun a j => F j a) a, l.foldl (fun b j => G j b) b)
  | [], _, _ => rfl
  | j :: l, a, b => fold_pair F G l (F j a) (G j b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **`compressFe` is RIPEMD-160's compression function.** -/
theorem compressFe_eq (h : RIPEMD160.State) (X : Array UInt32) :
    compressFe h (fun k => X[k]!) = RIPEMD160.compress h X := by
  unfold compressFe
  extract_lets w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 la lb lc ld le ra rb rc rd re l0 lr0 l1 lr1 l2 lr2 l3 lr3 l4 lr4 l5 lr5 l6 lr6 l7 lr7 l8 lr8 l9 lr9 l10 lr10 l11 lr11 l12 lr12 l13 lr13 l14 lr14 l15 lr15 l16 lr16 l17 lr17 l18 lr18 l19 lr19 l20 lr20 l21 lr21 l22 lr22 l23 lr23 l24 lr24 l25 lr25 l26 lr26 l27 lr27 l28 lr28 l29 lr29 l30 lr30 l31 lr31 l32 lr32 l33 lr33 l34 lr34 l35 lr35 l36 lr36 l37 lr37 l38 lr38 l39 lr39 l40 lr40 l41 lr41 l42 lr42 l43 lr43 l44 lr44 l45 lr45 l46 lr46 l47 lr47 l48 lr48 l49 lr49 l50 lr50 l51 lr51 l52 lr52 l53 lr53 l54 lr54 l55 lr55 l56 lr56 l57 lr57 l58 lr58 l59 lr59 l60 lr60 l61 lr61 l62 lr62 l63 lr63 l64 lr64 l65 lr65 l66 lr66 l67 lr67 l68 lr68 l69 lr69 l70 lr70 l71 lr71 l72 lr72 l73 lr73 l74 lr74 l75 lr75 l76 lr76 l77 lr77 l78 lr78 l79 lr79 r0 rr0 r1 rr1 r2 rr2 r3 rr3 r4 rr4 r5 rr5 r6 rr6 r7 rr7 r8 rr8 r9 rr9 r10 rr10 r11 rr11 r12 rr12 r13 rr13 r14 rr14 r15 rr15 r16 rr16 r17 rr17 r18 rr18 r19 rr19 r20 rr20 r21 rr21 r22 rr22 r23 rr23 r24 rr24 r25 rr25 r26 rr26 r27 rr27 r28 rr28 r29 rr29 r30 rr30 r31 rr31 r32 rr32 r33 rr33 r34 rr34 r35 rr35 r36 rr36 r37 rr37 r38 rr38 r39 rr39 r40 rr40 r41 rr41 r42 rr42 r43 rr43 r44 rr44 r45 rr45 r46 rr46 r47 rr47 r48 rr48 r49 rr49 r50 rr50 r51 rr51 r52 rr52 r53 rr53 r54 rr54 r55 rr55 r56 rr56 r57 rr57 r58 rr58 r59 rr59 r60 rr60 r61 rr61 r62 rr62 r63 rr63 r64 rr64 r65 rr65 r66 rr66 r67 rr67 r68 rr68 r69 rr69 r70 rr70 r71 rr71 r72 rr72 r73 rr73 r74 rr74 r75 rr75 r76 rr76 r77 rr77 r78 rr78 r79 rr79
  have eL0 : stL X 0 h = ⟨le, l0, lb, lr0, ld⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL1 : stL X 1 ⟨le, l0, lb, lr0, ld⟩ = ⟨ld, l1, l0, lr1, lr0⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL2 : stL X 2 ⟨ld, l1, l0, lr1, lr0⟩ = ⟨lr0, l2, l1, lr2, lr1⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL3 : stL X 3 ⟨lr0, l2, l1, lr2, lr1⟩ = ⟨lr1, l3, l2, lr3, lr2⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL4 : stL X 4 ⟨lr1, l3, l2, lr3, lr2⟩ = ⟨lr2, l4, l3, lr4, lr3⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL5 : stL X 5 ⟨lr2, l4, l3, lr4, lr3⟩ = ⟨lr3, l5, l4, lr5, lr4⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL6 : stL X 6 ⟨lr3, l5, l4, lr5, lr4⟩ = ⟨lr4, l6, l5, lr6, lr5⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL7 : stL X 7 ⟨lr4, l6, l5, lr6, lr5⟩ = ⟨lr5, l7, l6, lr7, lr6⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL8 : stL X 8 ⟨lr5, l7, l6, lr7, lr6⟩ = ⟨lr6, l8, l7, lr8, lr7⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL9 : stL X 9 ⟨lr6, l8, l7, lr8, lr7⟩ = ⟨lr7, l9, l8, lr9, lr8⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL10 : stL X 10 ⟨lr7, l9, l8, lr9, lr8⟩ = ⟨lr8, l10, l9, lr10, lr9⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL11 : stL X 11 ⟨lr8, l10, l9, lr10, lr9⟩ = ⟨lr9, l11, l10, lr11, lr10⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL12 : stL X 12 ⟨lr9, l11, l10, lr11, lr10⟩ = ⟨lr10, l12, l11, lr12, lr11⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL13 : stL X 13 ⟨lr10, l12, l11, lr12, lr11⟩ = ⟨lr11, l13, l12, lr13, lr12⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL14 : stL X 14 ⟨lr11, l13, l12, lr13, lr12⟩ = ⟨lr12, l14, l13, lr14, lr13⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL15 : stL X 15 ⟨lr12, l14, l13, lr14, lr13⟩ = ⟨lr13, l15, l14, lr15, lr14⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL16 : stL X 16 ⟨lr13, l15, l14, lr15, lr14⟩ = ⟨lr14, l16, l15, lr16, lr15⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL17 : stL X 17 ⟨lr14, l16, l15, lr16, lr15⟩ = ⟨lr15, l17, l16, lr17, lr16⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL18 : stL X 18 ⟨lr15, l17, l16, lr17, lr16⟩ = ⟨lr16, l18, l17, lr18, lr17⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL19 : stL X 19 ⟨lr16, l18, l17, lr18, lr17⟩ = ⟨lr17, l19, l18, lr19, lr18⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL20 : stL X 20 ⟨lr17, l19, l18, lr19, lr18⟩ = ⟨lr18, l20, l19, lr20, lr19⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL21 : stL X 21 ⟨lr18, l20, l19, lr20, lr19⟩ = ⟨lr19, l21, l20, lr21, lr20⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL22 : stL X 22 ⟨lr19, l21, l20, lr21, lr20⟩ = ⟨lr20, l22, l21, lr22, lr21⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL23 : stL X 23 ⟨lr20, l22, l21, lr22, lr21⟩ = ⟨lr21, l23, l22, lr23, lr22⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL24 : stL X 24 ⟨lr21, l23, l22, lr23, lr22⟩ = ⟨lr22, l24, l23, lr24, lr23⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL25 : stL X 25 ⟨lr22, l24, l23, lr24, lr23⟩ = ⟨lr23, l25, l24, lr25, lr24⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL26 : stL X 26 ⟨lr23, l25, l24, lr25, lr24⟩ = ⟨lr24, l26, l25, lr26, lr25⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL27 : stL X 27 ⟨lr24, l26, l25, lr26, lr25⟩ = ⟨lr25, l27, l26, lr27, lr26⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL28 : stL X 28 ⟨lr25, l27, l26, lr27, lr26⟩ = ⟨lr26, l28, l27, lr28, lr27⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL29 : stL X 29 ⟨lr26, l28, l27, lr28, lr27⟩ = ⟨lr27, l29, l28, lr29, lr28⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL30 : stL X 30 ⟨lr27, l29, l28, lr29, lr28⟩ = ⟨lr28, l30, l29, lr30, lr29⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL31 : stL X 31 ⟨lr28, l30, l29, lr30, lr29⟩ = ⟨lr29, l31, l30, lr31, lr30⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL32 : stL X 32 ⟨lr29, l31, l30, lr31, lr30⟩ = ⟨lr30, l32, l31, lr32, lr31⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL33 : stL X 33 ⟨lr30, l32, l31, lr32, lr31⟩ = ⟨lr31, l33, l32, lr33, lr32⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL34 : stL X 34 ⟨lr31, l33, l32, lr33, lr32⟩ = ⟨lr32, l34, l33, lr34, lr33⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL35 : stL X 35 ⟨lr32, l34, l33, lr34, lr33⟩ = ⟨lr33, l35, l34, lr35, lr34⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL36 : stL X 36 ⟨lr33, l35, l34, lr35, lr34⟩ = ⟨lr34, l36, l35, lr36, lr35⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL37 : stL X 37 ⟨lr34, l36, l35, lr36, lr35⟩ = ⟨lr35, l37, l36, lr37, lr36⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL38 : stL X 38 ⟨lr35, l37, l36, lr37, lr36⟩ = ⟨lr36, l38, l37, lr38, lr37⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL39 : stL X 39 ⟨lr36, l38, l37, lr38, lr37⟩ = ⟨lr37, l39, l38, lr39, lr38⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL40 : stL X 40 ⟨lr37, l39, l38, lr39, lr38⟩ = ⟨lr38, l40, l39, lr40, lr39⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL41 : stL X 41 ⟨lr38, l40, l39, lr40, lr39⟩ = ⟨lr39, l41, l40, lr41, lr40⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL42 : stL X 42 ⟨lr39, l41, l40, lr41, lr40⟩ = ⟨lr40, l42, l41, lr42, lr41⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL43 : stL X 43 ⟨lr40, l42, l41, lr42, lr41⟩ = ⟨lr41, l43, l42, lr43, lr42⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL44 : stL X 44 ⟨lr41, l43, l42, lr43, lr42⟩ = ⟨lr42, l44, l43, lr44, lr43⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL45 : stL X 45 ⟨lr42, l44, l43, lr44, lr43⟩ = ⟨lr43, l45, l44, lr45, lr44⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL46 : stL X 46 ⟨lr43, l45, l44, lr45, lr44⟩ = ⟨lr44, l46, l45, lr46, lr45⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL47 : stL X 47 ⟨lr44, l46, l45, lr46, lr45⟩ = ⟨lr45, l47, l46, lr47, lr46⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL48 : stL X 48 ⟨lr45, l47, l46, lr47, lr46⟩ = ⟨lr46, l48, l47, lr48, lr47⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL49 : stL X 49 ⟨lr46, l48, l47, lr48, lr47⟩ = ⟨lr47, l49, l48, lr49, lr48⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL50 : stL X 50 ⟨lr47, l49, l48, lr49, lr48⟩ = ⟨lr48, l50, l49, lr50, lr49⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL51 : stL X 51 ⟨lr48, l50, l49, lr50, lr49⟩ = ⟨lr49, l51, l50, lr51, lr50⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL52 : stL X 52 ⟨lr49, l51, l50, lr51, lr50⟩ = ⟨lr50, l52, l51, lr52, lr51⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL53 : stL X 53 ⟨lr50, l52, l51, lr52, lr51⟩ = ⟨lr51, l53, l52, lr53, lr52⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL54 : stL X 54 ⟨lr51, l53, l52, lr53, lr52⟩ = ⟨lr52, l54, l53, lr54, lr53⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL55 : stL X 55 ⟨lr52, l54, l53, lr54, lr53⟩ = ⟨lr53, l55, l54, lr55, lr54⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL56 : stL X 56 ⟨lr53, l55, l54, lr55, lr54⟩ = ⟨lr54, l56, l55, lr56, lr55⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL57 : stL X 57 ⟨lr54, l56, l55, lr56, lr55⟩ = ⟨lr55, l57, l56, lr57, lr56⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL58 : stL X 58 ⟨lr55, l57, l56, lr57, lr56⟩ = ⟨lr56, l58, l57, lr58, lr57⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL59 : stL X 59 ⟨lr56, l58, l57, lr58, lr57⟩ = ⟨lr57, l59, l58, lr59, lr58⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL60 : stL X 60 ⟨lr57, l59, l58, lr59, lr58⟩ = ⟨lr58, l60, l59, lr60, lr59⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL61 : stL X 61 ⟨lr58, l60, l59, lr60, lr59⟩ = ⟨lr59, l61, l60, lr61, lr60⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL62 : stL X 62 ⟨lr59, l61, l60, lr61, lr60⟩ = ⟨lr60, l62, l61, lr62, lr61⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL63 : stL X 63 ⟨lr60, l62, l61, lr62, lr61⟩ = ⟨lr61, l63, l62, lr63, lr62⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL64 : stL X 64 ⟨lr61, l63, l62, lr63, lr62⟩ = ⟨lr62, l64, l63, lr64, lr63⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL65 : stL X 65 ⟨lr62, l64, l63, lr64, lr63⟩ = ⟨lr63, l65, l64, lr65, lr64⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL66 : stL X 66 ⟨lr63, l65, l64, lr65, lr64⟩ = ⟨lr64, l66, l65, lr66, lr65⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL67 : stL X 67 ⟨lr64, l66, l65, lr66, lr65⟩ = ⟨lr65, l67, l66, lr67, lr66⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL68 : stL X 68 ⟨lr65, l67, l66, lr67, lr66⟩ = ⟨lr66, l68, l67, lr68, lr67⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL69 : stL X 69 ⟨lr66, l68, l67, lr68, lr67⟩ = ⟨lr67, l69, l68, lr69, lr68⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL70 : stL X 70 ⟨lr67, l69, l68, lr69, lr68⟩ = ⟨lr68, l70, l69, lr70, lr69⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL71 : stL X 71 ⟨lr68, l70, l69, lr70, lr69⟩ = ⟨lr69, l71, l70, lr71, lr70⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL72 : stL X 72 ⟨lr69, l71, l70, lr71, lr70⟩ = ⟨lr70, l72, l71, lr72, lr71⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL73 : stL X 73 ⟨lr70, l72, l71, lr72, lr71⟩ = ⟨lr71, l73, l72, lr73, lr72⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL74 : stL X 74 ⟨lr71, l73, l72, lr73, lr72⟩ = ⟨lr72, l74, l73, lr74, lr73⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL75 : stL X 75 ⟨lr72, l74, l73, lr74, lr73⟩ = ⟨lr73, l75, l74, lr75, lr74⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL76 : stL X 76 ⟨lr73, l75, l74, lr75, lr74⟩ = ⟨lr74, l76, l75, lr76, lr75⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL77 : stL X 77 ⟨lr74, l76, l75, lr76, lr75⟩ = ⟨lr75, l77, l76, lr77, lr76⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL78 : stL X 78 ⟨lr75, l77, l76, lr77, lr76⟩ = ⟨lr76, l78, l77, lr78, lr77⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eL79 : stL X 79 ⟨lr76, l78, l77, lr78, lr77⟩ = ⟨lr77, l79, l78, lr79, lr78⟩ := by
    simp only [stL, RIPEMD160.step, RIPEMD160.r, RIPEMD160.s, RIPEMD160.K, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR0 : stR X 0 h = ⟨re, r0, rb, rr0, rd⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR1 : stR X 1 ⟨re, r0, rb, rr0, rd⟩ = ⟨rd, r1, r0, rr1, rr0⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR2 : stR X 2 ⟨rd, r1, r0, rr1, rr0⟩ = ⟨rr0, r2, r1, rr2, rr1⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR3 : stR X 3 ⟨rr0, r2, r1, rr2, rr1⟩ = ⟨rr1, r3, r2, rr3, rr2⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR4 : stR X 4 ⟨rr1, r3, r2, rr3, rr2⟩ = ⟨rr2, r4, r3, rr4, rr3⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR5 : stR X 5 ⟨rr2, r4, r3, rr4, rr3⟩ = ⟨rr3, r5, r4, rr5, rr4⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR6 : stR X 6 ⟨rr3, r5, r4, rr5, rr4⟩ = ⟨rr4, r6, r5, rr6, rr5⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR7 : stR X 7 ⟨rr4, r6, r5, rr6, rr5⟩ = ⟨rr5, r7, r6, rr7, rr6⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR8 : stR X 8 ⟨rr5, r7, r6, rr7, rr6⟩ = ⟨rr6, r8, r7, rr8, rr7⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR9 : stR X 9 ⟨rr6, r8, r7, rr8, rr7⟩ = ⟨rr7, r9, r8, rr9, rr8⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR10 : stR X 10 ⟨rr7, r9, r8, rr9, rr8⟩ = ⟨rr8, r10, r9, rr10, rr9⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR11 : stR X 11 ⟨rr8, r10, r9, rr10, rr9⟩ = ⟨rr9, r11, r10, rr11, rr10⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR12 : stR X 12 ⟨rr9, r11, r10, rr11, rr10⟩ = ⟨rr10, r12, r11, rr12, rr11⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR13 : stR X 13 ⟨rr10, r12, r11, rr12, rr11⟩ = ⟨rr11, r13, r12, rr13, rr12⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR14 : stR X 14 ⟨rr11, r13, r12, rr13, rr12⟩ = ⟨rr12, r14, r13, rr14, rr13⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR15 : stR X 15 ⟨rr12, r14, r13, rr14, rr13⟩ = ⟨rr13, r15, r14, rr15, rr14⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR16 : stR X 16 ⟨rr13, r15, r14, rr15, rr14⟩ = ⟨rr14, r16, r15, rr16, rr15⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR17 : stR X 17 ⟨rr14, r16, r15, rr16, rr15⟩ = ⟨rr15, r17, r16, rr17, rr16⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR18 : stR X 18 ⟨rr15, r17, r16, rr17, rr16⟩ = ⟨rr16, r18, r17, rr18, rr17⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR19 : stR X 19 ⟨rr16, r18, r17, rr18, rr17⟩ = ⟨rr17, r19, r18, rr19, rr18⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR20 : stR X 20 ⟨rr17, r19, r18, rr19, rr18⟩ = ⟨rr18, r20, r19, rr20, rr19⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR21 : stR X 21 ⟨rr18, r20, r19, rr20, rr19⟩ = ⟨rr19, r21, r20, rr21, rr20⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR22 : stR X 22 ⟨rr19, r21, r20, rr21, rr20⟩ = ⟨rr20, r22, r21, rr22, rr21⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR23 : stR X 23 ⟨rr20, r22, r21, rr22, rr21⟩ = ⟨rr21, r23, r22, rr23, rr22⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR24 : stR X 24 ⟨rr21, r23, r22, rr23, rr22⟩ = ⟨rr22, r24, r23, rr24, rr23⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR25 : stR X 25 ⟨rr22, r24, r23, rr24, rr23⟩ = ⟨rr23, r25, r24, rr25, rr24⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR26 : stR X 26 ⟨rr23, r25, r24, rr25, rr24⟩ = ⟨rr24, r26, r25, rr26, rr25⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR27 : stR X 27 ⟨rr24, r26, r25, rr26, rr25⟩ = ⟨rr25, r27, r26, rr27, rr26⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR28 : stR X 28 ⟨rr25, r27, r26, rr27, rr26⟩ = ⟨rr26, r28, r27, rr28, rr27⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR29 : stR X 29 ⟨rr26, r28, r27, rr28, rr27⟩ = ⟨rr27, r29, r28, rr29, rr28⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR30 : stR X 30 ⟨rr27, r29, r28, rr29, rr28⟩ = ⟨rr28, r30, r29, rr30, rr29⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR31 : stR X 31 ⟨rr28, r30, r29, rr30, rr29⟩ = ⟨rr29, r31, r30, rr31, rr30⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR32 : stR X 32 ⟨rr29, r31, r30, rr31, rr30⟩ = ⟨rr30, r32, r31, rr32, rr31⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR33 : stR X 33 ⟨rr30, r32, r31, rr32, rr31⟩ = ⟨rr31, r33, r32, rr33, rr32⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR34 : stR X 34 ⟨rr31, r33, r32, rr33, rr32⟩ = ⟨rr32, r34, r33, rr34, rr33⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR35 : stR X 35 ⟨rr32, r34, r33, rr34, rr33⟩ = ⟨rr33, r35, r34, rr35, rr34⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR36 : stR X 36 ⟨rr33, r35, r34, rr35, rr34⟩ = ⟨rr34, r36, r35, rr36, rr35⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR37 : stR X 37 ⟨rr34, r36, r35, rr36, rr35⟩ = ⟨rr35, r37, r36, rr37, rr36⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR38 : stR X 38 ⟨rr35, r37, r36, rr37, rr36⟩ = ⟨rr36, r38, r37, rr38, rr37⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR39 : stR X 39 ⟨rr36, r38, r37, rr38, rr37⟩ = ⟨rr37, r39, r38, rr39, rr38⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR40 : stR X 40 ⟨rr37, r39, r38, rr39, rr38⟩ = ⟨rr38, r40, r39, rr40, rr39⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR41 : stR X 41 ⟨rr38, r40, r39, rr40, rr39⟩ = ⟨rr39, r41, r40, rr41, rr40⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR42 : stR X 42 ⟨rr39, r41, r40, rr41, rr40⟩ = ⟨rr40, r42, r41, rr42, rr41⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR43 : stR X 43 ⟨rr40, r42, r41, rr42, rr41⟩ = ⟨rr41, r43, r42, rr43, rr42⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR44 : stR X 44 ⟨rr41, r43, r42, rr43, rr42⟩ = ⟨rr42, r44, r43, rr44, rr43⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR45 : stR X 45 ⟨rr42, r44, r43, rr44, rr43⟩ = ⟨rr43, r45, r44, rr45, rr44⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR46 : stR X 46 ⟨rr43, r45, r44, rr45, rr44⟩ = ⟨rr44, r46, r45, rr46, rr45⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR47 : stR X 47 ⟨rr44, r46, r45, rr46, rr45⟩ = ⟨rr45, r47, r46, rr47, rr46⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR48 : stR X 48 ⟨rr45, r47, r46, rr47, rr46⟩ = ⟨rr46, r48, r47, rr48, rr47⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR49 : stR X 49 ⟨rr46, r48, r47, rr48, rr47⟩ = ⟨rr47, r49, r48, rr49, rr48⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR50 : stR X 50 ⟨rr47, r49, r48, rr49, rr48⟩ = ⟨rr48, r50, r49, rr50, rr49⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR51 : stR X 51 ⟨rr48, r50, r49, rr50, rr49⟩ = ⟨rr49, r51, r50, rr51, rr50⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR52 : stR X 52 ⟨rr49, r51, r50, rr51, rr50⟩ = ⟨rr50, r52, r51, rr52, rr51⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR53 : stR X 53 ⟨rr50, r52, r51, rr52, rr51⟩ = ⟨rr51, r53, r52, rr53, rr52⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR54 : stR X 54 ⟨rr51, r53, r52, rr53, rr52⟩ = ⟨rr52, r54, r53, rr54, rr53⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR55 : stR X 55 ⟨rr52, r54, r53, rr54, rr53⟩ = ⟨rr53, r55, r54, rr55, rr54⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR56 : stR X 56 ⟨rr53, r55, r54, rr55, rr54⟩ = ⟨rr54, r56, r55, rr56, rr55⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR57 : stR X 57 ⟨rr54, r56, r55, rr56, rr55⟩ = ⟨rr55, r57, r56, rr57, rr56⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR58 : stR X 58 ⟨rr55, r57, r56, rr57, rr56⟩ = ⟨rr56, r58, r57, rr58, rr57⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR59 : stR X 59 ⟨rr56, r58, r57, rr58, rr57⟩ = ⟨rr57, r59, r58, rr59, rr58⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR60 : stR X 60 ⟨rr57, r59, r58, rr59, rr58⟩ = ⟨rr58, r60, r59, rr60, rr59⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR61 : stR X 61 ⟨rr58, r60, r59, rr60, rr59⟩ = ⟨rr59, r61, r60, rr61, rr60⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR62 : stR X 62 ⟨rr59, r61, r60, rr61, rr60⟩ = ⟨rr60, r62, r61, rr62, rr61⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR63 : stR X 63 ⟨rr60, r62, r61, rr62, rr61⟩ = ⟨rr61, r63, r62, rr63, rr62⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR64 : stR X 64 ⟨rr61, r63, r62, rr63, rr62⟩ = ⟨rr62, r64, r63, rr64, rr63⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR65 : stR X 65 ⟨rr62, r64, r63, rr64, rr63⟩ = ⟨rr63, r65, r64, rr65, rr64⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR66 : stR X 66 ⟨rr63, r65, r64, rr65, rr64⟩ = ⟨rr64, r66, r65, rr66, rr65⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR67 : stR X 67 ⟨rr64, r66, r65, rr66, rr65⟩ = ⟨rr65, r67, r66, rr67, rr66⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR68 : stR X 68 ⟨rr65, r67, r66, rr67, rr66⟩ = ⟨rr66, r68, r67, rr68, rr67⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR69 : stR X 69 ⟨rr66, r68, r67, rr68, rr67⟩ = ⟨rr67, r69, r68, rr69, rr68⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR70 : stR X 70 ⟨rr67, r69, r68, rr69, rr68⟩ = ⟨rr68, r70, r69, rr70, rr69⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR71 : stR X 71 ⟨rr68, r70, r69, rr70, rr69⟩ = ⟨rr69, r71, r70, rr71, rr70⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR72 : stR X 72 ⟨rr69, r71, r70, rr71, rr70⟩ = ⟨rr70, r72, r71, rr72, rr71⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR73 : stR X 73 ⟨rr70, r72, r71, rr72, rr71⟩ = ⟨rr71, r73, r72, rr73, rr72⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR74 : stR X 74 ⟨rr71, r73, r72, rr73, rr72⟩ = ⟨rr72, r74, r73, rr74, rr73⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR75 : stR X 75 ⟨rr72, r74, r73, rr74, rr73⟩ = ⟨rr73, r75, r74, rr75, rr74⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR76 : stR X 76 ⟨rr73, r75, r74, rr75, rr74⟩ = ⟨rr74, r76, r75, rr76, rr75⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR77 : stR X 77 ⟨rr74, r76, r75, rr76, rr75⟩ = ⟨rr75, r77, r76, rr77, rr76⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR78 : stR X 78 ⟨rr75, r77, r76, rr77, rr76⟩ = ⟨rr76, r78, r77, rr78, rr77⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have eR79 : stR X 79 ⟨rr76, r78, r77, rr78, rr77⟩ = ⟨rr77, r79, r78, rr79, rr78⟩ := by
    simp only [stR, RIPEMD160.step, RIPEMD160.r', RIPEMD160.s', RIPEMD160.K', List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, Nat.reduceDiv, Nat.reduceSub, getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, RIPEMD160.f, ↓reduceIte, UInt32.add_zero]
    rfl
  have hfun : (fun (p : RIPEMD160.State × RIPEMD160.State) (j : Nat) =>
      match p with
      | (a, b) => (RIPEMD160.step a (RIPEMD160.f j a.h₁ a.h₂ a.h₃) X[RIPEMD160.r[j]!]!
          RIPEMD160.K[j / 16]! RIPEMD160.s[j]!,
        RIPEMD160.step b (RIPEMD160.f (79 - j) b.h₁ b.h₂ b.h₃) X[RIPEMD160.r'[j]!]!
          RIPEMD160.K'[j / 16]! RIPEMD160.s'[j]!)) = fun p j => (stL X j p.1, stR X j p.2) := by
    funext p j; rfl
  have hL : (List.range 80).foldl (fun a j => stL X j a) h = ⟨lr77, l79, l78, lr79, lr78⟩ := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
      List.foldl_nil, eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13, eL14, eL15, eL16, eL17, eL18, eL19, eL20, eL21, eL22, eL23, eL24, eL25, eL26, eL27, eL28, eL29, eL30, eL31, eL32, eL33, eL34, eL35, eL36, eL37, eL38, eL39, eL40, eL41, eL42, eL43, eL44, eL45, eL46, eL47, eL48, eL49, eL50, eL51, eL52, eL53, eL54, eL55, eL56, eL57, eL58, eL59, eL60, eL61, eL62, eL63, eL64, eL65, eL66, eL67, eL68, eL69, eL70, eL71, eL72, eL73, eL74, eL75, eL76, eL77, eL78, eL79]
  have hR : (List.range 80).foldl (fun b j => stR X j b) h = ⟨rr77, r79, r78, rr79, rr78⟩ := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
      List.foldl_nil, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7, eR8, eR9, eR10, eR11, eR12, eR13, eR14, eR15, eR16, eR17, eR18, eR19, eR20, eR21, eR22, eR23, eR24, eR25, eR26, eR27, eR28, eR29, eR30, eR31, eR32, eR33, eR34, eR35, eR36, eR37, eR38, eR39, eR40, eR41, eR42, eR43, eR44, eR45, eR46, eR47, eR48, eR49, eR50, eR51, eR52, eR53, eR54, eR55, eR56, eR57, eR58, eR59, eR60, eR61, eR62, eR63, eR64, eR65, eR66, eR67, eR68, eR69, eR70, eR71, eR72, eR73, eR74, eR75, eR76, eR77, eR78, eR79]
  unfold RIPEMD160.compress
  rw [hfun, fold_pair, hL, hR]

end FeProofs.Ripemd160
