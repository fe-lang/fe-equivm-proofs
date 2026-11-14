import FeProofs.Precompiles.Ripemd160.Words
import FeProofs.Precompiles.Ripemd160.Hash

/-!
# Ripemd160: `ripemd_compress` is pure

The exported `ripemd_compress`, in 98 pieces, on the state of five words and a block of 64
bytes, is `pure` of `compressFe` on the sixteen little-endian words of the block
(`ripemd_compress_eq`): one `simp` over the pieces with the word lemmas of `Words.lean`, then
one `simp` that names each value by the let of `compressFe` it is (`extract_lets` gives the
names), so that the two sides meet without unfolding either.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ripemd160

open FeProofs.Precompiles
open Precompiles.Exported.Ripemd160

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **`ripemd_compress`** on the state `S` and the block of bytes `B`. -/
theorem ripemd_compress_eq (S : RIPEMD160.State) (B : ℕ → UInt8) :
    ripemd_compress (toV5 S) (toBlk B) = pure ((), toV5 (compressFe S (Xof B))) := by
  simp (config := { decide := true, maxSteps := 10000000 }) only [ripemd_compress, ripemd_compress_k1, ripemd_compress_k2, ripemd_compress_k3, ripemd_compress_k4, ripemd_compress_k5, ripemd_compress_k6, ripemd_compress_k7, ripemd_compress_k8, ripemd_compress_k9, ripemd_compress_k10, ripemd_compress_k11, ripemd_compress_k12, ripemd_compress_k13, ripemd_compress_k14, ripemd_compress_k15, ripemd_compress_k16, ripemd_compress_k17, ripemd_compress_k18, ripemd_compress_k19, ripemd_compress_k20, ripemd_compress_k21, ripemd_compress_k22, ripemd_compress_k23, ripemd_compress_k24, ripemd_compress_k25, ripemd_compress_k26, ripemd_compress_k27, ripemd_compress_k28, ripemd_compress_k29, ripemd_compress_k30, ripemd_compress_k31, ripemd_compress_k32, ripemd_compress_k33, ripemd_compress_k34, ripemd_compress_k35, ripemd_compress_k36, ripemd_compress_k37, ripemd_compress_k38, ripemd_compress_k39, ripemd_compress_k40, ripemd_compress_k41, ripemd_compress_k42, ripemd_compress_k43, ripemd_compress_k44, ripemd_compress_k45, ripemd_compress_k46, ripemd_compress_k47, ripemd_compress_k48, ripemd_compress_k49, ripemd_compress_k50, ripemd_compress_k51, ripemd_compress_k52, ripemd_compress_k53, ripemd_compress_k54, ripemd_compress_k55, ripemd_compress_k56, ripemd_compress_k57, ripemd_compress_k58, ripemd_compress_k59, ripemd_compress_k60, ripemd_compress_k61, ripemd_compress_k62, ripemd_compress_k63, ripemd_compress_k64, ripemd_compress_k65, ripemd_compress_k66, ripemd_compress_k67, ripemd_compress_k68, ripemd_compress_k69, ripemd_compress_k70, ripemd_compress_k71, ripemd_compress_k72, ripemd_compress_k73, ripemd_compress_k74, ripemd_compress_k75, ripemd_compress_k76, ripemd_compress_k77, ripemd_compress_k78, ripemd_compress_k79, ripemd_compress_k80, ripemd_compress_k81, ripemd_compress_k82, ripemd_compress_k83, ripemd_compress_k84, ripemd_compress_k85, ripemd_compress_k86, ripemd_compress_k87, ripemd_compress_k88, ripemd_compress_k89, ripemd_compress_k90, ripemd_compress_k91, ripemd_compress_k92, ripemd_compress_k93, ripemd_compress_k94, ripemd_compress_k95, ripemd_compress_k96, ripemd_compress_k97, checkIndex_lit, pure_bind, toNat_lit,
    toBlk_get, toV5_get0, toV5_get1, toV5_get2, toV5_get3, toV5_get4, shl_lw32, or_lw32,
    addW_lw32, addW_lit, rotate_lw32, f0_lw32, f1_lw32, f2_lw32, f3_lw32, f4_lw32, toV5_set0,
    toV5_set1, toV5_set2, toV5_set3, toV5_set4]
  unfold compressFe
  extract_lets w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 la lb lc ld le ra rb rc rd re l0 lr0 l1 lr1 l2 lr2 l3 lr3 l4 lr4 l5 lr5 l6 lr6 l7 lr7 l8 lr8 l9 lr9 l10 lr10 l11 lr11 l12 lr12 l13 lr13 l14 lr14 l15 lr15 l16 lr16 l17 lr17 l18 lr18 l19 lr19 l20 lr20 l21 lr21 l22 lr22 l23 lr23 l24 lr24 l25 lr25 l26 lr26 l27 lr27 l28 lr28 l29 lr29 l30 lr30 l31 lr31 l32 lr32 l33 lr33 l34 lr34 l35 lr35 l36 lr36 l37 lr37 l38 lr38 l39 lr39 l40 lr40 l41 lr41 l42 lr42 l43 lr43 l44 lr44 l45 lr45 l46 lr46 l47 lr47 l48 lr48 l49 lr49 l50 lr50 l51 lr51 l52 lr52 l53 lr53 l54 lr54 l55 lr55 l56 lr56 l57 lr57 l58 lr58 l59 lr59 l60 lr60 l61 lr61 l62 lr62 l63 lr63 l64 lr64 l65 lr65 l66 lr66 l67 lr67 l68 lr68 l69 lr69 l70 lr70 l71 lr71 l72 lr72 l73 lr73 l74 lr74 l75 lr75 l76 lr76 l77 lr77 l78 lr78 l79 lr79 r0 rr0 r1 rr1 r2 rr2 r3 rr3 r4 rr4 r5 rr5 r6 rr6 r7 rr7 r8 rr8 r9 rr9 r10 rr10 r11 rr11 r12 rr12 r13 rr13 r14 rr14 r15 rr15 r16 rr16 r17 rr17 r18 rr18 r19 rr19 r20 rr20 r21 rr21 r22 rr22 r23 rr23 r24 rr24 r25 rr25 r26 rr26 r27 rr27 r28 rr28 r29 rr29 r30 rr30 r31 rr31 r32 rr32 r33 rr33 r34 rr34 r35 rr35 r36 rr36 r37 rr37 r38 rr38 r39 rr39 r40 rr40 r41 rr41 r42 rr42 r43 rr43 r44 rr44 r45 rr45 r46 rr46 r47 rr47 r48 rr48 r49 rr49 r50 rr50 r51 rr51 r52 rr52 r53 rr53 r54 rr54 r55 rr55 r56 rr56 r57 rr57 r58 rr58 r59 rr59 r60 rr60 r61 rr61 r62 rr62 r63 rr63 r64 rr64 r65 rr65 r66 rr66 r67 rr67 r68 rr68 r69 rr69 r70 rr70 r71 rr71 r72 rr72 r73 rr73 r74 rr74 r75 rr75 r76 rr76 r77 rr77 r78 rr78 r79 rr79
  have e_w0 : (B 0).toUInt32 ||| (B 1).toUInt32 <<< UInt32.ofNat 8 ||| (B 2).toUInt32 <<< UInt32.ofNat 16 ||| (B 3).toUInt32 <<< UInt32.ofNat 24 = w0 := rfl
  have e_w1 : (B 4).toUInt32 ||| (B 5).toUInt32 <<< UInt32.ofNat 8 ||| (B 6).toUInt32 <<< UInt32.ofNat 16 ||| (B 7).toUInt32 <<< UInt32.ofNat 24 = w1 := rfl
  have e_w2 : (B 8).toUInt32 ||| (B 9).toUInt32 <<< UInt32.ofNat 8 ||| (B 10).toUInt32 <<< UInt32.ofNat 16 ||| (B 11).toUInt32 <<< UInt32.ofNat 24 = w2 := rfl
  have e_w3 : (B 12).toUInt32 ||| (B 13).toUInt32 <<< UInt32.ofNat 8 ||| (B 14).toUInt32 <<< UInt32.ofNat 16 ||| (B 15).toUInt32 <<< UInt32.ofNat 24 = w3 := rfl
  have e_w4 : (B 16).toUInt32 ||| (B 17).toUInt32 <<< UInt32.ofNat 8 ||| (B 18).toUInt32 <<< UInt32.ofNat 16 ||| (B 19).toUInt32 <<< UInt32.ofNat 24 = w4 := rfl
  have e_w5 : (B 20).toUInt32 ||| (B 21).toUInt32 <<< UInt32.ofNat 8 ||| (B 22).toUInt32 <<< UInt32.ofNat 16 ||| (B 23).toUInt32 <<< UInt32.ofNat 24 = w5 := rfl
  have e_w6 : (B 24).toUInt32 ||| (B 25).toUInt32 <<< UInt32.ofNat 8 ||| (B 26).toUInt32 <<< UInt32.ofNat 16 ||| (B 27).toUInt32 <<< UInt32.ofNat 24 = w6 := rfl
  have e_w7 : (B 28).toUInt32 ||| (B 29).toUInt32 <<< UInt32.ofNat 8 ||| (B 30).toUInt32 <<< UInt32.ofNat 16 ||| (B 31).toUInt32 <<< UInt32.ofNat 24 = w7 := rfl
  have e_w8 : (B 32).toUInt32 ||| (B 33).toUInt32 <<< UInt32.ofNat 8 ||| (B 34).toUInt32 <<< UInt32.ofNat 16 ||| (B 35).toUInt32 <<< UInt32.ofNat 24 = w8 := rfl
  have e_w9 : (B 36).toUInt32 ||| (B 37).toUInt32 <<< UInt32.ofNat 8 ||| (B 38).toUInt32 <<< UInt32.ofNat 16 ||| (B 39).toUInt32 <<< UInt32.ofNat 24 = w9 := rfl
  have e_w10 : (B 40).toUInt32 ||| (B 41).toUInt32 <<< UInt32.ofNat 8 ||| (B 42).toUInt32 <<< UInt32.ofNat 16 ||| (B 43).toUInt32 <<< UInt32.ofNat 24 = w10 := rfl
  have e_w11 : (B 44).toUInt32 ||| (B 45).toUInt32 <<< UInt32.ofNat 8 ||| (B 46).toUInt32 <<< UInt32.ofNat 16 ||| (B 47).toUInt32 <<< UInt32.ofNat 24 = w11 := rfl
  have e_w12 : (B 48).toUInt32 ||| (B 49).toUInt32 <<< UInt32.ofNat 8 ||| (B 50).toUInt32 <<< UInt32.ofNat 16 ||| (B 51).toUInt32 <<< UInt32.ofNat 24 = w12 := rfl
  have e_w13 : (B 52).toUInt32 ||| (B 53).toUInt32 <<< UInt32.ofNat 8 ||| (B 54).toUInt32 <<< UInt32.ofNat 16 ||| (B 55).toUInt32 <<< UInt32.ofNat 24 = w13 := rfl
  have e_w14 : (B 56).toUInt32 ||| (B 57).toUInt32 <<< UInt32.ofNat 8 ||| (B 58).toUInt32 <<< UInt32.ofNat 16 ||| (B 59).toUInt32 <<< UInt32.ofNat 24 = w14 := rfl
  have e_w15 : (B 60).toUInt32 ||| (B 61).toUInt32 <<< UInt32.ofNat 8 ||| (B 62).toUInt32 <<< UInt32.ofNat 16 ||| (B 63).toUInt32 <<< UInt32.ofNat 24 = w15 := rfl
  have e_l0 : RIPEMD160.rol (S.h₀ + (F0 S.h₁ S.h₂ S.h₃) + w0) 11 + S.h₄ = l0 := rfl
  have e_lr0 : RIPEMD160.rol (S.h₂) 10 = lr0 := rfl
  have e_l1 : RIPEMD160.rol (S.h₄ + (F0 l0 S.h₁ lr0) + w1) 14 + S.h₃ = l1 := rfl
  have e_lr1 : RIPEMD160.rol (S.h₁) 10 = lr1 := rfl
  have e_l2 : RIPEMD160.rol (S.h₃ + (F0 l1 l0 lr1) + w2) 15 + lr0 = l2 := rfl
  have e_lr2 : RIPEMD160.rol (l0) 10 = lr2 := rfl
  have e_l3 : RIPEMD160.rol (lr0 + (F0 l2 l1 lr2) + w3) 12 + lr1 = l3 := rfl
  have e_lr3 : RIPEMD160.rol (l1) 10 = lr3 := rfl
  have e_l4 : RIPEMD160.rol (lr1 + (F0 l3 l2 lr3) + w4) 5 + lr2 = l4 := rfl
  have e_lr4 : RIPEMD160.rol (l2) 10 = lr4 := rfl
  have e_l5 : RIPEMD160.rol (lr2 + (F0 l4 l3 lr4) + w5) 8 + lr3 = l5 := rfl
  have e_lr5 : RIPEMD160.rol (l3) 10 = lr5 := rfl
  have e_l6 : RIPEMD160.rol (lr3 + (F0 l5 l4 lr5) + w6) 7 + lr4 = l6 := rfl
  have e_lr6 : RIPEMD160.rol (l4) 10 = lr6 := rfl
  have e_l7 : RIPEMD160.rol (lr4 + (F0 l6 l5 lr6) + w7) 9 + lr5 = l7 := rfl
  have e_lr7 : RIPEMD160.rol (l5) 10 = lr7 := rfl
  have e_l8 : RIPEMD160.rol (lr5 + (F0 l7 l6 lr7) + w8) 11 + lr6 = l8 := rfl
  have e_lr8 : RIPEMD160.rol (l6) 10 = lr8 := rfl
  have e_l9 : RIPEMD160.rol (lr6 + (F0 l8 l7 lr8) + w9) 13 + lr7 = l9 := rfl
  have e_lr9 : RIPEMD160.rol (l7) 10 = lr9 := rfl
  have e_l10 : RIPEMD160.rol (lr7 + (F0 l9 l8 lr9) + w10) 14 + lr8 = l10 := rfl
  have e_lr10 : RIPEMD160.rol (l8) 10 = lr10 := rfl
  have e_l11 : RIPEMD160.rol (lr8 + (F0 l10 l9 lr10) + w11) 15 + lr9 = l11 := rfl
  have e_lr11 : RIPEMD160.rol (l9) 10 = lr11 := rfl
  have e_l12 : RIPEMD160.rol (lr9 + (F0 l11 l10 lr11) + w12) 6 + lr10 = l12 := rfl
  have e_lr12 : RIPEMD160.rol (l10) 10 = lr12 := rfl
  have e_l13 : RIPEMD160.rol (lr10 + (F0 l12 l11 lr12) + w13) 7 + lr11 = l13 := rfl
  have e_lr13 : RIPEMD160.rol (l11) 10 = lr13 := rfl
  have e_l14 : RIPEMD160.rol (lr11 + (F0 l13 l12 lr13) + w14) 9 + lr12 = l14 := rfl
  have e_lr14 : RIPEMD160.rol (l12) 10 = lr14 := rfl
  have e_l15 : RIPEMD160.rol (lr12 + (F0 l14 l13 lr14) + w15) 8 + lr13 = l15 := rfl
  have e_lr15 : RIPEMD160.rol (l13) 10 = lr15 := rfl
  have e_l16 : RIPEMD160.rol (lr13 + (F1 l15 l14 lr15) + w7 + UInt32.ofNat 1518500249) 7 + lr14 = l16 := rfl
  have e_lr16 : RIPEMD160.rol (l14) 10 = lr16 := rfl
  have e_l17 : RIPEMD160.rol (lr14 + (F1 l16 l15 lr16) + w4 + UInt32.ofNat 1518500249) 6 + lr15 = l17 := rfl
  have e_lr17 : RIPEMD160.rol (l15) 10 = lr17 := rfl
  have e_l18 : RIPEMD160.rol (lr15 + (F1 l17 l16 lr17) + w13 + UInt32.ofNat 1518500249) 8 + lr16 = l18 := rfl
  have e_lr18 : RIPEMD160.rol (l16) 10 = lr18 := rfl
  have e_l19 : RIPEMD160.rol (lr16 + (F1 l18 l17 lr18) + w1 + UInt32.ofNat 1518500249) 13 + lr17 = l19 := rfl
  have e_lr19 : RIPEMD160.rol (l17) 10 = lr19 := rfl
  have e_l20 : RIPEMD160.rol (lr17 + (F1 l19 l18 lr19) + w10 + UInt32.ofNat 1518500249) 11 + lr18 = l20 := rfl
  have e_lr20 : RIPEMD160.rol (l18) 10 = lr20 := rfl
  have e_l21 : RIPEMD160.rol (lr18 + (F1 l20 l19 lr20) + w6 + UInt32.ofNat 1518500249) 9 + lr19 = l21 := rfl
  have e_lr21 : RIPEMD160.rol (l19) 10 = lr21 := rfl
  have e_l22 : RIPEMD160.rol (lr19 + (F1 l21 l20 lr21) + w15 + UInt32.ofNat 1518500249) 7 + lr20 = l22 := rfl
  have e_lr22 : RIPEMD160.rol (l20) 10 = lr22 := rfl
  have e_l23 : RIPEMD160.rol (lr20 + (F1 l22 l21 lr22) + w3 + UInt32.ofNat 1518500249) 15 + lr21 = l23 := rfl
  have e_lr23 : RIPEMD160.rol (l21) 10 = lr23 := rfl
  have e_l24 : RIPEMD160.rol (lr21 + (F1 l23 l22 lr23) + w12 + UInt32.ofNat 1518500249) 7 + lr22 = l24 := rfl
  have e_lr24 : RIPEMD160.rol (l22) 10 = lr24 := rfl
  have e_l25 : RIPEMD160.rol (lr22 + (F1 l24 l23 lr24) + w0 + UInt32.ofNat 1518500249) 12 + lr23 = l25 := rfl
  have e_lr25 : RIPEMD160.rol (l23) 10 = lr25 := rfl
  have e_l26 : RIPEMD160.rol (lr23 + (F1 l25 l24 lr25) + w9 + UInt32.ofNat 1518500249) 15 + lr24 = l26 := rfl
  have e_lr26 : RIPEMD160.rol (l24) 10 = lr26 := rfl
  have e_l27 : RIPEMD160.rol (lr24 + (F1 l26 l25 lr26) + w5 + UInt32.ofNat 1518500249) 9 + lr25 = l27 := rfl
  have e_lr27 : RIPEMD160.rol (l25) 10 = lr27 := rfl
  have e_l28 : RIPEMD160.rol (lr25 + (F1 l27 l26 lr27) + w2 + UInt32.ofNat 1518500249) 11 + lr26 = l28 := rfl
  have e_lr28 : RIPEMD160.rol (l26) 10 = lr28 := rfl
  have e_l29 : RIPEMD160.rol (lr26 + (F1 l28 l27 lr28) + w14 + UInt32.ofNat 1518500249) 7 + lr27 = l29 := rfl
  have e_lr29 : RIPEMD160.rol (l27) 10 = lr29 := rfl
  have e_l30 : RIPEMD160.rol (lr27 + (F1 l29 l28 lr29) + w11 + UInt32.ofNat 1518500249) 13 + lr28 = l30 := rfl
  have e_lr30 : RIPEMD160.rol (l28) 10 = lr30 := rfl
  have e_l31 : RIPEMD160.rol (lr28 + (F1 l30 l29 lr30) + w8 + UInt32.ofNat 1518500249) 12 + lr29 = l31 := rfl
  have e_lr31 : RIPEMD160.rol (l29) 10 = lr31 := rfl
  have e_l32 : RIPEMD160.rol (lr29 + (F2 l31 l30 lr31) + w3 + UInt32.ofNat 1859775393) 11 + lr30 = l32 := rfl
  have e_lr32 : RIPEMD160.rol (l30) 10 = lr32 := rfl
  have e_l33 : RIPEMD160.rol (lr30 + (F2 l32 l31 lr32) + w10 + UInt32.ofNat 1859775393) 13 + lr31 = l33 := rfl
  have e_lr33 : RIPEMD160.rol (l31) 10 = lr33 := rfl
  have e_l34 : RIPEMD160.rol (lr31 + (F2 l33 l32 lr33) + w14 + UInt32.ofNat 1859775393) 6 + lr32 = l34 := rfl
  have e_lr34 : RIPEMD160.rol (l32) 10 = lr34 := rfl
  have e_l35 : RIPEMD160.rol (lr32 + (F2 l34 l33 lr34) + w4 + UInt32.ofNat 1859775393) 7 + lr33 = l35 := rfl
  have e_lr35 : RIPEMD160.rol (l33) 10 = lr35 := rfl
  have e_l36 : RIPEMD160.rol (lr33 + (F2 l35 l34 lr35) + w9 + UInt32.ofNat 1859775393) 14 + lr34 = l36 := rfl
  have e_lr36 : RIPEMD160.rol (l34) 10 = lr36 := rfl
  have e_l37 : RIPEMD160.rol (lr34 + (F2 l36 l35 lr36) + w15 + UInt32.ofNat 1859775393) 9 + lr35 = l37 := rfl
  have e_lr37 : RIPEMD160.rol (l35) 10 = lr37 := rfl
  have e_l38 : RIPEMD160.rol (lr35 + (F2 l37 l36 lr37) + w8 + UInt32.ofNat 1859775393) 13 + lr36 = l38 := rfl
  have e_lr38 : RIPEMD160.rol (l36) 10 = lr38 := rfl
  have e_l39 : RIPEMD160.rol (lr36 + (F2 l38 l37 lr38) + w1 + UInt32.ofNat 1859775393) 15 + lr37 = l39 := rfl
  have e_lr39 : RIPEMD160.rol (l37) 10 = lr39 := rfl
  have e_l40 : RIPEMD160.rol (lr37 + (F2 l39 l38 lr39) + w2 + UInt32.ofNat 1859775393) 14 + lr38 = l40 := rfl
  have e_lr40 : RIPEMD160.rol (l38) 10 = lr40 := rfl
  have e_l41 : RIPEMD160.rol (lr38 + (F2 l40 l39 lr40) + w7 + UInt32.ofNat 1859775393) 8 + lr39 = l41 := rfl
  have e_lr41 : RIPEMD160.rol (l39) 10 = lr41 := rfl
  have e_l42 : RIPEMD160.rol (lr39 + (F2 l41 l40 lr41) + w0 + UInt32.ofNat 1859775393) 13 + lr40 = l42 := rfl
  have e_lr42 : RIPEMD160.rol (l40) 10 = lr42 := rfl
  have e_l43 : RIPEMD160.rol (lr40 + (F2 l42 l41 lr42) + w6 + UInt32.ofNat 1859775393) 6 + lr41 = l43 := rfl
  have e_lr43 : RIPEMD160.rol (l41) 10 = lr43 := rfl
  have e_l44 : RIPEMD160.rol (lr41 + (F2 l43 l42 lr43) + w13 + UInt32.ofNat 1859775393) 5 + lr42 = l44 := rfl
  have e_lr44 : RIPEMD160.rol (l42) 10 = lr44 := rfl
  have e_l45 : RIPEMD160.rol (lr42 + (F2 l44 l43 lr44) + w11 + UInt32.ofNat 1859775393) 12 + lr43 = l45 := rfl
  have e_lr45 : RIPEMD160.rol (l43) 10 = lr45 := rfl
  have e_l46 : RIPEMD160.rol (lr43 + (F2 l45 l44 lr45) + w5 + UInt32.ofNat 1859775393) 7 + lr44 = l46 := rfl
  have e_lr46 : RIPEMD160.rol (l44) 10 = lr46 := rfl
  have e_l47 : RIPEMD160.rol (lr44 + (F2 l46 l45 lr46) + w12 + UInt32.ofNat 1859775393) 5 + lr45 = l47 := rfl
  have e_lr47 : RIPEMD160.rol (l45) 10 = lr47 := rfl
  have e_l48 : RIPEMD160.rol (lr45 + (F3 l47 l46 lr47) + w1 + UInt32.ofNat 2400959708) 11 + lr46 = l48 := rfl
  have e_lr48 : RIPEMD160.rol (l46) 10 = lr48 := rfl
  have e_l49 : RIPEMD160.rol (lr46 + (F3 l48 l47 lr48) + w9 + UInt32.ofNat 2400959708) 12 + lr47 = l49 := rfl
  have e_lr49 : RIPEMD160.rol (l47) 10 = lr49 := rfl
  have e_l50 : RIPEMD160.rol (lr47 + (F3 l49 l48 lr49) + w11 + UInt32.ofNat 2400959708) 14 + lr48 = l50 := rfl
  have e_lr50 : RIPEMD160.rol (l48) 10 = lr50 := rfl
  have e_l51 : RIPEMD160.rol (lr48 + (F3 l50 l49 lr50) + w10 + UInt32.ofNat 2400959708) 15 + lr49 = l51 := rfl
  have e_lr51 : RIPEMD160.rol (l49) 10 = lr51 := rfl
  have e_l52 : RIPEMD160.rol (lr49 + (F3 l51 l50 lr51) + w0 + UInt32.ofNat 2400959708) 14 + lr50 = l52 := rfl
  have e_lr52 : RIPEMD160.rol (l50) 10 = lr52 := rfl
  have e_l53 : RIPEMD160.rol (lr50 + (F3 l52 l51 lr52) + w8 + UInt32.ofNat 2400959708) 15 + lr51 = l53 := rfl
  have e_lr53 : RIPEMD160.rol (l51) 10 = lr53 := rfl
  have e_l54 : RIPEMD160.rol (lr51 + (F3 l53 l52 lr53) + w12 + UInt32.ofNat 2400959708) 9 + lr52 = l54 := rfl
  have e_lr54 : RIPEMD160.rol (l52) 10 = lr54 := rfl
  have e_l55 : RIPEMD160.rol (lr52 + (F3 l54 l53 lr54) + w4 + UInt32.ofNat 2400959708) 8 + lr53 = l55 := rfl
  have e_lr55 : RIPEMD160.rol (l53) 10 = lr55 := rfl
  have e_l56 : RIPEMD160.rol (lr53 + (F3 l55 l54 lr55) + w13 + UInt32.ofNat 2400959708) 9 + lr54 = l56 := rfl
  have e_lr56 : RIPEMD160.rol (l54) 10 = lr56 := rfl
  have e_l57 : RIPEMD160.rol (lr54 + (F3 l56 l55 lr56) + w3 + UInt32.ofNat 2400959708) 14 + lr55 = l57 := rfl
  have e_lr57 : RIPEMD160.rol (l55) 10 = lr57 := rfl
  have e_l58 : RIPEMD160.rol (lr55 + (F3 l57 l56 lr57) + w7 + UInt32.ofNat 2400959708) 5 + lr56 = l58 := rfl
  have e_lr58 : RIPEMD160.rol (l56) 10 = lr58 := rfl
  have e_l59 : RIPEMD160.rol (lr56 + (F3 l58 l57 lr58) + w15 + UInt32.ofNat 2400959708) 6 + lr57 = l59 := rfl
  have e_lr59 : RIPEMD160.rol (l57) 10 = lr59 := rfl
  have e_l60 : RIPEMD160.rol (lr57 + (F3 l59 l58 lr59) + w14 + UInt32.ofNat 2400959708) 8 + lr58 = l60 := rfl
  have e_lr60 : RIPEMD160.rol (l58) 10 = lr60 := rfl
  have e_l61 : RIPEMD160.rol (lr58 + (F3 l60 l59 lr60) + w5 + UInt32.ofNat 2400959708) 6 + lr59 = l61 := rfl
  have e_lr61 : RIPEMD160.rol (l59) 10 = lr61 := rfl
  have e_l62 : RIPEMD160.rol (lr59 + (F3 l61 l60 lr61) + w6 + UInt32.ofNat 2400959708) 5 + lr60 = l62 := rfl
  have e_lr62 : RIPEMD160.rol (l60) 10 = lr62 := rfl
  have e_l63 : RIPEMD160.rol (lr60 + (F3 l62 l61 lr62) + w2 + UInt32.ofNat 2400959708) 12 + lr61 = l63 := rfl
  have e_lr63 : RIPEMD160.rol (l61) 10 = lr63 := rfl
  have e_l64 : RIPEMD160.rol (lr61 + (F4 l63 l62 lr63) + w4 + UInt32.ofNat 2840853838) 9 + lr62 = l64 := rfl
  have e_lr64 : RIPEMD160.rol (l62) 10 = lr64 := rfl
  have e_l65 : RIPEMD160.rol (lr62 + (F4 l64 l63 lr64) + w0 + UInt32.ofNat 2840853838) 15 + lr63 = l65 := rfl
  have e_lr65 : RIPEMD160.rol (l63) 10 = lr65 := rfl
  have e_l66 : RIPEMD160.rol (lr63 + (F4 l65 l64 lr65) + w5 + UInt32.ofNat 2840853838) 5 + lr64 = l66 := rfl
  have e_lr66 : RIPEMD160.rol (l64) 10 = lr66 := rfl
  have e_l67 : RIPEMD160.rol (lr64 + (F4 l66 l65 lr66) + w9 + UInt32.ofNat 2840853838) 11 + lr65 = l67 := rfl
  have e_lr67 : RIPEMD160.rol (l65) 10 = lr67 := rfl
  have e_l68 : RIPEMD160.rol (lr65 + (F4 l67 l66 lr67) + w7 + UInt32.ofNat 2840853838) 6 + lr66 = l68 := rfl
  have e_lr68 : RIPEMD160.rol (l66) 10 = lr68 := rfl
  have e_l69 : RIPEMD160.rol (lr66 + (F4 l68 l67 lr68) + w12 + UInt32.ofNat 2840853838) 8 + lr67 = l69 := rfl
  have e_lr69 : RIPEMD160.rol (l67) 10 = lr69 := rfl
  have e_l70 : RIPEMD160.rol (lr67 + (F4 l69 l68 lr69) + w2 + UInt32.ofNat 2840853838) 13 + lr68 = l70 := rfl
  have e_lr70 : RIPEMD160.rol (l68) 10 = lr70 := rfl
  have e_l71 : RIPEMD160.rol (lr68 + (F4 l70 l69 lr70) + w10 + UInt32.ofNat 2840853838) 12 + lr69 = l71 := rfl
  have e_lr71 : RIPEMD160.rol (l69) 10 = lr71 := rfl
  have e_l72 : RIPEMD160.rol (lr69 + (F4 l71 l70 lr71) + w14 + UInt32.ofNat 2840853838) 5 + lr70 = l72 := rfl
  have e_lr72 : RIPEMD160.rol (l70) 10 = lr72 := rfl
  have e_l73 : RIPEMD160.rol (lr70 + (F4 l72 l71 lr72) + w1 + UInt32.ofNat 2840853838) 12 + lr71 = l73 := rfl
  have e_lr73 : RIPEMD160.rol (l71) 10 = lr73 := rfl
  have e_l74 : RIPEMD160.rol (lr71 + (F4 l73 l72 lr73) + w3 + UInt32.ofNat 2840853838) 13 + lr72 = l74 := rfl
  have e_lr74 : RIPEMD160.rol (l72) 10 = lr74 := rfl
  have e_l75 : RIPEMD160.rol (lr72 + (F4 l74 l73 lr74) + w8 + UInt32.ofNat 2840853838) 14 + lr73 = l75 := rfl
  have e_lr75 : RIPEMD160.rol (l73) 10 = lr75 := rfl
  have e_l76 : RIPEMD160.rol (lr73 + (F4 l75 l74 lr75) + w11 + UInt32.ofNat 2840853838) 11 + lr74 = l76 := rfl
  have e_lr76 : RIPEMD160.rol (l74) 10 = lr76 := rfl
  have e_l77 : RIPEMD160.rol (lr74 + (F4 l76 l75 lr76) + w6 + UInt32.ofNat 2840853838) 8 + lr75 = l77 := rfl
  have e_lr77 : RIPEMD160.rol (l75) 10 = lr77 := rfl
  have e_l78 : RIPEMD160.rol (lr75 + (F4 l77 l76 lr77) + w15 + UInt32.ofNat 2840853838) 5 + lr76 = l78 := rfl
  have e_lr78 : RIPEMD160.rol (l76) 10 = lr78 := rfl
  have e_l79 : RIPEMD160.rol (lr76 + (F4 l78 l77 lr78) + w13 + UInt32.ofNat 2840853838) 6 + lr77 = l79 := rfl
  have e_lr79 : RIPEMD160.rol (l77) 10 = lr79 := rfl
  have e_r0 : RIPEMD160.rol (S.h₀ + (F4 S.h₁ S.h₂ S.h₃) + w5 + UInt32.ofNat 1352829926) 8 + S.h₄ = r0 := rfl
  have e_r1 : RIPEMD160.rol (S.h₄ + (F4 r0 S.h₁ lr0) + w14 + UInt32.ofNat 1352829926) 9 + S.h₃ = r1 := rfl
  have e_r2 : RIPEMD160.rol (S.h₃ + (F4 r1 r0 lr1) + w7 + UInt32.ofNat 1352829926) 9 + lr0 = r2 := rfl
  have e_rr2 : RIPEMD160.rol (r0) 10 = rr2 := rfl
  have e_r3 : RIPEMD160.rol (lr0 + (F4 r2 r1 rr2) + w0 + UInt32.ofNat 1352829926) 11 + lr1 = r3 := rfl
  have e_rr3 : RIPEMD160.rol (r1) 10 = rr3 := rfl
  have e_r4 : RIPEMD160.rol (lr1 + (F4 r3 r2 rr3) + w9 + UInt32.ofNat 1352829926) 13 + rr2 = r4 := rfl
  have e_rr4 : RIPEMD160.rol (r2) 10 = rr4 := rfl
  have e_r5 : RIPEMD160.rol (rr2 + (F4 r4 r3 rr4) + w2 + UInt32.ofNat 1352829926) 15 + rr3 = r5 := rfl
  have e_rr5 : RIPEMD160.rol (r3) 10 = rr5 := rfl
  have e_r6 : RIPEMD160.rol (rr3 + (F4 r5 r4 rr5) + w11 + UInt32.ofNat 1352829926) 15 + rr4 = r6 := rfl
  have e_rr6 : RIPEMD160.rol (r4) 10 = rr6 := rfl
  have e_r7 : RIPEMD160.rol (rr4 + (F4 r6 r5 rr6) + w4 + UInt32.ofNat 1352829926) 5 + rr5 = r7 := rfl
  have e_rr7 : RIPEMD160.rol (r5) 10 = rr7 := rfl
  have e_r8 : RIPEMD160.rol (rr5 + (F4 r7 r6 rr7) + w13 + UInt32.ofNat 1352829926) 7 + rr6 = r8 := rfl
  have e_rr8 : RIPEMD160.rol (r6) 10 = rr8 := rfl
  have e_r9 : RIPEMD160.rol (rr6 + (F4 r8 r7 rr8) + w6 + UInt32.ofNat 1352829926) 7 + rr7 = r9 := rfl
  have e_rr9 : RIPEMD160.rol (r7) 10 = rr9 := rfl
  have e_r10 : RIPEMD160.rol (rr7 + (F4 r9 r8 rr9) + w15 + UInt32.ofNat 1352829926) 8 + rr8 = r10 := rfl
  have e_rr10 : RIPEMD160.rol (r8) 10 = rr10 := rfl
  have e_r11 : RIPEMD160.rol (rr8 + (F4 r10 r9 rr10) + w8 + UInt32.ofNat 1352829926) 11 + rr9 = r11 := rfl
  have e_rr11 : RIPEMD160.rol (r9) 10 = rr11 := rfl
  have e_r12 : RIPEMD160.rol (rr9 + (F4 r11 r10 rr11) + w1 + UInt32.ofNat 1352829926) 14 + rr10 = r12 := rfl
  have e_rr12 : RIPEMD160.rol (r10) 10 = rr12 := rfl
  have e_r13 : RIPEMD160.rol (rr10 + (F4 r12 r11 rr12) + w10 + UInt32.ofNat 1352829926) 14 + rr11 = r13 := rfl
  have e_rr13 : RIPEMD160.rol (r11) 10 = rr13 := rfl
  have e_r14 : RIPEMD160.rol (rr11 + (F4 r13 r12 rr13) + w3 + UInt32.ofNat 1352829926) 12 + rr12 = r14 := rfl
  have e_rr14 : RIPEMD160.rol (r12) 10 = rr14 := rfl
  have e_r15 : RIPEMD160.rol (rr12 + (F4 r14 r13 rr14) + w12 + UInt32.ofNat 1352829926) 6 + rr13 = r15 := rfl
  have e_rr15 : RIPEMD160.rol (r13) 10 = rr15 := rfl
  have e_r16 : RIPEMD160.rol (rr13 + (F3 r15 r14 rr15) + w6 + UInt32.ofNat 1548603684) 9 + rr14 = r16 := rfl
  have e_rr16 : RIPEMD160.rol (r14) 10 = rr16 := rfl
  have e_r17 : RIPEMD160.rol (rr14 + (F3 r16 r15 rr16) + w11 + UInt32.ofNat 1548603684) 13 + rr15 = r17 := rfl
  have e_rr17 : RIPEMD160.rol (r15) 10 = rr17 := rfl
  have e_r18 : RIPEMD160.rol (rr15 + (F3 r17 r16 rr17) + w3 + UInt32.ofNat 1548603684) 15 + rr16 = r18 := rfl
  have e_rr18 : RIPEMD160.rol (r16) 10 = rr18 := rfl
  have e_r19 : RIPEMD160.rol (rr16 + (F3 r18 r17 rr18) + w7 + UInt32.ofNat 1548603684) 7 + rr17 = r19 := rfl
  have e_rr19 : RIPEMD160.rol (r17) 10 = rr19 := rfl
  have e_r20 : RIPEMD160.rol (rr17 + (F3 r19 r18 rr19) + w0 + UInt32.ofNat 1548603684) 12 + rr18 = r20 := rfl
  have e_rr20 : RIPEMD160.rol (r18) 10 = rr20 := rfl
  have e_r21 : RIPEMD160.rol (rr18 + (F3 r20 r19 rr20) + w13 + UInt32.ofNat 1548603684) 8 + rr19 = r21 := rfl
  have e_rr21 : RIPEMD160.rol (r19) 10 = rr21 := rfl
  have e_r22 : RIPEMD160.rol (rr19 + (F3 r21 r20 rr21) + w5 + UInt32.ofNat 1548603684) 9 + rr20 = r22 := rfl
  have e_rr22 : RIPEMD160.rol (r20) 10 = rr22 := rfl
  have e_r23 : RIPEMD160.rol (rr20 + (F3 r22 r21 rr22) + w10 + UInt32.ofNat 1548603684) 11 + rr21 = r23 := rfl
  have e_rr23 : RIPEMD160.rol (r21) 10 = rr23 := rfl
  have e_r24 : RIPEMD160.rol (rr21 + (F3 r23 r22 rr23) + w14 + UInt32.ofNat 1548603684) 7 + rr22 = r24 := rfl
  have e_rr24 : RIPEMD160.rol (r22) 10 = rr24 := rfl
  have e_r25 : RIPEMD160.rol (rr22 + (F3 r24 r23 rr24) + w15 + UInt32.ofNat 1548603684) 7 + rr23 = r25 := rfl
  have e_rr25 : RIPEMD160.rol (r23) 10 = rr25 := rfl
  have e_r26 : RIPEMD160.rol (rr23 + (F3 r25 r24 rr25) + w8 + UInt32.ofNat 1548603684) 12 + rr24 = r26 := rfl
  have e_rr26 : RIPEMD160.rol (r24) 10 = rr26 := rfl
  have e_r27 : RIPEMD160.rol (rr24 + (F3 r26 r25 rr26) + w12 + UInt32.ofNat 1548603684) 7 + rr25 = r27 := rfl
  have e_rr27 : RIPEMD160.rol (r25) 10 = rr27 := rfl
  have e_r28 : RIPEMD160.rol (rr25 + (F3 r27 r26 rr27) + w4 + UInt32.ofNat 1548603684) 6 + rr26 = r28 := rfl
  have e_rr28 : RIPEMD160.rol (r26) 10 = rr28 := rfl
  have e_r29 : RIPEMD160.rol (rr26 + (F3 r28 r27 rr28) + w9 + UInt32.ofNat 1548603684) 15 + rr27 = r29 := rfl
  have e_rr29 : RIPEMD160.rol (r27) 10 = rr29 := rfl
  have e_r30 : RIPEMD160.rol (rr27 + (F3 r29 r28 rr29) + w1 + UInt32.ofNat 1548603684) 13 + rr28 = r30 := rfl
  have e_rr30 : RIPEMD160.rol (r28) 10 = rr30 := rfl
  have e_r31 : RIPEMD160.rol (rr28 + (F3 r30 r29 rr30) + w2 + UInt32.ofNat 1548603684) 11 + rr29 = r31 := rfl
  have e_rr31 : RIPEMD160.rol (r29) 10 = rr31 := rfl
  have e_r32 : RIPEMD160.rol (rr29 + (F2 r31 r30 rr31) + w15 + UInt32.ofNat 1836072691) 9 + rr30 = r32 := rfl
  have e_rr32 : RIPEMD160.rol (r30) 10 = rr32 := rfl
  have e_r33 : RIPEMD160.rol (rr30 + (F2 r32 r31 rr32) + w5 + UInt32.ofNat 1836072691) 7 + rr31 = r33 := rfl
  have e_rr33 : RIPEMD160.rol (r31) 10 = rr33 := rfl
  have e_r34 : RIPEMD160.rol (rr31 + (F2 r33 r32 rr33) + w1 + UInt32.ofNat 1836072691) 15 + rr32 = r34 := rfl
  have e_rr34 : RIPEMD160.rol (r32) 10 = rr34 := rfl
  have e_r35 : RIPEMD160.rol (rr32 + (F2 r34 r33 rr34) + w3 + UInt32.ofNat 1836072691) 11 + rr33 = r35 := rfl
  have e_rr35 : RIPEMD160.rol (r33) 10 = rr35 := rfl
  have e_r36 : RIPEMD160.rol (rr33 + (F2 r35 r34 rr35) + w7 + UInt32.ofNat 1836072691) 8 + rr34 = r36 := rfl
  have e_rr36 : RIPEMD160.rol (r34) 10 = rr36 := rfl
  have e_r37 : RIPEMD160.rol (rr34 + (F2 r36 r35 rr36) + w14 + UInt32.ofNat 1836072691) 6 + rr35 = r37 := rfl
  have e_rr37 : RIPEMD160.rol (r35) 10 = rr37 := rfl
  have e_r38 : RIPEMD160.rol (rr35 + (F2 r37 r36 rr37) + w6 + UInt32.ofNat 1836072691) 6 + rr36 = r38 := rfl
  have e_rr38 : RIPEMD160.rol (r36) 10 = rr38 := rfl
  have e_r39 : RIPEMD160.rol (rr36 + (F2 r38 r37 rr38) + w9 + UInt32.ofNat 1836072691) 14 + rr37 = r39 := rfl
  have e_rr39 : RIPEMD160.rol (r37) 10 = rr39 := rfl
  have e_r40 : RIPEMD160.rol (rr37 + (F2 r39 r38 rr39) + w11 + UInt32.ofNat 1836072691) 12 + rr38 = r40 := rfl
  have e_rr40 : RIPEMD160.rol (r38) 10 = rr40 := rfl
  have e_r41 : RIPEMD160.rol (rr38 + (F2 r40 r39 rr40) + w8 + UInt32.ofNat 1836072691) 13 + rr39 = r41 := rfl
  have e_rr41 : RIPEMD160.rol (r39) 10 = rr41 := rfl
  have e_r42 : RIPEMD160.rol (rr39 + (F2 r41 r40 rr41) + w12 + UInt32.ofNat 1836072691) 5 + rr40 = r42 := rfl
  have e_rr42 : RIPEMD160.rol (r40) 10 = rr42 := rfl
  have e_r43 : RIPEMD160.rol (rr40 + (F2 r42 r41 rr42) + w2 + UInt32.ofNat 1836072691) 14 + rr41 = r43 := rfl
  have e_rr43 : RIPEMD160.rol (r41) 10 = rr43 := rfl
  have e_r44 : RIPEMD160.rol (rr41 + (F2 r43 r42 rr43) + w10 + UInt32.ofNat 1836072691) 13 + rr42 = r44 := rfl
  have e_rr44 : RIPEMD160.rol (r42) 10 = rr44 := rfl
  have e_r45 : RIPEMD160.rol (rr42 + (F2 r44 r43 rr44) + w0 + UInt32.ofNat 1836072691) 13 + rr43 = r45 := rfl
  have e_rr45 : RIPEMD160.rol (r43) 10 = rr45 := rfl
  have e_r46 : RIPEMD160.rol (rr43 + (F2 r45 r44 rr45) + w4 + UInt32.ofNat 1836072691) 7 + rr44 = r46 := rfl
  have e_rr46 : RIPEMD160.rol (r44) 10 = rr46 := rfl
  have e_r47 : RIPEMD160.rol (rr44 + (F2 r46 r45 rr46) + w13 + UInt32.ofNat 1836072691) 5 + rr45 = r47 := rfl
  have e_rr47 : RIPEMD160.rol (r45) 10 = rr47 := rfl
  have e_r48 : RIPEMD160.rol (rr45 + (F1 r47 r46 rr47) + w8 + UInt32.ofNat 2053994217) 15 + rr46 = r48 := rfl
  have e_rr48 : RIPEMD160.rol (r46) 10 = rr48 := rfl
  have e_r49 : RIPEMD160.rol (rr46 + (F1 r48 r47 rr48) + w6 + UInt32.ofNat 2053994217) 5 + rr47 = r49 := rfl
  have e_rr49 : RIPEMD160.rol (r47) 10 = rr49 := rfl
  have e_r50 : RIPEMD160.rol (rr47 + (F1 r49 r48 rr49) + w4 + UInt32.ofNat 2053994217) 8 + rr48 = r50 := rfl
  have e_rr50 : RIPEMD160.rol (r48) 10 = rr50 := rfl
  have e_r51 : RIPEMD160.rol (rr48 + (F1 r50 r49 rr50) + w1 + UInt32.ofNat 2053994217) 11 + rr49 = r51 := rfl
  have e_rr51 : RIPEMD160.rol (r49) 10 = rr51 := rfl
  have e_r52 : RIPEMD160.rol (rr49 + (F1 r51 r50 rr51) + w3 + UInt32.ofNat 2053994217) 14 + rr50 = r52 := rfl
  have e_rr52 : RIPEMD160.rol (r50) 10 = rr52 := rfl
  have e_r53 : RIPEMD160.rol (rr50 + (F1 r52 r51 rr52) + w11 + UInt32.ofNat 2053994217) 14 + rr51 = r53 := rfl
  have e_rr53 : RIPEMD160.rol (r51) 10 = rr53 := rfl
  have e_r54 : RIPEMD160.rol (rr51 + (F1 r53 r52 rr53) + w15 + UInt32.ofNat 2053994217) 6 + rr52 = r54 := rfl
  have e_rr54 : RIPEMD160.rol (r52) 10 = rr54 := rfl
  have e_r55 : RIPEMD160.rol (rr52 + (F1 r54 r53 rr54) + w0 + UInt32.ofNat 2053994217) 14 + rr53 = r55 := rfl
  have e_rr55 : RIPEMD160.rol (r53) 10 = rr55 := rfl
  have e_r56 : RIPEMD160.rol (rr53 + (F1 r55 r54 rr55) + w5 + UInt32.ofNat 2053994217) 6 + rr54 = r56 := rfl
  have e_rr56 : RIPEMD160.rol (r54) 10 = rr56 := rfl
  have e_r57 : RIPEMD160.rol (rr54 + (F1 r56 r55 rr56) + w12 + UInt32.ofNat 2053994217) 9 + rr55 = r57 := rfl
  have e_rr57 : RIPEMD160.rol (r55) 10 = rr57 := rfl
  have e_r58 : RIPEMD160.rol (rr55 + (F1 r57 r56 rr57) + w2 + UInt32.ofNat 2053994217) 12 + rr56 = r58 := rfl
  have e_rr58 : RIPEMD160.rol (r56) 10 = rr58 := rfl
  have e_r59 : RIPEMD160.rol (rr56 + (F1 r58 r57 rr58) + w13 + UInt32.ofNat 2053994217) 9 + rr57 = r59 := rfl
  have e_rr59 : RIPEMD160.rol (r57) 10 = rr59 := rfl
  have e_r60 : RIPEMD160.rol (rr57 + (F1 r59 r58 rr59) + w9 + UInt32.ofNat 2053994217) 12 + rr58 = r60 := rfl
  have e_rr60 : RIPEMD160.rol (r58) 10 = rr60 := rfl
  have e_r61 : RIPEMD160.rol (rr58 + (F1 r60 r59 rr60) + w7 + UInt32.ofNat 2053994217) 5 + rr59 = r61 := rfl
  have e_rr61 : RIPEMD160.rol (r59) 10 = rr61 := rfl
  have e_r62 : RIPEMD160.rol (rr59 + (F1 r61 r60 rr61) + w10 + UInt32.ofNat 2053994217) 15 + rr60 = r62 := rfl
  have e_rr62 : RIPEMD160.rol (r60) 10 = rr62 := rfl
  have e_r63 : RIPEMD160.rol (rr60 + (F1 r62 r61 rr62) + w14 + UInt32.ofNat 2053994217) 8 + rr61 = r63 := rfl
  have e_rr63 : RIPEMD160.rol (r61) 10 = rr63 := rfl
  have e_r64 : RIPEMD160.rol (rr61 + (F0 r63 r62 rr63) + w12) 8 + rr62 = r64 := rfl
  have e_rr64 : RIPEMD160.rol (r62) 10 = rr64 := rfl
  have e_r65 : RIPEMD160.rol (rr62 + (F0 r64 r63 rr64) + w15) 5 + rr63 = r65 := rfl
  have e_rr65 : RIPEMD160.rol (r63) 10 = rr65 := rfl
  have e_r66 : RIPEMD160.rol (rr63 + (F0 r65 r64 rr65) + w10) 12 + rr64 = r66 := rfl
  have e_rr66 : RIPEMD160.rol (r64) 10 = rr66 := rfl
  have e_r67 : RIPEMD160.rol (rr64 + (F0 r66 r65 rr66) + w4) 9 + rr65 = r67 := rfl
  have e_rr67 : RIPEMD160.rol (r65) 10 = rr67 := rfl
  have e_r68 : RIPEMD160.rol (rr65 + (F0 r67 r66 rr67) + w1) 12 + rr66 = r68 := rfl
  have e_rr68 : RIPEMD160.rol (r66) 10 = rr68 := rfl
  have e_r69 : RIPEMD160.rol (rr66 + (F0 r68 r67 rr68) + w5) 5 + rr67 = r69 := rfl
  have e_rr69 : RIPEMD160.rol (r67) 10 = rr69 := rfl
  have e_r70 : RIPEMD160.rol (rr67 + (F0 r69 r68 rr69) + w8) 14 + rr68 = r70 := rfl
  have e_rr70 : RIPEMD160.rol (r68) 10 = rr70 := rfl
  have e_r71 : RIPEMD160.rol (rr68 + (F0 r70 r69 rr70) + w7) 6 + rr69 = r71 := rfl
  have e_rr71 : RIPEMD160.rol (r69) 10 = rr71 := rfl
  have e_r72 : RIPEMD160.rol (rr69 + (F0 r71 r70 rr71) + w6) 8 + rr70 = r72 := rfl
  have e_rr72 : RIPEMD160.rol (r70) 10 = rr72 := rfl
  have e_r73 : RIPEMD160.rol (rr70 + (F0 r72 r71 rr72) + w2) 13 + rr71 = r73 := rfl
  have e_rr73 : RIPEMD160.rol (r71) 10 = rr73 := rfl
  have e_r74 : RIPEMD160.rol (rr71 + (F0 r73 r72 rr73) + w13) 6 + rr72 = r74 := rfl
  have e_rr74 : RIPEMD160.rol (r72) 10 = rr74 := rfl
  have e_r75 : RIPEMD160.rol (rr72 + (F0 r74 r73 rr74) + w14) 5 + rr73 = r75 := rfl
  have e_rr75 : RIPEMD160.rol (r73) 10 = rr75 := rfl
  have e_r76 : RIPEMD160.rol (rr73 + (F0 r75 r74 rr75) + w0) 15 + rr74 = r76 := rfl
  have e_rr76 : RIPEMD160.rol (r74) 10 = rr76 := rfl
  have e_r77 : RIPEMD160.rol (rr74 + (F0 r76 r75 rr76) + w3) 13 + rr75 = r77 := rfl
  have e_rr77 : RIPEMD160.rol (r75) 10 = rr77 := rfl
  have e_r78 : RIPEMD160.rol (rr75 + (F0 r77 r76 rr77) + w9) 11 + rr76 = r78 := rfl
  have e_rr78 : RIPEMD160.rol (r76) 10 = rr78 := rfl
  have e_r79 : RIPEMD160.rol (rr76 + (F0 r78 r77 rr78) + w11) 11 + rr77 = r79 := rfl
  have e_rr79 : RIPEMD160.rol (r77) 10 = rr79 := rfl
  simp only [e_w0, e_w1, e_w2, e_w3, e_w4, e_w5, e_w6, e_w7, e_w8, e_w9, e_w10, e_w11, e_w12, e_w13, e_w14, e_w15, e_l0, e_lr0, e_l1, e_lr1, e_l2, e_lr2, e_l3, e_lr3, e_l4, e_lr4, e_l5, e_lr5, e_l6, e_lr6, e_l7, e_lr7, e_l8, e_lr8, e_l9, e_lr9, e_l10, e_lr10, e_l11, e_lr11, e_l12, e_lr12, e_l13, e_lr13, e_l14, e_lr14, e_l15, e_lr15, e_l16, e_lr16, e_l17, e_lr17, e_l18, e_lr18, e_l19, e_lr19, e_l20, e_lr20, e_l21, e_lr21, e_l22, e_lr22, e_l23, e_lr23, e_l24, e_lr24, e_l25, e_lr25, e_l26, e_lr26, e_l27, e_lr27, e_l28, e_lr28, e_l29, e_lr29, e_l30, e_lr30, e_l31, e_lr31, e_l32, e_lr32, e_l33, e_lr33, e_l34, e_lr34, e_l35, e_lr35, e_l36, e_lr36, e_l37, e_lr37, e_l38, e_lr38, e_l39, e_lr39, e_l40, e_lr40, e_l41, e_lr41, e_l42, e_lr42, e_l43, e_lr43, e_l44, e_lr44, e_l45, e_lr45, e_l46, e_lr46, e_l47, e_lr47, e_l48, e_lr48, e_l49, e_lr49, e_l50, e_lr50, e_l51, e_lr51, e_l52, e_lr52, e_l53, e_lr53, e_l54, e_lr54, e_l55, e_lr55, e_l56, e_lr56, e_l57, e_lr57, e_l58, e_lr58, e_l59, e_lr59, e_l60, e_lr60, e_l61, e_lr61, e_l62, e_lr62, e_l63, e_lr63, e_l64, e_lr64, e_l65, e_lr65, e_l66, e_lr66, e_l67, e_lr67, e_l68, e_lr68, e_l69, e_lr69, e_l70, e_lr70, e_l71, e_lr71, e_l72, e_lr72, e_l73, e_lr73, e_l74, e_lr74, e_l75, e_lr75, e_l76, e_lr76, e_l77, e_lr77, e_l78, e_lr78, e_l79, e_lr79, e_r0, e_r1, e_r2, e_rr2, e_r3, e_rr3, e_r4, e_rr4, e_r5, e_rr5, e_r6, e_rr6, e_r7, e_rr7, e_r8, e_rr8, e_r9, e_rr9, e_r10, e_rr10, e_r11, e_rr11, e_r12, e_rr12, e_r13, e_rr13, e_r14, e_rr14, e_r15, e_rr15, e_r16, e_rr16, e_r17, e_rr17, e_r18, e_rr18, e_r19, e_rr19, e_r20, e_rr20, e_r21, e_rr21, e_r22, e_rr22, e_r23, e_rr23, e_r24, e_rr24, e_r25, e_rr25, e_r26, e_rr26, e_r27, e_rr27, e_r28, e_rr28, e_r29, e_rr29, e_r30, e_rr30, e_r31, e_rr31, e_r32, e_rr32, e_r33, e_rr33, e_r34, e_rr34, e_r35, e_rr35, e_r36, e_rr36, e_r37, e_rr37, e_r38, e_rr38, e_r39, e_rr39, e_r40, e_rr40, e_r41, e_rr41, e_r42, e_rr42, e_r43, e_rr43, e_r44, e_rr44, e_r45, e_rr45, e_r46, e_rr46, e_r47, e_rr47, e_r48, e_rr48, e_r49, e_rr49, e_r50, e_rr50, e_r51, e_rr51, e_r52, e_rr52, e_r53, e_rr53, e_r54, e_rr54, e_r55, e_rr55, e_r56, e_rr56, e_r57, e_rr57, e_r58, e_rr58, e_r59, e_rr59, e_r60, e_rr60, e_r61, e_rr61, e_r62, e_rr62, e_r63, e_rr63, e_r64, e_rr64, e_r65, e_rr65, e_r66, e_rr66, e_r67, e_rr67, e_r68, e_rr68, e_r69, e_rr69, e_r70, e_rr70, e_r71, e_rr71, e_r72, e_rr72, e_r73, e_rr73, e_r74, e_rr74, e_r75, e_rr75, e_r76, e_rr76, e_r77, e_rr77, e_r78, e_rr78, e_r79, e_rr79]

end FeProofs.Ripemd160
