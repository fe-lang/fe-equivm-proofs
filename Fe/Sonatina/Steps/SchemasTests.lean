import Fe.Sonatina.Steps.SchemasCheck

/-!
# Tests of the schema library, evaluated by `decide`

Each `example` is checked by kernel evaluation (`decide +kernel`, which adds no axiom).  The
rejected cases include the counterexamples of review finding H-7.
-/

namespace Fe.Sonatina.Steps.Schemas.Tests

open Fe.Sonatina.Steps.Schemas KB

/-- No fact for any atom. -/
abbrev none' : Nat → KB := fun _ => unknown

/-- Atom 0 with its top 248 bits known zero, others unknown. -/
abbrev low8 : Nat → KB := fun v => if v = 0 then ⟨M ^^^ 255, 0⟩ else unknown

def x : Term := .atom 0
def y : Term := .atom 1
def n (w : Nat) : Term := .lit w

/-! ## Word semantics: corners, and agreement with `Interp.lean` -/

-- Shifts by 256 or more.
example : evalConst (.op2 .shl) [256, 1] = some 0 := by decide +kernel
example : evalConst (.op2 .shr) [300, M] = some 0 := by decide +kernel
example : evalConst (.op2 .sar) [256, M - 7] = some M := by decide +kernel
example : evalConst (.op2 .sar) [256, 7] = some 0 := by decide +kernel
example : evalConst (.op2 .sar) [255, 2 ^ 255] = some M := by decide +kernel
example : evalConst (.op2 .sar) [4, M - 31] = some (M - 1) := by decide +kernel
-- Division and modulo by zero; `sdiv` of the minimum by -1; signs of `smod`.
example : evalConst (.op2 .udiv) [7, 0] = some 0 := by decide +kernel
example : evalConst (.op2 .umod) [7, 0] = some 0 := by decide +kernel
example : evalConst (.op2 .sdiv) [2 ^ 255, M] = some (2 ^ 255) := by decide +kernel
example : evalConst (.op2 .sdiv) [W - 7, 2] = some (W - 3) := by decide +kernel
example : evalConst (.op2 .smod) [W - 7, 2] = some M := by decide +kernel
example : evalConst (.op2 .smod) [7, W - 2] = some 1 := by decide +kernel
-- `exp`.
example : evalConst (.op2 .exp) [2, 255] = some (2 ^ 255) := by decide +kernel
example : evalConst (.op2 .exp) [2, 256] = some 0 := by decide +kernel
example : evalConst (.op2 .exp) [3, 5] = some 243 := by decide +kernel
example : evalConst (.op2 .exp) [0, 0] = some 1 := by decide +kernel
-- `byte` past 31, `signextend` at 31 and past.
example : evalConst (.op2 .byte) [31, 0x1234] = some 0x34 := by decide +kernel
example : evalConst (.op2 .byte) [30, 0x1234] = some 0x12 := by decide +kernel
example : evalConst (.op2 .byte) [32, M] = some 0 := by decide +kernel
example : evalConst (.op2 .signextend) [0, 0x80] = some (W - 128) := by decide +kernel
example : evalConst (.op2 .signextend) [0, 0x17f] = some 0x7f := by decide +kernel
example : evalConst (.op2 .signextend) [31, 5] = some 5 := by decide +kernel
example : evalConst (.op2 .signextend) [32, 0x80] = some 0x80 := by decide +kernel
-- `addmod`, `mulmod` without wrapping, and by zero.
example : evalConst (.op3 .addmod) [M, 2, 7] = some ((M + 2) % 7) := by decide +kernel
example : evalConst (.op3 .mulmod) [M, M, 12] = some ((M * M) % 12) := by decide +kernel
example : evalConst (.op3 .addmod) [5, 6, 0] = some 0 := by decide +kernel
example : evalConst (.op3 .mulmod) [5, 6, 0] = some 0 := by decide +kernel
-- `clz`, `is_zero`, comparisons as words.
example : evalConst (.op1 .clz) [0] = some 256 := by decide +kernel
example : evalConst (.op1 .clz) [1] = some 255 := by decide +kernel
example : evalConst (.op1 .clz) [M] = some 0 := by decide +kernel
example : evalConst (.op1 .isZero) [0] = some 1 := by decide +kernel
example : evalConst (.op2 .slt) [M, 0] = some 1 := by decide +kernel
example : evalConst (.op2 .lt) [M, 0] = some 0 := by decide +kernel
example : evalConst (.op2 .sgt) [0, 2 ^ 255] = some 1 := by decide +kernel
-- Out of range or wrong arity.
example : evalConst (.op2 .add) [W, 0] = none := by decide +kernel
example : evalConst (.op2 .add) [1] = none := by decide +kernel

-- The word functions are the interpreter's, here on corner cases.
example : BinOp.eval .sar 256 3 (W - 8) = Op2.eval .sar 3 (W - 8) := by decide +kernel
example : BinOp.eval .sar 256 300 (W - 8) = Op2.eval .sar 300 (W - 8) := by decide +kernel
example : BinOp.eval .evmSignExtend 256 0 0xff = Op2.eval .signextend 0 0xff := by
  decide +kernel
example : BinOp.eval .evmByte 256 1 (2 ^ 248 * 0xab + 2 ^ 240 * 0xcd) =
    Op2.eval .byte 1 (2 ^ 248 * 0xab + 2 ^ 240 * 0xcd) := by decide +kernel
example : BinOp.eval .evmSdiv 256 (2 ^ 255) M = Op2.eval .sdiv (2 ^ 255) M := by decide +kernel
example : BinOp.eval .sub 256 3 5 = Op2.eval .sub 3 5 := by decide +kernel

/-! ## Known bits -/

-- Design §4.5's example: `shr 248 v4` has its top 248 bits known zero.
example : transfer2 .shr (exact 248) unknown = ⟨M ^^^ 255, 0⟩ := by decide +kernel
example : (transfer2 .and ⟨M ^^^ 255, 0⟩ (exact 0x0f)).kz = M ^^^ 0x0f := by decide +kernel
example : transfer2 .shl (exact 256) unknown = exact 0 := by decide +kernel
example : transfer2 .sar (exact 300) ⟨0, signBit⟩ = exact M := by decide +kernel
example : transfer2 .eq ⟨1, 0⟩ ⟨0, 1⟩ = exactBool false := by decide +kernel
example : transfer2 .lt (exact 3) (exact 5) = exactBool true := by decide +kernel
example : transfer1 .isZero ⟨0, 4⟩ = exactBool false := by decide +kernel
example : transfer2 .signextend (exact 0) ⟨0, 0x80⟩ = ⟨0, M ^^^ 0x7f⟩ := by decide +kernel
-- The direction of a fact check: a weaker claim passes, a stronger one does not.
example : KB.le ⟨M ^^^ 0xffff, 0⟩ (transfer2 .shr (exact 248) unknown) = true := by decide +kernel
example : KB.le ⟨M ^^^ 0x7f, 0⟩ (transfer2 .shr (exact 248) unknown) = false := by
  decide +kernel
example : meet (exact 4) (exact 6) = ⟨M ^^^ 6, 4⟩ := by decide +kernel

/-! ## Identities -/

-- I5 (design §4.5's example): `and v 255 → v` when `v`'s top bits are known zero.
example : checkI low8 (.op2 .and x (n 255)) x = true := by decide +kernel
example : checkI low8 (.op2 .and (n 255) x) x = true := by decide +kernel
example : checkI none' (.op2 .and x (n 255)) x = false := by decide +kernel
example : checkI low8 (.op2 .and x (n 127)) x = false := by decide +kernel
example : checkI none' (.op2 .add (n 0) x) x = true := by decide +kernel
example : checkI none' (.op2 .sub x x) (n 0) = true := by decide +kernel
example : checkI none' (.op2 .sub x y) (n 0) = false := by decide +kernel
example : checkI none' (.op2 .or x (n M)) (n M) = true := by decide +kernel
example : checkI none' (.op2 .sdiv x (n 1)) x = true := by decide +kernel
example : checkI none' (.op2 .smod x (n 1)) (n 0) = true := by decide +kernel
example : checkI none' (.op2 .eq x x) (n 1) = true := by decide +kernel
example : checkI low8 (.op2 .eq x (n 256)) (n 0) = true := by decide +kernel
example : checkI none' (.op2 .gt (n 0) x) (n 0) = true := by decide +kernel
example : checkI none' (.op2 .lt (n 0) x) (n 0) = false := by decide +kernel
example : checkI none' (.op2 .shr (n 256) x) (n 0) = true := by decide +kernel
example : checkI none' (.op2 .sar (n 256) x) (n 0) = false := by decide +kernel
example : checkI none' (.op2 .signextend (n 31) x) x = true := by decide +kernel
example : checkI none' (.op2 .signextend (n 0) x) x = false := by decide +kernel
example : checkI low8 (.op2 .signextend (n 1) x) x = true := by decide +kernel
example : checkI none' (.op2 .exp x (n 0)) (n 1) = true := by decide +kernel
example : checkI none' (.op2 .exp (n 0) x) (n 0) = false := by decide +kernel
example : checkI none' (.op2 .exp (n 0) (n 3)) (n 0) = true := by decide +kernel
example : checkI none' (.op1 .not (.op1 .not x)) x = true := by decide +kernel
-- `evm_add_mod`, `evm_mul_mod` by zero (review H-7).
example : checkI none' (.op3 .addmod x y (n 0)) (n 0) = true := by decide +kernel
example : checkI none' (.op3 .mulmod x y (n 0)) (n 0) = true := by decide +kernel
-- I15 `undo_inverse_shift`: accepted below 256 with the dropped bits known zero.
example : checkI low8 (.op2 .shr (n 8) (.op2 .shl (n 8) x)) x = true := by decide +kernel
example : checkI none' (.op2 .shr (n 8) (.op2 .shl (n 8) x)) x = false := by decide +kernel
-- H-7: `shr 256 (shl 256 x) → x` is wrong (it is 0) and is rejected even with every bit of `x`
-- but bit 0 known zero.
example : checkI (fun _ => ⟨M ^^^ 1, 0⟩) (.op2 .shr (n 256) (.op2 .shl (n 256) x)) x = false := by
  decide +kernel
example : (Term.op2 .shr (n 256) (.op2 .shl (n 256) x)).eval (fun _ => 1) ≠
    x.eval (fun _ => 1) := by decide +kernel

/-! ## `scalar_canonicalize` -/

-- S1: `and (and x y) (or y x) → and x y`.
example : checkS none' (.op2 .and (.op2 .and x y) (.op2 .or y x)) (.op2 .and x y) = true := by
  decide +kernel
example : checkS none' (.op2 .xor (.op2 .or x y) (.op2 .xor x y)) (.op2 .and y x) = true := by
  decide +kernel
example : checkS none' (.op2 .and (.op2 .and x y) (.op2 .and x y)) (.op2 .and x y) = false := by
  decide +kernel
-- S2, S3.
example : checkS none' (.op2 .shr (n 248) x) (.op2 .byte (n 0) x) = true := by decide +kernel
example : checkS none' (.op2 .and (.op2 .shr (n 8) x) (n 255)) (.op2 .byte (n 30) x) = true := by
  decide +kernel
example : checkS none' (.op2 .and (n 255) (.op2 .shr (n 248) x)) (.op2 .byte (n 0) x) = true := by
  decide +kernel
-- H-7 counterexamples for S3: `c = 4` (`31 - 4 / 8 = 31` reads bits 0–7, not 4–11) and
-- `c = 256` (`31 - 256 / 8` is 0 in `Nat`, the top byte, not 0) are rejected; both differ.
example : checkS none' (.op2 .and (.op2 .shr (n 4) x) (n 255)) (.op2 .byte (n 31) x) = false := by
  decide +kernel
example : (Term.op2 .and (.op2 .shr (n 4) x) (n 255)).eval (fun _ => 0xff0) ≠
    (Term.op2 .byte (n 31) x).eval (fun _ => 0xff0) := by decide +kernel
example : checkS none' (.op2 .and (.op2 .shr (n 256) x) (n 255)) (.op2 .byte (n 0) x) = false := by
  decide +kernel
example : (Term.op2 .and (.op2 .shr (n 256) x) (n 255)).eval (fun _ => M) ≠
    (Term.op2 .byte (n 0) x).eval (fun _ => M) := by decide +kernel
-- S4, and its H-7 counterexamples `c = 4` and `c = 256`.
example : checkS none' (.op2 .sar (n 248) (.op2 .shl (n 248) x)) (.op2 .signextend (n 0) x) = true := by
  decide +kernel
example : checkS none' (.op2 .sar (n 4) (.op2 .shl (n 4) x)) (.op2 .signextend (n 31) x) = false := by
  decide +kernel
example : (Term.op2 .sar (n 4) (.op2 .shl (n 4) x)).eval (fun _ => 2 ^ 251) ≠
    (Term.op2 .signextend (n 31) x).eval (fun _ => 2 ^ 251) := by decide +kernel
example : checkS none' (.op2 .sar (n 256) (.op2 .shl (n 256) x)) (.op2 .signextend (n 0) x) = false := by
  decide +kernel
example : (Term.op2 .sar (n 256) (.op2 .shl (n 256) x)).eval (fun _ => 0x80) ≠
    (Term.op2 .signextend (n 0) x).eval (fun _ => 0x80) := by decide +kernel
-- S5–S8: `eq (add x 3) 10 → eq x 7`; `sub x c` and `sub c x` move the constant differently.
example : checkS none' (.op2 .eq (.op2 .add x (n 3)) (n 10)) (.op2 .eq x (n 7)) = true := by
  decide +kernel
example : checkS none' (.op2 .eq (n 10) (.op2 .add (n 3) x)) (.op2 .eq x (n 7)) = true := by
  decide +kernel
example : checkS none' (.op2 .eq (.op2 .sub x (n 3)) (n 10)) (.op2 .eq x (n 13)) = true := by
  decide +kernel
example : checkS none' (.op2 .eq (.op2 .sub (n 3) x) (n 10)) (.op2 .eq x (n (W - 7))) = true := by
  decide +kernel
example : checkS none' (.op2 .eq (.op2 .sub (n 3) x) (n 10)) (.op2 .eq x (n 13)) = false := by
  decide +kernel
example : checkS none' (.op1 .isZero (.op2 .add x (n 3))) (.op2 .eq x (n (W - 3))) = true := by
  decide +kernel
example : checkS none' (.op1 .isZero (.op2 .xor x (n 3))) (.op2 .eq x (n 3)) = true := by
  decide +kernel
-- S9, S11.
example : checkS none' (.op2 .eq (n 0) x) (.op1 .isZero x) = true := by decide +kernel
example : checkS none' (.op2 .mul x (n 8)) (.op2 .shl (n 3) x) = true := by decide +kernel
example : checkS none' (.op2 .mul x (n 1)) (.op2 .shl (n 0) x) = false := by decide +kernel
-- S12: `sar` totals stop at 255, `shl` at 256.
example : checkS none' (.op2 .sar (n 200) (.op2 .sar (n 100) x)) (.op2 .sar (n 255) x) = true := by
  decide +kernel
example : checkS none' (.op2 .shl (n 200) (.op2 .shl (n 300) x)) (.op2 .shl (n 256) x) = true := by
  decide +kernel
example : checkS none' (.op2 .shl (n 200) (.op2 .shr (n 100) x)) (.op2 .shl (n 300) x) = false := by
  decide +kernel
-- S13 needs the product to fit.
example : checkS none' (.op2 .udiv (.op2 .udiv x (n 3)) (n 5)) (.op2 .udiv x (n 15)) = true := by
  decide +kernel
example : checkS none' (.op2 .udiv (.op2 .udiv x (n (2 ^ 200 + 1))) (n (2 ^ 100 + 1)))
    (.op2 .udiv x (n ((2 ^ 200 + 1) * (2 ^ 100 + 1) % W))) = false := by decide +kernel
-- S14, S15, and H-7's `k = 256`: the divisor `2 ^ 256` is the word 0, and `umod x 0` is 0.
example : checkS none' (.op2 .udiv x (n 256)) (.op2 .shr (n 8) x) = true := by decide +kernel
example : checkS none' (.op2 .umod x (n 256)) (.op2 .and x (n 255)) = true := by decide +kernel
example : checkS none' (.op2 .umod x (n (2 ^ 256))) (.op2 .and x (n M)) = false := by
  decide +kernel
example : (Term.op2 .umod x (n (2 ^ 256))).eval (fun _ => 5) ≠
    (Term.op2 .and x (n M)).eval (fun _ => 5) := by decide +kernel

/-! ## GVN -/

example : checkG none' (.op2 .sub (.op2 .add x y) y) x = true := by decide +kernel
example : checkG none' (.op2 .sub (.op2 .add x y) x) y = true := by decide +kernel
example : checkG none' (.op2 .add y (.op2 .sub x y)) x = true := by decide +kernel
example : checkG none' (.op2 .add (.op2 .sub x y) x) x = false := by decide +kernel
example : checkG none' (.op2 .mul (n 16) x) (.op2 .shl (n 4) x) = true := by decide +kernel

/-! ## Branches -/

-- `br (is_zero (is_zero c))` is `br c`; `br (is_zero c)` is `br c` with the targets swapped.
example : checkBranch none' (.op1 .isZero (.op1 .isZero x)) x false = true := by decide +kernel
example : checkBranch none' (.op1 .isZero x) x true = true := by decide +kernel
example : checkBranch none' (.op1 .isZero x) x false = false := by decide +kernel
-- B2: `eq v 0` is `is_zero v`, no swap; B3: `gt v 0` is its negation.
example : checkBranch none' (.op2 .eq x (n 0)) (.op1 .isZero x) false = true := by decide +kernel
example : checkBranch none' (.op2 .gt x (n 0)) (.op1 .isZero x) true = true := by decide +kernel
example : checkBranch none' (.op2 .lt (n 0) x) (.op1 .isZero x) true = true := by decide +kernel
example : checkBranch none' (.op1 .isZero (.op2 .gt x (n 0))) (.op1 .isZero x) false = true := by
  decide +kernel
example : checkBranch none' (.op2 .gt x (n 0)) (.op1 .isZero x) false = false := by decide +kernel

/-! ## Demanded bits -/

example : demand2 .shl (some 8) 0xff00 = (M, 0xff) := by decide +kernel
example : demand2 .shl (some 300) 0xff00 = (M, 0) := by decide +kernel
example : demand2 .shr (some 8) 0xff = (M, 0xff00) := by decide +kernel
example : demand2 .sar (some 8) (2 ^ 250) = (M, signBit) := by decide +kernel
example : demand2 .signextend (some 0) 0x100 = (0, 0x80) := by decide +kernel
example : demand2 .add none 1 = (M, M) := by decide +kernel
example : demand2 .add none 0 = (0, 0) := by decide +kernel
example : demand1 .not 0xf0 = 0xf0 := by decide +kernel
-- D1–D3 in both orders: only the low byte is read, and `y`'s low byte is known one (`and`) or
-- zero (`or`, `xor`).
example : checkD (fun v => if v = 1 then ⟨0, 0xff⟩ else unknown) 0xff (.op2 .and y x) x = true := by
  decide +kernel
example : checkD (fun v => if v = 1 then ⟨0xff, 0⟩ else unknown) 0xff (.op2 .or x y) x = true := by
  decide +kernel
example : checkD (fun v => if v = 1 then ⟨0xff, 0⟩ else unknown) 0xff (.op2 .xor y x) x = true := by
  decide +kernel
example : checkD (fun v => if v = 1 then ⟨0xff, 0⟩ else unknown) 0x1ff (.op2 .or x y) x = false := by
  decide +kernel


/-! ## Review 9: cases rejected before, accepted now -/

-- Finding 3: GVN replaces whichever of `eq x 0` / `is_zero x`, `mul x 2^k` / `shl k x` comes
-- later by the one that dominates.
example : checkG none' (.op1 .isZero x) (.op2 .eq x (n 0)) = true := by decide +kernel
example : checkG none' (.op2 .shl (n 3) x) (.op2 .mul x (n 8)) = true := by decide +kernel
-- Finding 3: commutative operands canonicalized by rank.
example : checkExact none' (.op2 .add y x) (.op2 .add x y) = true := by decide +kernel
example : checkExact none' (.op2 .mul y x) (.op2 .mul x y) = true := by decide +kernel
example : checkExact none' (.op2 .and y x) (.op2 .and x y) = true := by decide +kernel
example : checkExact none' (.op2 .or y x) (.op2 .or x y) = true := by decide +kernel
example : checkExact none' (.op2 .xor y x) (.op2 .xor x y) = true := by decide +kernel
example : checkExact none' (.op2 .eq x (n 0)) (.op2 .eq (n 0) x) = true := by decide +kernel
example : checkExact none' (.op2 .mul x (n 8)) (.op2 .mul (n 8) x) = true := by decide +kernel
example : checkExact none' (.op2 .sub y x) (.op2 .sub x y) = false := by decide +kernel
-- Commutative equality inside a schema: G2 with `c` a commuted copy of `b`.
example : checkExact none' (.op2 .sub (.op2 .add x (.op2 .and y x)) (.op2 .and x y)) x = true := by
  decide +kernel
example : Term.commEq (.op2 .add (.op2 .xor y x) (n 1)) (.op2 .add (n 1) (.op2 .xor x y)) = true := by
  decide +kernel
-- Finding 6: `branch_conditions` strips one `is_zero`; composed zero compares.
example : checkBranch none' (.op1 .isZero (.op1 .isZero x)) (.op1 .isZero x) true = true := by
  decide +kernel
example : checkBranch none' (.op2 .eq x (n 0)) x true = true := by decide +kernel
example : checkBranch none' (.op2 .gt x (n 0)) x false = true := by decide +kernel
example : checkBranch none' (.op2 .gt x (n 0)) x true = false := by decide +kernel
example : checkBranchOn none' (.op2 .eq (n 0) (.op2 .xor y x)) (.op1 .isZero (.op2 .xor x y)) false
    = true := by decide +kernel
-- Finding 8: `fold_constant_comparison`'s output with its operands in the other order.
example : checkS none' (.op2 .eq (.op2 .add x (n 3)) (n 10)) (.op2 .eq (n 7) x) = true := by
  decide +kernel
-- Finding 4: each round of `ScalarCanonicalize::run` is its own step: `eq (xor x 1) 1` becomes
-- `eq x 0` in one round (the Rust emits `eq`, never `is_zero`, from
-- `fold_constant_comparison`), then `is_zero x` in the next.
example : checkExact none' (.op2 .eq (.op2 .xor x (n 1)) (n 1)) (.op2 .eq x (n 0)) = true := by
  decide +kernel
example : checkExact none' (.op2 .eq x (n 0)) (.op1 .isZero x) = true := by decide +kernel
example : checkExact none' (.op2 .udiv x (n (2 ^ 248))) (.op2 .shr (n 248) x) = true := by
  decide +kernel
example : checkExact none' (.op2 .shr (n 248) x) (.op2 .byte (n 0) x) = true := by decide +kernel

end Fe.Sonatina.Steps.Schemas.Tests

-- The axioms the library's lemmas use.
#print axioms Fe.Sonatina.Steps.Schemas.evalConst_sound
#print axioms Fe.Sonatina.Steps.Schemas.runInst_clz
#print axioms Fe.Sonatina.Steps.Schemas.transfer2_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkI_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkS_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkG_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkBranch_sound
#print axioms Fe.Sonatina.Steps.Schemas.demand2_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkD_sound
#print axioms Fe.Sonatina.Steps.Schemas.Term.fold_eval
#print axioms Fe.Sonatina.Steps.Schemas.checkExact_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkDemand_sound
#print axioms Fe.Sonatina.Steps.Schemas.checkBranchOn_target
#print axioms Fe.Sonatina.Steps.Schemas.factsOn_env
