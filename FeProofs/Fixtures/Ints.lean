import FeProofs.Fixtures.Exported

/-!
# Integer types against the EVM

`Fe/EVM/Int.lean` defines integer operations by their meaning in `Int`.  This file checks them
against EVMLean's opcodes on a grid of boundary words, and checks what the exported `ints`
fixture does on a few inputs.  The checks are evaluations, not proofs for every word.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.Fixtures.Ints

/-- Boundary words: small values, the edges of 8, 32 and 255 bits, and negatives. -/
def samples : List UInt256 :=
  [0, 1, 2, 3, 7, 8, 127, 128, 129, 255, 256, 257, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32,
    123456789012345678901234567890, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 1, 2 ^ 256 - 129,
    2 ^ 256 - 128, 2 ^ 256 - 3, 2 ^ 256 - 2, 2 ^ 256 - 1].map UInt256.ofNat

/-- Shift amounts and exponents. -/
def small : List UInt256 := [0, 1, 2, 7, 8, 31, 32, 255, 256, 257, 2 ^ 255].map UInt256.ofNat

def pairs (f : UInt256 → UInt256 → Bool) : Bool := samples.all fun a => samples.all (f a)

/-- The result of a model computation that reads neither the environment nor the world. -/
def run (m : FeM UInt256) : Option UInt256 :=
  match m.exec default (World.init default default) with
  | some (.ok (v, _)) => some v
  | _ => none

/-! ## 256-bit operations are the EVM's -/

theorem addW_u256 : pairs (fun a b => IntTy.addW (.u 256) a b == a + b) = true := by
  native_decide
theorem subW_i256 : pairs (fun a b => IntTy.subW (.i 256) a b == a - b) = true := by
  native_decide
theorem mulW_i256 : pairs (fun a b => IntTy.mulW (.i 256) a b == a * b) = true := by
  native_decide

theorem divW_i256 : pairs (fun a b =>
    b == UInt256.ofNat 0 || run (IntTy.divW (.i 256) a b) == some (UInt256.sdiv a b)) = true := by
  native_decide

theorem rem_i256 : pairs (fun a b =>
    b == UInt256.ofNat 0 || run (IntTy.rem (.i 256) a b) == some (UInt256.smod a b)) = true := by
  native_decide

theorem lt_i256 : pairs (fun a b => IntTy.lt (.i 256) a b == UInt256.sltBool a b) = true := by
  native_decide

theorem not_i256 : samples.all (fun a => IntTy.not (.i 256) a == ~~~a) = true := by
  native_decide

theorem shl_u256 :
    samples.all (fun a => small.all fun b => IntTy.shl (.u 256) a b == a <<< b) = true := by
  native_decide

theorem shr_u256 :
    samples.all (fun a => small.all fun b => IntTy.shr (.u 256) a b == a >>> b) = true := by
  native_decide

theorem shr_i256 :
    samples.all (fun a => small.all fun b => IntTy.shr (.i 256) a b == UInt256.sar b a) = true := by
  native_decide

theorem powW_u256 :
    samples.all (fun a => small.all fun b => IntTy.powW (.u 256) a b == UInt256.exp a b) = true := by
  native_decide

/-! ## Narrow types are the EVM's operations, then cut or sign-extended -/

/-- A cast to `i8` is `SIGNEXTEND` from byte 0, and one to `i32` from byte 3. -/
theorem cast_i8 : samples.all (fun a =>
    IntTy.cast (.u 256) (.i 8) a == UInt256.signextend (UInt256.ofNat 0) a) = true := by
  native_decide
theorem cast_i32 : samples.all (fun a =>
    IntTy.cast (.u 256) (.i 32) a == UInt256.signextend (UInt256.ofNat 3) a) = true := by
  native_decide

/-- A cast to `u8` keeps the low byte. -/
theorem cast_u8 : samples.all (fun a =>
    IntTy.cast (.u 256) (.u 8) a == a &&& UInt256.ofNat 255) = true := by
  native_decide

/-- Wrapping `i32` multiplication is `MUL`, sign-extended from byte 3. -/
theorem mulW_i32 : pairs (fun a b =>
    let a := IntTy.cast (.u 256) (.i 32) a
    let b := IntTy.cast (.u 256) (.i 32) b
    IntTy.mulW (.i 32) a b == UInt256.signextend (UInt256.ofNat 3) (a * b)) = true := by
  native_decide

/-- Checked `u8` addition panics exactly when the sum leaves the byte. -/
theorem add_u8 : pairs (fun a b =>
    let a := a &&& UInt256.ofNat 255
    let b := b &&& UInt256.ofNat 255
    run (IntTy.add (.u 8) a b) == if a.toNat + b.toNat < 256 then some (a + b) else none) = true := by
  native_decide

/-- The canonical word of a negative constant. -/
theorem wrap_neg : IntTy.wrap (.i 256) (-5) = UInt256.ofNat (2 ^ 256 - 5) := by native_decide

/-! ## The exported fixture -/

/-- `narrow(200, 100)`: the `u8` sum overflows. -/
theorem narrow_overflow (I : ExecutionEnv) (w : World) :
    (recv_Narrow (UInt256.ofNat 200) (UInt256.ofNat 100)).exec I w =
      some (.error (.panic 0x11)) := by
  have h200 : (UInt256.ofNat 200).toNat = 200 := rfl
  have h100 : (UInt256.ofNat 100).toNat = 100 := rfl
  simp [recv_Narrow, IntTy.add, IntTy.checked, IntTy.Fits, IntTy.val, h200, h100]

/-- `signed(3, 7)` is `-3`. -/
theorem signed_neg (I : ExecutionEnv) (w : World) :
    (recv_Signed (UInt256.ofNat 3) (UInt256.ofNat 7)).exec I w =
      some (.ok (UInt256.ofNat (2 ^ 256 - 3), w)) := by
  have hlt : UInt256.sltBool (UInt256.ofNat 3) (UInt256.ofNat 7) = true := by decide
  have h3 : (UInt256.ofNat 3).toNat = 3 := rfl
  have hw : IntTy.wrap (.i 32) (-3) = UInt256.ofNat (2 ^ 256 - 3) := by native_decide
  simp [recv_Signed, hlt, IntTy.neg, IntTy.checked, IntTy.Fits, IntTy.val, h3, hw]

end FeProofs.Fixtures.Ints
