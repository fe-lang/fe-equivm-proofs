import Fe.EVM.World

/-!
# Integer types

A Fe integer of any width is held in the model as a word in canonical form: below `2 ^ bits` if
its type is unsigned, sign-extended to 256 bits if signed.  An operation takes the integers its
operands denote, computes in `Int`, and gives back the canonical word of the result: `wrap` of it
for an operation that wraps, `checked` for one that panics when the type lacks the result.

`u256` operations keep their own definitions in `World.lean` (`checkedAdd` and the rest), which
the proofs written before this module use.
-/

namespace Fe.EVM

open Ethereum

/-- An integer type: unsigned or signed, of a width in bits. -/
inductive IntTy where
  | u (bits : Nat)
  | i (bits : Nat)
  deriving DecidableEq, Repr

namespace IntTy

/-- The width of the type. -/
def bits : IntTy → Nat
  | u b | i b => b

/-- The integer a canonical word denotes. -/
def val (t : IntTy) (w : UInt256) : Int :=
  match t with
  | u _ => w.toNat
  | i _ => if w.toNat < 2 ^ 255 then w.toNat else (w.toNat : Int) - 2 ^ 256

/-- The type has the integer `n`. -/
def Fits (t : IntTy) (n : Int) : Prop :=
  match t with
  | u b => 0 ≤ n ∧ n < 2 ^ b
  | i b => -(2 ^ (b - 1)) ≤ n ∧ n < 2 ^ (b - 1)

instance (t : IntTy) (n : Int) : Decidable (t.Fits n) := by
  unfold Fits; split <;> infer_instance

/-- The canonical word of the value of the type congruent to `n` modulo `2 ^ bits`. -/
def wrap (t : IntTy) (n : Int) : UInt256 :=
  match t with
  | u b => UInt256.ofNat (n % 2 ^ b).toNat
  | i b =>
    let m := n % 2 ^ b
    UInt256.ofNat ((if m < 2 ^ (b - 1) then m else m - 2 ^ b) % 2 ^ 256).toNat

/-- The value `n`, or `Panic(0x11)` if the type lacks it. -/
def checked (t : IntTy) (n : Int) : FeM UInt256 :=
  if t.Fits n then pure (t.wrap n) else Fe.M.panic 0x11

/-- The value nearest `n`. -/
def clamp (t : IntTy) (n : Int) : UInt256 :=
  match t with
  | u b => t.wrap (max 0 (min n (2 ^ b - 1)))
  | i b => t.wrap (max (-(2 ^ (b - 1))) (min n (2 ^ (b - 1) - 1)))

/-! ## Arithmetic

Checked forms run in the model monad; wrapping forms are pure, except division, which panics on
a zero divisor either way. -/

def add (t : IntTy) (a b : UInt256) : FeM UInt256 := t.checked (t.val a + t.val b)
def addW (t : IntTy) (a b : UInt256) : UInt256 := t.wrap (t.val a + t.val b)
def sub (t : IntTy) (a b : UInt256) : FeM UInt256 := t.checked (t.val a - t.val b)
def subW (t : IntTy) (a b : UInt256) : UInt256 := t.wrap (t.val a - t.val b)
def mul (t : IntTy) (a b : UInt256) : FeM UInt256 := t.checked (t.val a * t.val b)
def mulW (t : IntTy) (a b : UInt256) : UInt256 := t.wrap (t.val a * t.val b)

/-- Division rounds toward zero.  A zero divisor is `Panic(0x12)`; only a signed `MIN / -1`
    overflows. -/
def div (t : IntTy) (a b : UInt256) : FeM UInt256 :=
  if t.val b = 0 then Fe.M.panic 0x12 else t.checked ((t.val a).tdiv (t.val b))

def divW (t : IntTy) (a b : UInt256) : FeM UInt256 :=
  if t.val b = 0 then Fe.M.panic 0x12 else pure (t.wrap ((t.val a).tdiv (t.val b)))

/-- The remainder has the dividend's sign and never overflows. -/
def rem (t : IntTy) (a b : UInt256) : FeM UInt256 :=
  if t.val b = 0 then Fe.M.panic 0x12 else pure (t.wrap ((t.val a).tmod (t.val b)))

/-- Checked power: a negative exponent reverts with no data, and a result the type lacks is
    `Panic(0x11)`.  From exponent 256 on only the powers of `0`, `1` and `-1` fit any type. -/
def pow (t : IntTy) (a b : UInt256) : FeM UInt256 :=
  let x := t.val a
  let e := t.val b
  if e < 0 then Fe.M.revert ByteArray.empty
  else if e < 256 then t.checked (x ^ e.toNat)
  else if x = 0 ∨ x = 1 then pure a
  else if x = -1 then pure (t.wrap (if e % 2 = 0 then 1 else -1))
  else Fe.M.panic 0x11

/-- Wrapping power: the EVM's `EXP`, cut to the type.  The exponent is its bit pattern at the
    type's width, read unsigned. -/
def powW (t : IntTy) (a b : UInt256) : UInt256 :=
  t.wrap (UInt256.exp a (UInt256.ofNat (b.toNat % 2 ^ t.bits))).toNat

def neg (t : IntTy) (a : UInt256) : FeM UInt256 := t.checked (-(t.val a))
def negW (t : IntTy) (a : UInt256) : UInt256 := t.wrap (-(t.val a))

/-- Every bit inverted: `-a - 1` in two's complement. -/
def not (t : IntTy) (a : UInt256) : UInt256 := t.wrap (-(t.val a) - 1)

/-- A left shift drops the bits that leave the type. -/
def shl (t : IntTy) (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then UInt256.ofNat 0 else t.wrap (t.val a * 2 ^ b.toNat)

/-- A right shift rounds down: logical if unsigned, arithmetic if signed. -/
def shr (t : IntTy) (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then (if t.val a < 0 then t.wrap (-1) else UInt256.ofNat 0)
  else t.wrap ((t.val a).fdiv (2 ^ b.toNat))

def satAdd (t : IntTy) (a b : UInt256) : UInt256 := t.clamp (t.val a + t.val b)
def satSub (t : IntTy) (a b : UInt256) : UInt256 := t.clamp (t.val a - t.val b)
def satMul (t : IntTy) (a b : UInt256) : UInt256 := t.clamp (t.val a * t.val b)

def lt (t : IntTy) (a b : UInt256) : Bool := decide (t.val a < t.val b)
def le (t : IntTy) (a b : UInt256) : Bool := decide (t.val a ≤ t.val b)

/-- The value of type `t` cast to type `target`: kept if `target` has it, wrapped otherwise. -/
def cast (t target : IntTy) (a : UInt256) : UInt256 := target.wrap (t.val a)

/-! ## Bits -/

/-- The bit pattern of a canonical word at the type's width. -/
def pattern (t : IntTy) (a : UInt256) : Nat := a.toNat % 2 ^ t.bits

/-- The number of zero bits above the highest set bit, the width for zero. -/
def leadingZeros (t : IntTy) (a : UInt256) : UInt256 :=
  UInt256.ofNat
    ((List.range t.bits).takeWhile fun n => !(t.pattern a).testBit (t.bits - 1 - n)).length

/-- The number of zero bits below the lowest set bit, the width for zero. -/
def trailingZeros (t : IntTy) (a : UInt256) : UInt256 :=
  UInt256.ofNat ((List.range t.bits).takeWhile fun n => !(t.pattern a).testBit n).length

/-- The value whose bytes are those of `a` in reverse order. -/
def swapBytes (t : IntTy) (a : UInt256) : UInt256 :=
  let bytes := t.bits / 8
  t.wrap ((List.range bytes).foldl
    (fun acc n => acc * 256 + ((t.pattern a / 256 ^ n % 256 : Nat) : Int)) 0)

end IntTy

end Fe.EVM
