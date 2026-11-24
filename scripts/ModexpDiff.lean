import FeProofs.Precompiles.Exported.Modexp
import Fe.EVM.Diff

/-!
# MODEXP: the exported model against EVMLean

Runs the exported model of the contract `Modexp` of `FeProofs/Precompiles` (fevm's `modexp::run`
behind a fallback arm, given all the gas a `u64` holds) on call data, and EVMLean's MODEXP,
`Ξ_EXPMOD`, with enough gas, on the same bytes: the model must return what `Ξ_EXPMOD` outputs.
The inputs have wide and narrow bases, bases longer than the modulus, zero lengths, zero and one
moduli, odd moduli of one to many limbs, even moduli with few and many trailing zero bits,
powers of two, zero exponents and exponents with leading zero bytes, lengths that are not
multiples of 8 or 32, and call data shorter or longer than the lengths ask for.  Each length is
at most 1,024 bytes, the bound of EIP-7823 that fevm implements; EVMLean has no bound, so above
it the two differ by design, and there the model is only checked to fail.  Moduli at the bound
have exponents of at most 3 bytes, since the model runs slowly there in the interpreter.
`scripts/ModexpVectors.lean` tests the model on go-ethereum's vectors.

`lake lean scripts/ModexpDiff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace ModexpDiff

/-- What the model does on call data `d`: the bytes it returns, or `none` where it reverts
    without data; or how it ends otherwise. -/
def model (d : ByteArray) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Modexp.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok (some out)
  | some (.error (.revert data)) =>
    if data.isEmpty then .ok none else .error s!"reverts with {Ethereum.toHex data}"
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_EXPMOD` on call data `d`: its output, or `none` where it fails (an empty account map). -/
def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_EXPMOD σ ⟨2 ^ 64⟩ default I
  if σ' == ∅ then none else some o

def show? : Option ByteArray → String
  | some o => Ethereum.toHex o
  | none => "failure"

abbrev Gen := StateM StdGen

def below (k : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (k - 1)

def word (k : Nat) : ByteArray := (UInt256.ofNat k).toByteArray

def bytes (len : Nat) : Gen ByteArray := do
  let mut b := ByteArray.empty
  for _ in [:len] do b := b.push (UInt8.ofNat (← below 256))
  return b

def zeros (len : Nat) : ByteArray := ByteArray.mk (Array.replicate len 0)

/-- A length of up to `most` bytes: zero, one, a multiple of 8 or 32 or one off it, or any. -/
def length (most : Nat) : Gen Nat := do
  let k ← match ← below 8 with
    | 0 => pure 0
    | 1 => pure 1
    | 2 => return 8 * (← below 9)
    | 3 => return 8 * (← below 9) + 1
    | 4 => return 8 * (← below 9) + 7
    | 5 => return 32 * (← below 4) + 31
    | 6 => return 32 * (← below 4) + 33
    | _ => below (most + 1)
  return min most k

/-- A modulus of `len` bytes, and what kind it is. -/
def modulus (len : Nat) : Gen (ByteArray × String) := do
  let m ← bytes len
  if len == 0 then return (m, "random modulus")
  match ← below 10 with
  | 0 => return (zeros len, "zero modulus")
  | 1 => return (zeros (len - 1) |>.push 1, "modulus one")
  | 2 => return (m.set! (len - 1) (m.get! (len - 1) &&& 0xfe), "even modulus")
  | 3 =>
    -- Many trailing zero bits: the low limbs of 2 ^ k are zero.
    let z ← below (len + 1)
    return (m.extract 0 (len - z) ++ zeros z, "even modulus, many low zeros")
  | 4 =>
    let pos ← below len
    let bit ← below 8
    return ((zeros len).set! pos (UInt8.ofNat (2 ^ bit)), "power of two modulus")
  | 5 | 6 => return (m.set! (len - 1) (m.get! (len - 1) ||| 1), "odd modulus")
  | _ => return (m, "random modulus")

/-- One generated input, with the features it has. -/
def input : Gen (List String × ByteArray) := do
  if (← below 16) == 0 then
    -- A length above the bound.
    let over := 1025 + (← below 2000)
    let huge := if (← below 2) == 0 then over else 2 ^ 256 - over
    let which ← below 3
    let lens := (List.range 3).map fun i => if i == which then huge else 8 * i
    let d := lens.foldl (fun d l => d ++ word l) ByteArray.empty ++ (← bytes (← below 100))
    return (["length above 1,024"], d)
  -- Wide bases more often than not: up to 200 bytes, or the bound.
  let baseLen ← match ← below 8 with
    | 0 => pure 1024
    | 1 | 2 => length 31
    | _ => length 200
  let modLen ← match ← below 12 with
    | 0 => pure 1024
    | 1 | 2 | 3 => length 32
    | _ => length 120
  -- A modulus at the bound takes the interpreter minutes a product: short exponents there.
  let expLen ← length (if modLen == 1024 then 3 else 48)
  let base ← if (← below 12) == 0 then pure (zeros baseLen) else bytes baseLen
  let mut exp ← bytes expLen
  let mut tags : List String := []
  match ← below 6 with
  | 0 =>
    exp := zeros expLen
    tags := ["zero exponent"]
  | 1 =>
    if expLen > 2 then
      exp := zeros 2 ++ exp.extract 2 expLen
      tags := ["exponent with leading zeros"]
  | _ => pure ()
  let (m, kind) ← modulus modLen
  tags := kind :: tags
  if baseLen > 32 then tags := "base wider than 32 bytes" :: tags
  if baseLen > modLen then tags := "base longer than the modulus" :: tags
  if modLen > 32 then tags := "modulus of more than four limbs" :: tags
  if baseLen == 0 || expLen == 0 || modLen == 0 then tags := "zero length" :: tags
  if [baseLen, expLen, modLen].any (· % 8 != 0) then tags := "length not a multiple of 8" :: tags
  let d := word baseLen ++ word expLen ++ word modLen ++ base ++ exp ++ m
  match ← below 8 with
  | 0 => return ("call data shorter than the lengths" :: tags, d.extract 0 (← below d.size))
  | 1 => return ("call data longer than the lengths" :: tags, d ++ (← bytes (1 + (← below 64))))
  | _ => return (tags, d)

/-- The limbs of `x > 0`. -/
def limbs (x : Nat) : Nat := Nat.log2 x / 64 + 1

/-- The way `modexp::run` takes on call data `d` within the bound, from the numbers the
    specification reads. -/
def path (d : ByteArray) : String :=
  let bl := nat_of_slice d 0 32
  let el := nat_of_slice d 32 32
  let ml := nat_of_slice d 64 32
  let m := nat_of_slice d (96 + bl + el) ml
  let e := nat_of_slice d (96 + bl) el
  let k := (List.range (8 * ml)).find? (fun i => m.testBit i) |>.getD 0
  let q := m >>> k
  if ml == 0 then "path: no output"
  else if m ≤ 1 then "path: modulus zero or one"
  else if e == 0 then "path: zero exponent"
  else if nat_of_slice d 96 bl == 0 then "path: zero base"
  else if m % 2 == 1 then
    if limbs m ≤ 4 then "path: odd modulus in registers"
    else if e == 2 then "path: odd modulus in memory, one squaring"
    else "path: odd modulus in memory"
  else if q == 1 then s!"path: power of two, {if (k + 63) / 64 ≤ 2 then "at most" else "more than"} two limbs"
  else s!"path: even modulus, odd part {if limbs q ≤ 4 then "in registers" else "in memory"}"

def main (count : Nat) : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut tally : List (String × Nat) := []
  let mut gen := mkStdGen 1
  for _ in [:count] do
    let ((tags, d), next) := input.run gen
    gen := next
    let tags := if tags.contains "length above 1,024" then tags else path d :: tags
    for tag in tags do
      tally := match tally.lookup tag with
        | some k => (tag, k + 1) :: tally.filter (·.1 != tag)
        | none => (tag, 1) :: tally
    let kind := ", ".intercalate tags
    -- Above the bound fevm fails (EIP-7823); EVMLean has no bound.
    let s := if tags.contains "length above 1,024" then none else spec d
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: model {show? m}, expected {show? s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: the model {how}"
  let counts := ", ".intercalate ((tally.toArray.qsort (·.1 < ·.1)).toList.map fun (k, c) => s!"{k} {c}")
  IO.println s!"MODEXP: {count} generated inputs ({counts}); {agree} agree, {disagree} disagree"

end ModexpDiff

#eval ModexpDiff.main 300
