import FeProofs.Precompiles.Exported.Modexp
import Fe.EVM.Diff

/-!
# MODEXP: the exported model against EVMLean

Runs the exported model of the contract `Modexp` of `FeProofs/Precompiles` (fevm's `modexp::run`
behind a fallback arm, given all the gas a `u64` holds) on call data, and EVMLean's MODEXP,
`Ξ_EXPMOD`, with enough gas, on the same bytes: the model must return what `Ξ_EXPMOD` outputs.
The inputs are generated where EVMLean is right: EVMLean reduces the base modulo `2 ^ 256`, so
bases are shorter than 32 bytes, and it has no bound on the lengths, which fevm caps at 1,024
bytes (EIP-7823), so lengths are at most that.  They have zero lengths, a zero modulus, even and
odd moduli of one to a few limbs, sizes that are not multiples of 8, exponents with leading zero
bytes, and lengths longer than the input that follows them.  `scripts/ModexpVectors.lean` tests
the model on go-ethereum's vectors with wide bases.

`lake env lean scripts/ModexpDiff.lean` prints a line per disagreement and a total.
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

/-- A length of up to `most` bytes: zero, one, a multiple of 8 or one off it, or any. -/
def length (most : Nat) : Gen Nat := do
  match ← below 6 with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => return min most (8 * (← below 5))
  | 3 => return min most (8 * (← below 5) + 1)
  | 4 => return min most (8 * (← below 5) + 7)
  | _ => return (← below (most + 1))

/-- One generated input. -/
def input : Gen (String × ByteArray) := do
  let baseLen ← length 31
  let expLen ← length 40
  let modLen ← length 40
  let base ← bytes baseLen
  let mut exp ← bytes expLen
  let mut kind := "random"
  if expLen > 2 && (← below 3) == 0 then
    exp := ByteArray.mk (Array.replicate 2 0) ++ exp.extract 2 expLen
    kind := "exponent with leading zeros"
  let mut modulus ← bytes modLen
  match ← below 6 with
  | 0 =>
    modulus := ByteArray.mk (Array.replicate modLen 0)
    kind := "zero modulus"
  | 1 =>
    if modLen > 0 then
      modulus := modulus.set! (modLen - 1) (modulus.get! (modLen - 1) &&& 0xfe)
      kind := "even modulus"
  | _ => pure ()
  let d := word baseLen ++ word expLen ++ word modLen ++ base ++ exp ++ modulus
  let cut ← below 8
  let len ← below d.size
  match cut with
  | 0 => return ("longer than the input", d.extract 0 len)
  | _ => return (if baseLen == 0 || expLen == 0 || modLen == 0 then "zero length" else kind, d)

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut kinds : List (String × Nat) := []
  let mut gen := mkStdGen 1
  for _ in [:200] do
    let ((kind, d), next) := input.run gen
    gen := next
    kinds := match kinds.lookup kind with
      | some k => (kind, k + 1) :: kinds.filter (·.1 != kind)
      | none => (kind, 1) :: kinds
    let s := spec d
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: model {show? m}, EVMLean {show? s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: the model {how}"
  let counts := ", ".intercalate (kinds.reverse.map fun (k, c) => s!"{k} {c}")
  IO.println s!"MODEXP: 200 generated inputs ({counts}); {agree} agree, {disagree} disagree"

end ModexpDiff

#eval ModexpDiff.main
