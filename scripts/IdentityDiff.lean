import FeProofs.Precompiles.Exported.Identity
import Fe.EVM.Diff

/-!
# IDENTITY: the exported model against EVMLean

Runs the exported model of the contract `Identity` of `FeProofs/Precompiles` (fevm's `copied`
behind a fallback arm) on call data, and EVMLean's IDENTITY, `Ξ_ID`, on the same bytes: the model
must return what `Ξ_ID` outputs, which is the input.  The inputs are generated, of lengths around
the lanes of eight bytes the copy moves at a time and others up to 300 bytes.

`lake env lean scripts/IdentityDiff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace IdentityDiff

/-- What the model does on call data `d`: the bytes it returns, or how it ends otherwise. -/
def model (d : ByteArray) : Except String ByteArray :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Identity.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok out
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_ID` on call data `d`, with enough gas. -/
def spec (d : ByteArray) : ByteArray :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  (Ξ_ID default ⟨100000⟩ default I).2.2.2

abbrev Gen := StateM StdGen

def below (k : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (k - 1)

/-- Bytes of a length near a multiple of eight, or of any up to 300. -/
def input : Gen ByteArray := do
  let near : List Nat := [0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 33, 64]
  let len ← do if (← below 2) == 0 then pure near[← below near.length]! else below 301
  let mut b := ByteArray.empty
  for _ in [:len] do b := b.push (UInt8.ofNat (← below 256))
  return b

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  for seed in [:200] do
    let d := input.run' (mkStdGen seed)
    let s := spec d
    if s != d then
      disagree := disagree + 1
      IO.println s!"DISAGREE {Ethereum.toHex d}: EVMLean {Ethereum.toHex s}"
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {Ethereum.toHex d}: model {Ethereum.toHex m}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {Ethereum.toHex d}: the model {how}"
  IO.println s!"IDENTITY: 200 generated inputs; {agree} agree, {disagree} disagree"

end IdentityDiff

#eval IdentityDiff.main
