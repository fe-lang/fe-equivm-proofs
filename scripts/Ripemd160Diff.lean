import FeProofs.Precompiles.Exported.Ripemd160
import Fe.EVM.Diff

/-!
# RIPEMD-160: the exported model against EVMLean

Runs the exported model of the contract `Ripemd160` of `FeProofs/Precompiles` (fevm's
`hashes::ripemd160` behind a fallback arm) on call data, and EVMLean's RIPEMD-160, `Ξ_RIP160`, on
the same bytes: the model must return the 32 bytes `Ξ_RIP160` outputs.  The inputs are the test
vectors of the RIPEMD-160 paper (Dobbertin, Bosselaers and Preneel), whose hashes are checked too,
and generated ones: lengths around the 55, 56 and 64 bytes where the padding takes another block,
and others up to 300 bytes.

`lake lean scripts/Ripemd160Diff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace Ripemd160Diff

/-- What the model does on call data `d`: the bytes it returns, or how it ends otherwise. -/
def model (d : ByteArray) : Except String ByteArray :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Ripemd160.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok out
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_RIP160` on call data `d`: its output, or `none` where it fails (an empty account map). -/
def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_RIP160 σ ⟨100000000⟩ default I
  if σ' == ∅ then none else some o

def show? : Option ByteArray → String
  | some o => Ethereum.toHex o
  | none => "failure"

/-- The test vectors of the RIPEMD-160 paper: a message and its hash. -/
def paper : List (String × String) := [
  ("", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
  ("a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
  ("abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
  ("message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
  ("abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
  ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
  ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
    "b0e20b6e3116640286ed3a87a5713079b21f5189"),
  (String.join (List.replicate 8 "1234567890"), "9b752e45573d4b39f4dbd3323cab82bf63326bfb")]

/-! ## Generated inputs -/

abbrev Gen := StateM StdGen

def below (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

/-- Bytes of a length near where the padding takes another block, or of any up to 300. -/
def input : Gen (String × ByteArray) := do
  let near : List Nat := [0, 1, 54, 55, 56, 57, 63, 64, 65, 119, 120, 128]
  let atBlock ← below 2
  let nearLen ← below near.length
  let anyLen ← below 301
  let (kind, len) := if atBlock == 0 then ("near a block", near[nearLen]!) else ("any", anyLen)
  let mut b := ByteArray.empty
  for _ in [:len] do b := b.push (UInt8.ofNat (← below 256))
  return (kind, b)

/-! ## Comparing -/

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut generated := #[]
  let mut gen := mkStdGen 1
  for _ in [:200] do
    let ((kind, d), next) := input.run gen
    gen := next
    generated := generated.push (kind, d, none)
  let inputs := paper.map (fun (m, h) => (s!"paper {repr m}", m.toUTF8, some h)) ++
    generated.toList
  for (name, d, hash) in inputs do
    let s := spec d
    if let some h := hash then
      if s != some (ByteArray.mk (Array.replicate 12 0) ++ Diff.hex h) then
        disagree := disagree + 1
        IO.println s!"DISAGREE {name}: EVMLean {show? s}, the paper {h}"
    match model d with
    | .ok m =>
      if some m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {name} {Ethereum.toHex d}: model {Ethereum.toHex m}, \
          EVMLean {show? s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {name} {Ethereum.toHex d}: the model {how}"
  let near := generated.filter (·.1 == "near a block") |>.size
  IO.println s!"RIPEMD-160: {paper.length} vectors of the paper and 200 generated inputs (near a \
    block {near}, any {200 - near}); {agree} agree, {disagree} disagree"

end Ripemd160Diff

#eval Ripemd160Diff.main
