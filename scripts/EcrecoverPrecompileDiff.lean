import FeProofs.Precompiles.Exported.EcrecoverPrecompile
import Fe.EVM.Diff

/-!
# ECRECOVER: the exported model against EVMLean

Runs the exported model of the contract `EcrecoverPrecompile` of `FeProofs/Precompiles` (fevm's
`ecrecover` behind a fallback arm) on call data, and EVMLean's ECRECOVER, `Ξ_ECREC`, with enough
gas, on the same bytes: the model must return what `Ξ_ECREC` outputs, the signer's address as a
word or nothing.  The inputs are go-ethereum's `ecRecover` vectors and the vectors of EVMLean's
`Ethereum/Secp256k1/Tests.lean`, whose expected outputs are checked too, and generated ones:
signatures by random keys, with their `v` and with 26, 29 and the other parity, with `r` or `s`
at 0, `n - 1` and `n`, and inputs cut short or extended.

`lake env lean scripts/EcrecoverPrecompileDiff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM Weierstrass

namespace EcrecoverPrecompileDiff

def n : Nat := Secp256k1.n

/-- What the model does on call data `d`: the bytes it returns, or how it ends otherwise. -/
def model (d : ByteArray) : Except String ByteArray :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let runtime := FeProofs.Precompiles.Exported.EcrecoverPrecompile.runtime
  match (entry runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok out
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_ECREC` on call data `d`, with the gas it charges. -/
def spec (d : ByteArray) : ByteArray :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  (Ξ_ECREC default ⟨5000⟩ default I).2.2.2

def word (k : Nat) : ByteArray := (UInt256.ofNat k).toByteArray

def call (e v r s : Nat) : ByteArray := word e ++ word v ++ word r ++ word s

/-- go-ethereum's `core/vm/testdata/precompiles/ecRecover.json`: name, input, output. -/
def geth : List (String × String × String) := [
  ("CallEcrecoverUnrecoverableKey",
    "a8b53bdf3306a35a7103ab5504a0c9b492295564b6202b1942a84ef300107281" ++
    "000000000000000000000000000000000000000000000000000000000000001b" ++
    "3078356531653033663533636531386237373263636230303933666637316633" ++
    "6635336635633735623734646362333161383561613862383839326234653862" ++
    "1122334455667788991011121314151617181920212223242526272829303132",
    ""),
  ("ValidKey",
    "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c" ++
    "000000000000000000000000000000000000000000000000000000000000001c" ++
    "73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f" ++
    "eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549",
    "000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"),
  ("InvalidHighV-bits-1",
    "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c" ++
    "100000000000000000000000000000000000000000000000000000000000001c" ++
    "73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f" ++
    "eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549",
    ""),
  ("InvalidHighV-bits-2",
    "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c" ++
    "000000000000000000000000000000000000001000000000000000000000001c" ++
    "73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f" ++
    "eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549",
    ""),
  ("InvalidHighV-bits-3",
    "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c" ++
    "000000000000000000000000000000000000001000000000000000000000011c" ++
    "73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f" ++
    "eeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549",
    "")
]

/-- The vectors of EVMLean's `Ethereum/Secp256k1/Tests.lean`: name, input, output. -/
def evmlean : List (String × ByteArray × ByteArray) :=
  let e₁ := 0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3
  let r₁ := 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608
  let s₁ := 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada
  let e₂ := 0xdaf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e53
  let r₂ := 18515461264373351373200002665853028612451056578545711640558177340181847433846
  let s₂ := 46948507304638947509940763649030358759909902576025900602547168820602576006531
  let signer₁ := word 0x7156526fbd7a3c72969b54f64e42c10fbb768c8a
  [("ValidKey", call e₁ 28 r₁ s₁, signer₁),
   ("EIP-155", call e₂ 27 r₂ s₂, word 0x9d8a62f656a8d1615c1294fd71e9cfb3e4855a4f),
   ("high s", call e₁ 27 r₁ (n - s₁), signer₁),
   ("v 29", call e₁ 29 r₁ s₁, .empty),
   ("r 0", call e₁ 28 0 s₁, .empty),
   ("r n", call e₁ 28 n s₁, .empty),
   ("s 0", call e₁ 28 r₁ 0, .empty),
   ("s n", call e₁ 28 r₁ n, .empty),
   ("no point at 5", call 1 27 5 1, .empty),
   ("key at infinity", call 0x7f6e5d1 27
      0xd47644539acec3da5e3ecf5fe8863c628a9c97e8b71e9ea9167a6f4f83c03c32 7, .empty)]

/-! ## Generated inputs -/

abbrev Gen := StateM StdGen

def below (k : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (k - 1)

/-- A signature of `e` by the key `d`, with nonce `k`: `(v, r, s)`, `v` 27 or 28 by the parity of
    `k G`; none in the rare cases the signature scheme rejects. -/
def sign (e d k : Nat) : Option (Nat × Nat × Nat) := do
  let G : Point := ⟨Secp256k1.gx, Secp256k1.gy, 1⟩
  let (x, y) ← (mulAdd Secp256k1.p G .infinity G 256 k 0).toAffine Secp256k1.p
  let r := x % n
  let s := powMod k (n - 2) n * (e + r * d) % n
  if r == 0 || s == 0 || x ≥ n then none else some (27 + y % 2, r, s)

/-- One generated input. -/
def input : Gen (String × ByteArray) := do
  let e ← below (2 ^ 256)
  let d ← below (n - 1)
  let k ← below (n - 1)
  let some (v, r, s) := sign e (d + 1) (k + 1) | return ("random", call e 28 (k + 1) (d + 1))
  let d := match ← below 16 with
    | 0 => ("v 26", call e 26 r s)
    | 1 => ("v 29", call e 29 r s)
    | 2 => ("other v", call e (55 - v) r s)
    | 3 => ("r 0", call e v 0 s)
    | 4 => ("r n - 1", call e v (n - 1) s)
    | 5 => ("r n", call e v n s)
    | 6 => ("s 0", call e v r 0)
    | 7 => ("s n - 1", call e v r (n - 1))
    | 8 => ("s n", call e v r n)
    | _ => ("signed", call e v r s)
  let cut ← below 10
  let len ← below d.2.size
  let extra ← below (2 ^ 256)
  match cut with
  | 0 => return ("short", d.2.extract 0 len)
  | 1 => return ("long", d.2 ++ word extra)
  | _ => return d

/-! ## Comparing -/

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut recovered := 0
  let vectors := geth.map (fun (name, i, o) => (s!"geth {name}", Diff.hex i, Diff.hex o)) ++
    evmlean.map (fun (name, i, o) => (s!"EVMLean {name}", i, o))
  for (name, d, o) in vectors do
    let s := spec d
    if s != o then
      disagree := disagree + 1
      IO.println s!"DISAGREE {name}: EVMLean {Ethereum.toHex s}, expected {Ethereum.toHex o}"
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {name} {Ethereum.toHex d}: model {Ethereum.toHex m}, \
          EVMLean {Ethereum.toHex s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {name} {Ethereum.toHex d}: the model {how}"
  let mut kinds : List (String × Nat) := []
  let mut gen := mkStdGen 1
  for _ in [:150] do
    let ((kind, d), next) := input.run gen
    gen := next
    let s := spec d
    if !s.isEmpty then recovered := recovered + 1
    kinds := match kinds.lookup kind with
      | some k => (kind, k + 1) :: kinds.filter (·.1 != kind)
      | none => (kind, 1) :: kinds
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: model {Ethereum.toHex m}, \
          EVMLean {Ethereum.toHex s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: the model {how}"
  let counts := ", ".intercalate (kinds.reverse.map fun (k, c) => s!"{k} {c}")
  IO.println s!"ECRECOVER: {vectors.length} vectors and 150 generated inputs ({counts}); \
    {recovered} generated recover a signer; {agree} agree, {disagree} disagree"

end EcrecoverPrecompileDiff

#eval EcrecoverPrecompileDiff.main
