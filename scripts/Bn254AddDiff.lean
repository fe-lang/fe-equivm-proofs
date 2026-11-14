import FeProofs.Precompiles.Exported.Bn254Add
import Fe.EVM.Diff

/-!
# ECADD: the exported model against EVMLean

Runs the exported model of the contract `Bn254Add` of `FeProofs/Precompiles` (fevm's `bn254::add`
behind a fallback arm) on call data, and EVMLean's ECADD, `Ξ_BN_ADD`, on the same bytes: the model
must return the 64 bytes `Ξ_BN_ADD` outputs, or revert without data where it fails.  The inputs
are go-ethereum's `bn256Add` vectors, whose expected outputs are checked too, and generated ones:
points on the curve, sums of a point with itself, with its negation and with the point at
infinity, points off the curve, coordinates at and above the modulus, and inputs cut short or
extended.

`lake env lean scripts/Bn254AddDiff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM Weierstrass

namespace Bn254AddDiff

def p : Nat := BN254.p

/-- What the model does on call data `d`: the bytes it returns, or `none` where it reverts
    without data; or how it ends otherwise. -/
def model (d : ByteArray) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Bn254Add.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok (some out)
  | some (.error (.revert data)) =>
    if data.isEmpty then .ok none else .error s!"reverts with {Ethereum.toHex data}"
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_BN_ADD` on call data `d`: its output, or `none` where it fails (an empty account map). -/
def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_BN_ADD σ ⟨100000⟩ default I
  if σ' == ∅ then none else some o

def show? : Option ByteArray → String
  | some o => Ethereum.toHex o
  | none => "failure"

/-- go-ethereum's `core/vm/testdata/precompiles/bn256Add.json`: name, input, output. -/
def geth : List (String × String × String) := [
  ("chfast1",
    "18b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9" ++
    "063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f37266" ++
    "07c2b7f58a84bd6145f00c9c2bc0bb1a187f20ff2c92963a88019e7c6a014eed" ++
    "06614e20c147e940f2d70da3f74c9a17df361706a4485c742bd6788478fa17d7",
    "2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703" ++
    "301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c915"),
  ("chfast2",
    "2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703" ++
    "301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c915" ++
    "18b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9" ++
    "063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f37266",
    "2bd3e6d0f3b142924f5ca7b49ce5b9d54c4703d7ae5648e61d02268b1a0a9fb7" ++
    "21611ce0a6af85915e2f1d70300909ce2e49dfad4a4619c8390cae66cefdb204"),
  ("cdetrio1",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"),
  ("cdetrio2",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"),
  ("cdetrio3",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "00000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"),
  ("cdetrio4",
    "",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"),
  ("cdetrio5",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"),
  ("cdetrio6",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002"),
  ("cdetrio7",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002"),
  ("cdetrio8",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002"),
  ("cdetrio9",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002"),
  ("cdetrio10",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002"),
  ("cdetrio11",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002",
    "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3" ++
    "15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4"),
  ("cdetrio12",
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3" ++
    "15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4"),
  ("cdetrio13",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98",
    "15bf2bb17880144b5d1cd2b1f46eff9d617bffd1ca57c37fb5a49bd84e53cf66" ++
    "049c797f9ce0d17083deb32b5e36f2ea2a212ee036598dd7624c168993d1355f"),
  ("cdetrio14",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "2e83f8d734803fc370eba25ed1f6b8768bd6d83887b87165fc2434fe11a830cb" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000")
]

/-! ## Generated inputs -/

abbrev Gen := StateM StdGen

def below (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

def word (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

/-- A point on `y² = x³ + 3`: an `x` whose `x³ + 3` is a square, and a square root (`p ≡ 3`
    modulo 4), either one. -/
partial def onCurve : Gen (Nat × Nat) := do
  let x ← below p
  let a := fadd p (fmul p (fmul p x x) x) 3
  let y := powMod a ((p + 1) / 4) p
  if fmul p y y != a then onCurve
  else return (x, if (← below 2) == 0 then y else (p - y) % p)

/-- A pair `(x, y)` below `p` off the curve. -/
partial def offCurve : Gen (Nat × Nat) := do
  let x ← below p
  let y ← below p
  if fmul p y y == fadd p (fmul p (fmul p x x) x) 3 || (x == 0 && y == 0) then offCurve
  else return (x, y)

/-- An encoding of a point: on the curve most often, the point at infinity, or invalid. -/
def coordinates : Gen (Nat × Nat) := do
  match ← below 12 with
  | 0 => return (0, 0)
  | 1 => offCurve
  | 2 => do let (x, y) ← onCurve; return (x + p, y)
  | 3 => do let (x, y) ← onCurve; return (x, y + p)
  | 4 => return (p, ← below 4)
  | 5 => return (2 ^ 256 - 1, ← below p)
  | 6 => return (0, ← below p)
  | 7 => return (← below p, 0)
  | _ => onCurve

def pair (a b : Nat × Nat) : ByteArray := word a.1 ++ word a.2 ++ word b.1 ++ word b.2

/-- One generated input. -/
def input : Gen (String × ByteArray) := do
  let a ← onCurve
  match ← below 10 with
  | 0 => return ("P + P", pair a a)
  | 1 => return ("P + -P", pair a (a.1, (p - a.2) % p))
  | 2 => return ("P + O", pair a (0, 0))
  | 3 => return ("O + P", pair (0, 0) a)
  | 4 => do
    let d := pair (← coordinates) (← coordinates)
    return ("short", d.extract 0 (← below d.size))
  | 5 => do
    let d := pair a (← onCurve)
    let extra ← below 70
    return ("long", d ++ (ByteArray.mk (Array.replicate extra (UInt8.ofNat (← below 256)))))
  | 6 | 7 => return ("encodings", pair (← coordinates) (← coordinates))
  | _ => return ("P + Q", pair a (← onCurve))

/-! ## Comparing -/

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut successes := 0
  for (name, i, o) in geth do
    let d := Diff.hex i
    let s := spec d
    if s != some (Diff.hex o) then
      disagree := disagree + 1
      IO.println s!"DISAGREE geth {name}: EVMLean {show? s}, go-ethereum {o}"
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE geth {name} {i}: model {show? m}, EVMLean {show? s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE geth {name} {i}: the model {how}"
  let mut kinds : List (String × Nat) := []
  for seed in [:400] do
    let (kind, d) := input.run' (mkStdGen seed)
    let s := spec d
    if s.isSome then successes := successes + 1
    kinds := match kinds.lookup kind with
      | some n => (kind, n + 1) :: kinds.filter (·.1 != kind)
      | none => (kind, 1) :: kinds
    match model d with
    | .ok m =>
      if m == s then agree := agree + 1 else
        disagree := disagree + 1
        IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: model {show? m}, EVMLean {show? s}"
    | .error how =>
      disagree := disagree + 1
      IO.println s!"DISAGREE {kind} {Ethereum.toHex d}: the model {how}"
  let counts := ", ".intercalate (kinds.reverse.map fun (k, n) => s!"{k} {n}")
  IO.println s!"ECADD: {geth.length} go-ethereum vectors and 400 generated inputs ({counts}); \
    {successes} generated succeed; {agree} agree, {disagree} disagree"

end Bn254AddDiff

#eval Bn254AddDiff.main
