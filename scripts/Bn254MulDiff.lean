import FeProofs.Precompiles.Exported.Bn254Mul
import Fe.EVM.Diff

/-!
# ECMUL: the exported model against EVMLean

Runs the exported model of the contract `Bn254Mul` of `FeProofs/Precompiles` (fevm's `bn254::mul`
behind a fallback arm) on call data, and EVMLean's ECMUL, `Ξ_BN_MUL`, on the same bytes: the model
must return the 64 bytes `Ξ_BN_MUL` outputs, or revert without data where it fails.  The inputs
are go-ethereum's `bn256ScalarMul` vectors, whose expected outputs are checked too, and generated
ones: points on the curve, the point at infinity, points off the curve and coordinates at and
above the modulus, times the scalars 0, 1, 2, `r - 1`, `r`, `r + 1`, `2 ^ 256 - 1` and random
ones, and inputs cut short or extended.

`lake lean scripts/Bn254MulDiff.lean` prints a line per disagreement and a total.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM Weierstrass

namespace Bn254MulDiff

def p : Nat := BN254.p

/-- The order of G1. -/
def r : Nat := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

/-- What the model does on call data `d`: the bytes it returns, or `none` where it reverts
    without data; or how it ends otherwise. -/
def model (d : ByteArray) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Bn254Mul.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok (some out)
  | some (.error (.revert data)) =>
    if data.isEmpty then .ok none else .error s!"reverts with {Ethereum.toHex data}"
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_BN_MUL` on call data `d`: its output, or `none` where it fails (an empty account map). -/
def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_BN_MUL σ ⟨100000⟩ default I
  if σ' == ∅ then none else some o

def show? : Option ByteArray → String
  | some o => Ethereum.toHex o
  | none => "failure"

/-- go-ethereum's `core/vm/testdata/precompiles/bn256ScalarMul.json`: name, input, output. -/
def geth : List (String × String × String) := [
  ("chfast1",
    "2bd3e6d0f3b142924f5ca7b49ce5b9d54c4703d7ae5648e61d02268b1a0a9fb7" ++
    "21611ce0a6af85915e2f1d70300909ce2e49dfad4a4619c8390cae66cefdb204" ++
    "00000000000000000000000000000000000000000000000011138ce750fa15c2",
    "070a8d6a982153cae4be29d434e8faef8a47b274a053f5a4ee2a6c9c13c31e5c" ++
    "031b8ce914eba3a9ffb989f9cdd5b0f01943074bf4f0f315690ec3cec6981afc"),
  ("chfast2",
    "070a8d6a982153cae4be29d434e8faef8a47b274a053f5a4ee2a6c9c13c31e5c" ++
    "031b8ce914eba3a9ffb989f9cdd5b0f01943074bf4f0f315690ec3cec6981afc" ++
    "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46",
    "025a6f4181d2b4ea8b724290ffb40156eb0adb514c688556eb79cdea0752c2bb" ++
    "2eff3f31dea215f1eb86023a133a996eb6300b44da664d64251d05381bb8a02e"),
  ("chfast3",
    "025a6f4181d2b4ea8b724290ffb40156eb0adb514c688556eb79cdea0752c2bb" ++
    "2eff3f31dea215f1eb86023a133a996eb6300b44da664d64251d05381bb8a02e" ++
    "183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3",
    "14789d0d4a730b354403b5fac948113739e276c23e0258d8596ee72f9cd9d323" ++
    "0af18a63153e0ec25ff9f2951dd3fa90ed0197bfef6e2a1a62b5095b9d2b4a27"),
  ("cdetrio1",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6" ++
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "2cde5879ba6f13c0b5aa4ef627f159a3347df9722efce88a9afbb20b763b4c41" ++
    "1aa7e43076f6aee272755a7f9b84832e71559ba0d2e0b17d5f9f01755e5b0d11"),
  ("cdetrio2",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6" ++
    "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "163511ddc1c3f25d396745388200081287b3fd1472d8339d5fecb2eae0830451"),
  ("cdetrio3",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6" ++
    "0000000000000000000000000000000100000000000000000000000000000000",
    "1051acb0700ec6d42a88215852d582efbaef31529b6fcbc3277b5c1b300f5cf0" ++
    "135b2394bb45ab04b8bd7611bd2dfe1de6a4e6e2ccea1ea1955f577cd66af85b"),
  ("cdetrio4",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6" ++
    "0000000000000000000000000000000000000000000000000000000000000009",
    "1dbad7d39dbc56379f78fac1bca147dc8e66de1b9d183c7b167351bfe0aeab74" ++
    "2cd757d51289cd8dbd0acf9e673ad67d0f0a89f912af47ed1be53664f5692575"),
  ("cdetrio5",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6" ++
    "0000000000000000000000000000000000000000000000000000000000000001",
    "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3" ++
    "1a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6"),
  ("cdetrio6",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "29e587aadd7c06722aabba753017c093f70ba7eb1f1c0104ec0564e7e3e21f60" ++
    "22b1143f6a41008e7755c71c3d00b6b915d386de21783ef590486d8afa8453b1"),
  ("cdetrio7",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "2e83f8d734803fc370eba25ed1f6b8768bd6d83887b87165fc2434fe11a830cb"),
  ("cdetrio8",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "0000000000000000000000000000000100000000000000000000000000000000",
    "221a3577763877920d0d14a91cd59b9479f83b87a653bb41f82a3f6f120cea7c" ++
    "2752c7f64cdd7f0e494bff7b60419f242210f2026ed2ec70f89f78a4c56a1f15"),
  ("cdetrio9",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "0000000000000000000000000000000000000000000000000000000000000009",
    "228e687a379ba154554040f8821f4e41ee2be287c201aa9c3bc02c9dd12f1e69" ++
    "1e0fd6ee672d04cfd924ed8fdc7ba5f2d06c53c1edc30f65f2af5a5b97f0a76a"),
  ("cdetrio10",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c" ++
    "0000000000000000000000000000000000000000000000000000000000000001",
    "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9" ++
    "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c"),
  ("cdetrio11",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "00a1a234d08efaa2616607e31eca1980128b00b415c845ff25bba3afcb81dc00" ++
    "242077290ed33906aeb8e42fd98c41bcb9057ba03421af3f2d08cfc441186024"),
  ("cdetrio12",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
    "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "2929ee761a352600f54921df9bf472e66217e7bb0cee9032e00acc86b3c8bfaf"),
  ("cdetrio13",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
    "0000000000000000000000000000000100000000000000000000000000000000",
    "1071b63011e8c222c5a771dfa03c2e11aac9666dd097f2c620852c3951a4376a" ++
    "2f46fe2f73e1cf310a168d56baa5575a8319389d7bfa6b29ee2d908305791434"),
  ("cdetrio14",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
    "0000000000000000000000000000000000000000000000000000000000000009",
    "19f75b9dd68c080a688774a6213f131e3052bd353a304a189d7a2ee367e3c258" ++
    "2612f545fb9fc89fde80fd81c68fc7dcb27fea5fc124eeda69433cf5c46d2d7f"),
  ("cdetrio15",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
    "0000000000000000000000000000000000000000000000000000000000000001",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98"),
  ("zeroScalar",
    "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869" ++
    "073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98" ++
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
def point : Gen (String × Nat × Nat) := do
  match ← below 10 with
  | 0 => return ("infinity", 0, 0)
  | 1 => return ("off the curve", ← offCurve)
  | 2 => do let (x, y) ← onCurve; return ("x + p", x + p, y)
  | 3 => do let (x, y) ← onCurve; return ("y + p", x, y + p)
  | 4 => return ("x = p", p, ← below 4)
  | 5 => return ("x = 2^256 - 1", 2 ^ 256 - 1, ← below p)
  | _ => return ("on the curve", ← onCurve)

def scalar : Gen Nat := do
  match ← below 10 with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure 2
  | 3 => pure (r - 1)
  | 4 => pure r
  | 5 => pure (r + 1)
  | 6 => pure (2 ^ 256 - 1)
  | _ => below (2 ^ 256)

/-- One generated input. -/
def input : Gen (String × ByteArray) := do
  let (kind, x, y) ← point
  let d := word x ++ word y ++ word (← scalar)
  match ← below 10 with
  | 0 => return ("short", d.extract 0 (← below d.size))
  | 1 => do
    let extra ← below 70
    return ("long", d ++ (ByteArray.mk (Array.replicate extra (UInt8.ofNat (← below 256)))))
  | _ => return (kind, d)

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
  let mut gen := mkStdGen 1
  for _ in [:200] do
    let ((kind, d), next) := input.run gen
    gen := next
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
  IO.println s!"ECMUL: {geth.length} go-ethereum vectors and 200 generated inputs ({counts}); \
    {successes} generated succeed; {agree} agree, {disagree} disagree"

end Bn254MulDiff

#eval Bn254MulDiff.main
