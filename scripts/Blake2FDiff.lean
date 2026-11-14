import FeProofs.Precompiles.Exported.Blake2F
import Fe.EVM.Diff

/-!
# BLAKE2 F: the exported model against EVMLean

Runs the exported model of the contract `Blake2F` of `FeProofs/Precompiles` (fevm's
`blake2f::compress` behind a fallback arm that checks the input as fevm's `run` does) on call
data, and EVMLean's BLAKE2 F, `Ξ_BLAKE2_F`, on the same bytes: the model must return the 64 bytes
`Ξ_BLAKE2_F` outputs, or revert without data where it fails.  The inputs are go-ethereum's
`blake2F` and `fail-blake2f` vectors, whose expected outputs are checked too, but vector 8, which
runs 2 ^ 32 - 1 rounds, and generated ones: 213 bytes with round counts from 0 to 100,
final flags 0 and 1 and invalid ones, and inputs a byte short or long.

`lake env lean scripts/Blake2FDiff.lean` prints a line per disagreement and a total, in about half
an hour: the model's rounds run slowly in the interpreter.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace Blake2FDiff

/-- What the model does on call data `d`: the bytes it returns, or `none` where it reverts
    without data; or how it ends otherwise. -/
def model (d : ByteArray) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Blake2F.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok (some out)
  | some (.error (.revert data)) =>
    if data.isEmpty then .ok none else .error s!"reverts with {Ethereum.toHex data}"
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

/-- `Ξ_BLAKE2_F` on call data `d`: its output, or `none` where it fails (an empty account map). -/
def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_BLAKE2_F σ ⟨100000000⟩ default I
  if σ' == ∅ then none else some o

def show? : Option ByteArray → String
  | some o => Ethereum.toHex o
  | none => "failure"

/-- go-ethereum's `core/vm/testdata/precompiles/blake2F.json` and `fail-blake2f.json`: name,
    input, output (`none` for a failure). -/
def geth : List (String × String × Option String) := [
  ("vector 4",
    "0000000048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000001",
    some ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
      "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")),
  ("vector 5",
    "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000001",
    some ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")),
  ("vector 6",
    "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000000",
    some ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
      "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")),
  ("vector 7",
    "0000000148c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000001",
    some ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
      "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")),
  ("vector 8",
    "007A120048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000001",
    some ("6d2ce9e534d50e18ff866ae92d70cceba79bbcd14c63819fe48752c8aca87a4b" ++
      "b7dcc230d22a4047f0486cfcfb50a17b24b2899eb8fca370f22240adb5170189")),
  ("vector 0: empty input",
    "",
    none),
  ("vector 1: less than 213 bytes input",
    "00000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3a" ++
    "f54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319" ++
    "cde05b6162630000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000300000000000000000000000000000001",
    none),
  ("vector 2: more than 213 bytes input",
    "000000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d" ++
    "5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e" ++
    "1319cde05b616263000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "00000000000300000000000000000000000000000001",
    none),
  ("vector 3: malformed final block indicator flag",
    "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f" ++
    "3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e13" ++
    "19cde05b61626300000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000300000000000000000000000000000002",
    none)
]

/-! ## Generated inputs -/

abbrev Gen := StateM StdGen

def below (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

def bytes (n : Nat) : Gen ByteArray := do
  let mut b := ByteArray.empty
  for _ in [:n] do b := b.push (UInt8.ofNat (← below 256))
  return b

/-- One generated input: a round count, a state, a message block and offsets, and a flag. -/
def input : Gen (String × ByteArray) := do
  let rounds ← match ← below 4 with
    | 0 => pure 0
    | 1 => below 13
    | 2 => below 30
    | _ => below 100
  let body ← bytes 208
  let (kind, flag) ← match ← below 8 with
    | 0 => pure ("bad flag", 2 + (← below 254))
    | 1 | 2 | 3 => pure ("final", 1)
    | _ => pure ("not final", 0)
  let d := (UInt256.ofNat rounds).toByteArray.extract 28 32 ++ body
    ++ ByteArray.mk #[UInt8.ofNat flag]
  match ← below 12 with
  | 0 => return ("short", d.extract 0 212)
  | 1 => return ("long", d.push (UInt8.ofNat (← below 256)))
  | _ => return (kind, d)

/-! ## Comparing -/

def main : IO Unit := do
  let mut agree := 0
  let mut disagree := 0
  let mut successes := 0
  for (name, i, o) in geth do
    let d := Diff.hex i
    let s := spec d
    if s != o.map Diff.hex then
      disagree := disagree + 1
      IO.println s!"DISAGREE geth {name}: EVMLean {show? s}, go-ethereum {o.getD "failure"}"
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
  for _ in [:120] do
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
  IO.println s!"BLAKE2 F: {geth.length} go-ethereum vectors and 120 generated inputs ({counts}); \
    {successes} generated succeed; {agree} agree, {disagree} disagree"

end Blake2FDiff

#eval Blake2FDiff.main
