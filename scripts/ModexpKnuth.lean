import FeProofs.Precompiles.Exported.Modexp
import FeProofs.Precompiles.Modexp.Div32
import Fe.EVM.Diff

/-!
# MODEXP: targeted inputs for `Modulus::reduce`

Random inputs (`scripts/ModexpDiff.lean`) almost never reach the rare branches of Knuth
division.  This script builds inputs that do, from limbs chosen among values near `0`, `2 ^ 63`
and `2 ^ 64`, and checks three things on each:

1. *Which branches it takes*: `simReduce` follows `Modulus::reduce` step by step on numbers,
   with the digit from `div32` and the 2-by-1 remainder from `rem21`, the pure functions proved
   equal to the exported `div_3by2` and `rem_2by1` (`div_3by2_eq`, `rem_2by1_eq`), and the
   branch conditions of the exported code: the digit `β - 1` when the top two window limbs are
   the divisor's, the corrections inside `div_3by2`, the borrow and the add-back, `rem_2by1`'s
   corrections, the shift.
2. *The exported `Modulus_try_new` and `Modulus_reduce` themselves*, run on memory holding the
   divisor and the dividend: the limbs they leave must be those of `X mod M`, the rest zero.
   This also covers `count < n`, which `modexp::run` never reaches (`reduce` is called with
   `count = base_size > n` or `count = 2 n`).
3. *The whole contract against `Ξ_EXPMOD`*, on call data whose run reaches that reduction
   (odd moduli with a base longer than the modulus, and for five or more limbs the conversion of
   the base to Montgomery form, or the single squaring for `e = 2`).

`lake env lean scripts/ModexpKnuth.lean` prints a line per disagreement and the counts per branch.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM
open FeProofs.Precompiles FeProofs.Modexp

namespace ModexpKnuth

def B : Nat := 2 ^ 64

def L (x : Nat) : Limb := ⟨x % 2 ^ 64, Nat.mod_lt _ (by norm_num)⟩

def limbAtN (x i : Nat) : Nat := x / B ^ i % B

/-- The significant limbs of `x`. -/
def sig (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x / 64 + 1

/-- Which correction `div_3by2` makes (Möller–Granlund, algorithm 5), mirroring `div32`. -/
def div32Branch (u2 u1 u0 d1 d0 v : Limb) : String :=
  let x := addD (mulD v u2) (joinD u2 u1)
  let q1 := hiD x
  let q0 := loD x
  let r1 := subMod u1 (mulLo q1 d1)
  let d := joinD d1 d0
  let r := subD (subD (joinD r1 u0) (mulD d0 q1)) d
  if q0.val ≤ (hiD r).val then
    if d.val ≤ (addD r d).val then "div_3by2: decrement, then increment" else "div_3by2: decrement"
  else if d.val ≤ r.val then "div_3by2: increment" else "div_3by2: no correction"

/-- Which correction `rem_2by1` makes (algorithm 4), mirroring `rem21`. -/
def rem21Branch (u1 u0 d v : Limb) : String :=
  let x := addD (mulD v u1) (joinD u1 u0)
  let q1 := addMod (hiD x) 1
  let q0 := loD x
  let r := subMod u0 (mulLo q1 d)
  let add := q0.val < r.val
  let r := if add then addMod r d else r
  let sub := d.val ≤ r.val
  s!"rem_2by1: {if add then "add d" else "no add"}, {if sub then "subtract d" else "no subtract"}"

/-- `Modulus::reduce` on numbers: the remainder, and the branches it takes. -/
def simReduce (X M count : Nat) : Nat × List String := Id.run do
  let n := sig M
  if count < n then return (X, ["count < n"])
  let s := 64 * n - 1 - Nat.log2 M
  let D := M * 2 ^ s
  let mut tags : List String := [s!"shift {if s == 0 then "0" else "> 0"}"]
  if limbAtN D (n - 1) == 2 ^ 63 then tags := "normalised top limb 2^63" :: tags
  let N0 := X * 2 ^ s
  if n == 1 then
    let v := L ((2 ^ 128 - 1) / D - 2 ^ 64)
    let mut r : Nat := 0
    for i' in [:count + 1] do
      let i := count - i'
      let u0 := limbAtN N0 i
      if r + 1 == D then tags := "n = 1: remainder D - 1 before a limb" :: tags
      tags := rem21Branch (L r) (L u0) (L D) v :: tags
      r := (rem21 (L r) (L u0) (L D) v).val
    return (r / 2 ^ s, "n = 1" :: tags)
  let d1 := limbAtN D (n - 1)
  let d0 := limbAtN D (n - 2)
  let v := L ((2 ^ 192 - 1) / (d1 * B + d0) - 2 ^ 64)
  let mut w := N0
  tags := "n ≥ 2" :: tags
  for j' in [:count + 1 - n] do
    let j := count - n - j'
    let W := w / B ^ j % B ^ (n + 1)
    let hi := limbAtN W n
    let nx := limbAtN W (n - 1)
    let th := limbAtN W (n - 2)
    let q ← if hi == d1 && nx == d0 then
        tags := "digit β - 1" :: tags
        pure (B - 1)
      else
        tags := div32Branch (L hi) (L nx) (L th) (L d1) (L d0) v :: tags
        pure (div32 (L hi) (L nx) (L th) (L d1) (L d0) v).val
    let W' ← if W < q * D then
        tags := "add-back" :: tags
        pure (W + D - q * D)
      else
        tags := "no add-back" :: tags
        pure (W - q * D)
    if W' ≥ D then tags := "REMAINDER NOT BELOW D" :: tags
    w := w % B ^ j + B ^ j * W' + (w / B ^ (j + n + 1)) * B ^ (j + n + 1)
  return (w / 2 ^ s % B ^ n, tags)

/-! ## The exported functions on memory -/

def enc (x n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [:n] do
    let l := limbAtN x i
    for k in [:8] do b := b.push (UInt8.ofNat (l / 256 ^ (7 - k) % 256))
  return b

def readLimbs (mem : ByteArray) (p n : Nat) : Nat := Id.run do
  let mut x := 0
  for i in [:n] do
    let mut l := 0
    for k in [:8] do l := l * 256 + (mem.get! (p + 8 * i + k)).toNat
    x := x + l * B ^ i
  return x

/-- The exported `Modulus_try_new` and `Modulus_reduce` on the dividend `X` of `count` limbs and
    the modulus `M`: the limbs `0 .. max count n` of the work array afterwards. -/
def runReduce (X M count : Nat) : Except String Nat :=
  let n := sig M
  let Lw := max count n + 1
  let mem := ByteArray.mk (Array.replicate 0x60 0) ++ enc X Lw ++ enc M n
  let w0 : World := { (World.init ∅ default) with memory := mem }
  let I : ExecutionEnv := default
  let value : FeProofs.Lib.MemArray_u64 := ⟨UInt256.ofNat (0x60 + 8 * Lw), UInt256.ofNat n⟩
  let work : FeProofs.Lib.MemArray_u64 := ⟨UInt256.ofNat 0x60, UInt256.ofNat Lw⟩
  match (Exported.Modexp.Modulus_try_new value (UInt256.ofNat n)).exec I w0 with
  | some (.ok (.Some md, w1)) =>
    match (Exported.Modexp.Modulus_reduce md work (UInt256.ofNat count)).exec I w1 with
    | some (.ok (_, w2)) => .ok (readLimbs w2.memory 0x60 Lw)
    | some (.error e) => .error (Diff.describeExit e)
    | _ => .error "reduce does not terminate"
  | some (.ok (.None, _)) => .error "try_new: none"
  | some (.error e) => .error s!"try_new: {Diff.describeExit e}"
  | none => .error "try_new does not terminate"

/-! ## The whole contract -/

def model (d : ByteArray) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  match (entry FeProofs.Precompiles.Exported.Modexp.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => .ok (some out)
  | some (.error (.revert data)) =>
    if data.isEmpty then .ok none else .error s!"reverts with {Ethereum.toHex data}"
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

def spec (d : ByteArray) : Option ByteArray :=
  let σ : AccountMap := (∅ : AccountMap).insert 0 default
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }
  let (σ', _, _, o) := Ξ_EXPMOD σ ⟨2 ^ 64⟩ default I
  if σ' == ∅ then none else some o

def word (k : Nat) : ByteArray := (UInt256.ofNat k).toByteArray

def be (x len : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for k in [:len] do b := b.push (UInt8.ofNat (x / 256 ^ (len - 1 - k) % 256))
  return b

def calldata (base e M bl el ml : Nat) : ByteArray :=
  word bl ++ word el ++ word ml ++ be base bl ++ be e el ++ be M ml

/-- The reductions `modexp::run` makes on an odd `M > 1`, `e > 0`, nonzero base: of the base when
    it has more limbs than `M`, then for five or more limbs that of the base times `2 ^ (64 n)`, or
    of its square for `e = 2`. -/
def runReductions (base e M : Nat) : List (Nat × Nat) :=
  let n := sig M
  let bs := sig base
  if M % 2 == 0 || M ≤ 1 || e == 0 || base == 0 || (n ≤ 4 && bs ≤ n) then [] else
  let first := if bs > n then [(base, bs)] else []
  let b := if bs > n then base % M else base
  if n ≤ 4 then first
  else if e == 2 then first ++ [(b * b, 2 * n)]
  else first ++ [(b * B ^ n, 2 * n)]

/-! ## Inputs -/

abbrev Gen := StateM StdGen

def below (k : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (k - 1)

/-- A limb near `0`, `2 ^ 63` or `2 ^ 64`, or any. -/
def limb : Gen Nat := do
  match ← below 10 with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure (2 ^ 63 - 1)
  | 3 => pure (2 ^ 63)
  | 4 => pure (2 ^ 63 + 1)
  | 5 => pure (2 ^ 64 - 2)
  | 6 => pure (2 ^ 64 - 1)
  | 7 => return 2 ^ 64 - 1 - (← below 4)
  | _ => below (2 ^ 64)

def number (k : Nat) : Gen Nat := do
  let mut x := 0
  for i in [:k] do x := x + (← limb) * B ^ i
  return x

/-- A candidate: an odd modulus of `n` limbs with a nonzero top limb, possibly with the top limb
    a small power of two or with its high bit set, and a dividend of `count` limbs. -/
def candidate (n count : Nat) : Gen (Nat × Nat) := do
  let mut M ← number n
  match ← below 4 with
  | 0 => M := M % B ^ (n - 1) + B ^ (n - 1) * (2 ^ (← below 64))
  | 1 => M := M % B ^ (n - 1) + B ^ (n - 1) * (2 ^ 63 + (← below (2 ^ 63)))
  | _ => pure ()
  if M / B ^ (n - 1) == 0 then M := M + B ^ (n - 1)
  if M % 2 == 0 then M := M + 1
  let mut X ← number count
  if (← below 3) == 0 then
    -- The top limbs of the dividend those of the normalised divisor, or just below.
    X := X % B ^ (count - n) + B ^ (count - n) * (M - (← below 2))
  return (X, M)

def main : IO Unit := do
  let mut gen := mkStdGen 7
  let mut tally : List (String × Nat) := []
  let mut direct := 0
  let mut contract := 0
  let mut bad := 0
  let mut seen : List String := []
  -- Sizes (n, count): the base reduction for n = 1 .. 4, and dividends of 2n limbs for n ≥ 5.
  let shapes : List (Nat × Nat) := [(1, 2), (1, 5), (2, 3), (2, 6), (3, 5), (4, 6), (4, 9), (5, 10),
    (6, 12), (8, 16)]
  let mut picked : List (Nat × Nat × Nat × List String) := []
  for (n, count) in shapes do
    for _ in [:400] do
      let ((X, M), g') := (candidate n count).run gen
      gen := g'
      let (_, tags) := simReduce X M count
      -- Keep an input when it takes a branch not yet covered at this size.
      let new := (tags.map (fun t => s!"{n}:{t}")).filter (fun t => !seen.contains t)
      if !new.isEmpty then
        seen := seen ++ new
        picked := (X, M, count, tags) :: picked
  -- count < n, by the exported functions directly.
  let lows : List (Nat × Nat × Nat × List String) :=
    [(3, 2 ^ 128 + 5, 1, []), (2 ^ 64 + 7, 2 ^ 192 + 2 ^ 64 + 1, 2, []), (5, 2 ^ 255 + 3, 1, [])]
  for (X, M, count, _) in picked.reverse ++ lows do
    let (r, tags) := simReduce X M count
    for t in tags.eraseDups do
      tally := match tally.lookup t with
        | some k => (t, k + 1) :: tally.filter (·.1 != t)
        | none => (t, 1) :: tally
    let expect := X % M
    if r != expect then
      bad := bad + 1
      IO.println s!"SIMULATION DISAGREES X={X} M={M} count={count}: {r} vs {expect}"
    match runReduce X M count with
    | .ok got =>
      if got == expect then direct := direct + 1 else
        bad := bad + 1
        IO.println s!"DISAGREE reduce X={X} M={M} count={count}: model {got}, expected {expect}"
    | .error how =>
      bad := bad + 1
      IO.println s!"DISAGREE reduce X={X} M={M} count={count}: {how}"
  -- The whole contract, on call data whose run makes these reductions.
  let mut paths : List (String × Nat) := []
  for (X, M, count, _) in picked.reverse do
    let n := sig M
    -- The dividend as the base, so the run reduces it first (its limbs exceed n); then small_power
    -- (n ≤ 4, exponent 3), or large_power with exponent 1 or the single squaring of e = 2.
    let e := if n ≤ 4 then 3 else if X % 2 == 0 then 2 else 1
    let d := calldata X e M (8 * count) 1 (8 * n)
    for (Y, c) in runReductions X e M do
      for t in (simReduce Y M c).2.eraseDups do
        let t := s!"contract: {t}"
        paths := match paths.lookup t with
          | some k => (t, k + 1) :: paths.filter (·.1 != t)
          | none => (t, 1) :: paths
    match model d with
    | .ok m =>
      if m == spec d then contract := contract + 1 else
        bad := bad + 1
        IO.println s!"DISAGREE contract {Ethereum.toHex d}"
    | .error how =>
      bad := bad + 1
      IO.println s!"DISAGREE contract {Ethereum.toHex d}: the model {how}"
  -- The largest lengths: a 1,024-byte base reduced by moduli of one and four limbs, and by one
  -- of 127 limbs (a 1,016-byte modulus) with exponent 1.
  let mut big := 0
  for (bl, ml) in [(1024, 8), (1024, 32), (1024, 1016)] do
    let ((base, M), g') := (do
      let base ← number (bl / 8)
      let M ← number (ml / 8)
      return (base, M - M % 2 + 1 + B ^ (ml / 8 - 1) * (if M / B ^ (ml / 8 - 1) == 0 then 1 else 0))).run gen
    gen := g'
    let (_, tags) := simReduce base M (sig base)
    IO.println s!"large: base {bl} bytes, modulus {ml} bytes: {", ".intercalate tags.eraseDups}"
    let d := calldata base 1 M bl 1 ml
    match model d with
    | .ok m =>
      if m == spec d then big := big + 1 else
        bad := bad + 1
        IO.println s!"DISAGREE large {bl} {ml}"
    | .error how =>
      bad := bad + 1
      IO.println s!"DISAGREE large {bl} {ml}: the model {how}"
  let fmt (t : List (String × Nat)) :=
    "; ".intercalate ((t.toArray.qsort (·.1 < ·.1)).toList.map fun (k, c) => s!"{k}: {c}")
  IO.println s!"branches (inputs taking each): {fmt tally}"
  IO.println s!"contract runs: {fmt paths}"
  IO.println s!"MODEXP Knuth: {picked.length + lows.length} reductions, {direct} agree on the exported reduce; {contract} of {picked.length} contract runs and {big} of 3 large ones agree with Ξ_EXPMOD; {bad} disagree"

end ModexpKnuth

#eval ModexpKnuth.main
