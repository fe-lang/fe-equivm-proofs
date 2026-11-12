import Fe.EVM.Diff

/-!
# Generated calls

The Fe tests of a contract call it on the inputs their author thought of.  `generated` deploys
each contract with generated constructor arguments and sends it sequences of generated calls,
each from the state the last one left, and compares every creation and call with the model as
`Fe/EVM/Diff.lean` does for the calls of a test.

Arguments are generated from the ABI types of the contract's interface, so that most calls get
past decoding: numbers near the ends of their range or near a word the contract's storage
holds, addresses out of a few accounts, short dynamic values.  Some inputs are then cut short,
extended, or given a word no encoder writes.  Some calls go to no entry point, and some are
made under a static call.

A sequence is a function of its number, so a disagreement is reproduced by running it again.
-/

namespace Fe.EVM.Diff

open Ethereum Ethereum.EVM

/-! ## ABI types -/

inductive AbiType where
  | uint (bits : Nat)
  | int (bits : Nat)
  | address
  | bool
  | fixedBytes (size : Nat)
  /-- `bytes` and `string`. -/
  | bytes
  | array (item : AbiType) (length : Option Nat)
  | tuple (items : List AbiType)
  deriving Inhabited

mutual

/-- Parse a canonical type from the start of `cs`. -/
partial def parseType (cs : List Char) : Option (AbiType × List Char) := do
  match cs with
  | '(' :: rest =>
    let (items, rest) ← parseItems rest
    parseSuffixes (.tuple items) rest
  | _ =>
    let name := cs.takeWhile Char.isAlphanum
    let sized (kind : String) (make : Nat → AbiType) : Option AbiType :=
      if kind.toList.isPrefixOf name then
        (String.ofList (name.drop kind.length)).toNat?.map make
      else none
    let base ←
      if name == "address".toList then some AbiType.address
      else if name == "bool".toList then some .bool
      else if name == "string".toList || name == "bytes".toList then some .bytes
      else sized "uint" .uint <|> sized "int" .int <|> sized "bytes" .fixedBytes
    parseSuffixes base (cs.dropWhile Char.isAlphanum)

/-- The array suffixes after a type. -/
partial def parseSuffixes (base : AbiType) : List Char → Option (AbiType × List Char)
  | '[' :: rest =>
    match rest.dropWhile Char.isDigit with
    | ']' :: after =>
      parseSuffixes (.array base (String.ofList (rest.takeWhile Char.isDigit)).toNat?) after
    | _ => none
  | rest => some (base, rest)

/-- The components of a tuple, after its opening parenthesis. -/
partial def parseItems : List Char → Option (List AbiType × List Char)
  | ')' :: rest => some ([], rest)
  | cs => do
    let (item, rest) ← parseType cs
    match rest with
    | ',' :: rest =>
      let (items, rest) ← parseItems rest
      some (item :: items, rest)
    | ')' :: rest => some ([item], rest)
    | _ => none

end

/-- Whether a value of the type is encoded in the tail. -/
partial def AbiType.dynamic : AbiType → Bool
  | .bytes | .array _ none => true
  | .array item (some _) => item.dynamic
  | .tuple items => items.any AbiType.dynamic
  | _ => false

/-! ## Generators -/

abbrev Gen := StateM StdGen

/-- A number below `n`. -/
def below (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

def oneIn (n : Nat) : Gen Bool := return (← below n) == 0

def pick (xs : List Nat) : Gen Nat := return xs.getD (← below xs.length) 0

def word (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

/-- What a sequence has to draw on: the addresses in use, and the words in the contract's
    storage. -/
structure Known where
  addresses : List Nat
  words : List Nat := []

/-- A number below `2 ^ bits`, most often near an end of the range or near a known word: a
    balance is spent to its last unit by a call that names it. -/
def genNat (known : Known) (bits : Nat) : Gen Nat := do
  let near ← pick known.words
  let n ← match ← below (if known.words.isEmpty then 8 else 16) with
    | 0 => pure 0
    | 1 => pure 1
    | 2 => below 16
    | 3 | 4 => below 1001
    | 5 => pure (2 ^ bits - 1)
    | 6 => pure (2 ^ (bits - 1))
    | 7 => below (2 ^ bits)
    | 8 | 9 => below (near + 1)
    | 10 => pure (near + 1)
    | 11 => pure (near - 1)
    | _ => pure near
  return n % 2 ^ bits

def genBytes (size : Nat) : Gen ByteArray := do
  let mut bytes := ByteArray.empty
  for _ in [:size] do
    bytes := bytes.push (UInt8.ofNat (← below 256))
  return bytes

/-- The word of a value of a one-word type.  One time in sixteen it is any word, which a narrow
    type's decoder rejects. -/
def genScalar (known : Known) (type : AbiType) : Gen Nat := do
  if ← oneIn 16 then return ← below (2 ^ 256)
  match type with
  | .uint bits => genNat known bits
  | .int bits =>
    let magnitude ← genNat known (bits - 1)
    -- The complement of `m` is `-(m + 1)`.
    return if ← oneIn 2 then magnitude else 2 ^ 256 - 1 - magnitude
  | .address => do if ← oneIn 8 then below (2 ^ 160) else pick known.addresses
  | .bool => below 2
  | .fixedBytes size => return (← below (2 ^ (8 * size))) * 2 ^ (8 * (32 - size))
  | _ => pure 0

mutual

/-- The encoding of a value of the type. -/
partial def genValue (known : Known) : AbiType → Gen ByteArray
  | .bytes => do
    let size ← do if ← oneIn 2 then pick [0, 1, 31, 32, 33, 48, 64, 96] else below 100
    return word size ++ (← genBytes size) ++ ByteArray.mk (Array.replicate ((32 - size % 32) % 32) 0)
  | .array item none => do
    let length ← below 4
    return word length ++ (← genTuple known (List.replicate length item))
  | .array item (some length) => genTuple known (List.replicate length item)
  | .tuple items => genTuple known items
  | type => return word (← genScalar known type)

/-- The encoding of a value of each type: the heads, then the tails. -/
partial def genTuple (known : Known) (items : List AbiType) : Gen ByteArray := do
  let mut parts : Array (Bool × ByteArray) := #[]
  for item in items do
    parts := parts.push (item.dynamic, ← genValue known item)
  let headSize := parts.foldl (fun n (dynamic, part) => n + if dynamic then 32 else part.size) 0
  let mut heads := ByteArray.empty
  let mut tails := ByteArray.empty
  for (dynamic, part) in parts do
    if dynamic then
      heads := heads ++ word (headSize + tails.size)
      tails := tails ++ part
    else heads := heads ++ part
  return heads ++ tails

end

/-- Arguments of the canonical tuple type `inputs`, or a few words if it is not one. -/
def genInputs (known : Known) (inputs : String) : Gen ByteArray := do
  match parseType inputs.toList with
  | some (.tuple items, []) => genTuple known items
  | _ =>
    let mut bytes := ByteArray.empty
    for _ in [:← below 4] do
      bytes := bytes ++ word (← genNat known 256)
    return bytes

/-- One time in eight: the bytes cut short, extended by a word, or with one of the words after
    `start` replaced. -/
def mutate (known : Known) (start : Nat) (bytes : ByteArray) : Gen ByteArray := do
  if !(← oneIn 8) then return bytes
  match ← below 3 with
  | 0 => return bytes.extract 0 (← below (bytes.size + 1))
  | 1 => return bytes ++ word (← genNat known 256)
  | _ =>
    let words := (bytes.size - start) / 32
    if words == 0 then return bytes
    let offset := start + 32 * (← below words)
    let replacement ← do if ← oneIn 2 then pick [0, 32, 64, 2 ^ 255, 2 ^ 256 - 1] else genNat known 256
    return bytes.extract 0 offset ++ word replacement ++ bytes.extract (offset + 32) bytes.size

/-- An amount of wei: a small one, or one a contract may ask for. -/
def genAmount : Gen Nat := do
  if ← oneIn 2 then below 1001 else pick [10 ^ 9, 10 ^ 18, 32 * 10 ^ 18]

/-! ## Sequences -/

/-- The gas a generated creation or call runs with, and the bound on its steps.  A frame that
    runs longer counts as out of gas: the interpreter is slow, and the model is not run. -/
def generatedGas : Nat := 30000000
def generatedSteps : Nat := 50000

/-- Run a frame from the start of a transaction and compare it with `model`.  The model is not
    run when the EVM runs out of gas or overflows its stack: nothing bounds it then.  `Agrees`
    holds of no model run when the stack overflows, so that is a disagreement. -/
def frame (σ : AccountMap) (A : Substate) (I : ExecutionEnv) (model : FeM ByteArray) :
    Verdict × Except ExecutionException (ExecutionResult State) :=
  let r := run (fresh σ σ generatedGas A I) generatedSteps
  match r.result with
  | .error .OutOfGass | .error .OutOfFuel => (.outOfGas, r.result)
  | .error .StackOverflow => (.disagree "EVM halts with StackOverflow, model not run", r.result)
  | _ => (compare r.result (model.exec I (World.init σ A (r.events.toList.map supply))), r.result)

/-- Deploy `target`, trying a few argument lists until its constructor returns, and send it
    `calls` calls.  Returns the comparisons and how many calls returned. -/
def sequence (target : Target) (index calls : Nat) : Gen (Array Report × Nat) := do
  let actors := [0xa11ce, 0xb0b, 0xca401]
  let contract := 0xfe
  let mut known : Known := { addresses := [0, contract] ++ actors }
  let address : AccountAddress := Fin.ofNat _ contract
  let test := s!"generated{index}"
  let mut σ : AccountMap := actors.foldl
    (fun σ a => σ.insert (Fin.ofNat _ a) { (default : Account) with balance := .ofNat (10 ^ 24) }) ∅
  let mut reports : Array Report := #[]
  let mut deployed := false
  let A : Substate := (default : Substate).addAccessedAccount address
  for _ in [:4] do
    let creator : AccountAddress := Fin.ofNat _ (← pick actors)
    let pays ← do if target.interface.initPayable then oneIn 2 else oneIn 16
    let amount ← genAmount
    let value : UInt256 := .ofNat (if pays then amount else 0)
    let args ← mutate known 0 (← genInputs known target.interface.init)
    let account := σ.getD creator default
    let σ₁ := σ.insert creator
        { account with balance := account.balance - value, nonce := account.nonce + ⟨1⟩ }
      |>.insert address { (default : Account) with nonce := ⟨1⟩, balance := value }
    let I : ExecutionEnv :=
      { (default : ExecutionEnv) with
          codeOwner := address, sender := creator, source := creator, weiValue := value,
          code := target.creation ++ args, perm := true }
    let (verdict, result) :=
      frame σ₁ { A with createdAccounts := A.createdAccounts.insert address } I
        (target.model.init args >>= fun tail => pure (target.runtime ++ tail))
    reports := reports.push ⟨test, target.name, s!"init {Ethereum.toHex args}", verdict⟩
    if let .ok (.success s code) := result then
      σ := s.accountMap.insert address { s.accountMap.getD address default with code := code }
      deployed := true
      break
  let mut returned := 0
  if deployed then
    for _ in [:calls] do
      known := { known with words := (σ.getD address default).storage.values.map (·.toNat) }
      let sender : AccountAddress := Fin.ofNat _ (← pick actors)
      let arms := target.interface.arms
      let arm? ← do if ← oneIn 8 then pure none else pure arms[← below arms.length]?
      let input ← match arm? with
        | some arm =>
          mutate known 4 ((word arm.selector).extract 28 32 ++ (← genInputs known arm.inputs))
        | none => do genBytes (← pick [0, 1, 3, 4, 36, 68])
      let static ← oneIn 16
      let pays ← do if arm?.any (·.payable) then oneIn 2 else oneIn 16
      let amount ← genAmount
      let value : UInt256 := .ofNat (if pays && !static then amount else 0)
      let payer := σ.getD sender default
      let σ₁ := σ.insert sender { payer with balance := payer.balance - value }
      let payee := σ₁.getD address default
      let σ₁ := σ₁.insert address { payee with balance := payee.balance + value }
      let I : ExecutionEnv :=
        { (default : ExecutionEnv) with
            codeOwner := address, sender := sender, source := sender, weiValue := value,
            calldata := input, code := payee.code, perm := !static }
      let (verdict, result) := frame σ₁ A I target.model.runtime
      let how := if static then "static " else ""
      reports := reports.push
        ⟨test, target.name, s!"{how}{Ethereum.toHex input} value {value.toNat}", verdict⟩
      if let .ok (.success s _) := result then
        σ := s.accountMap
        returned := returned + 1
  return (reports, returned)

/-- Run `sequences` sequences of `calls` calls on each target and print one line per comparison
    that does not agree, and a total per target. -/
def generated (fixture : String) (targets : List Target) (sequences : Nat := 4)
    (calls : Nat := 32) : IO Unit := do
  for target in targets do
    let mut agree := 0
    let mut disagree := 0
    let mut outOfGas := 0
    let mut deployed := 0
    let mut returned := 0
    for index in [:sequences] do
      let (reports, count) := (sequence target index calls).run' (mkStdGen index)
      returned := returned + count
      if reports.any (!·.input.startsWith "init") then deployed := deployed + 1
      for r in reports do
        match r.verdict with
        | .agree _ => agree := agree + 1
        | .outOfGas => outOfGas := outOfGas + 1
        | .disagree why =>
          disagree := disagree + 1
          IO.println s!"DISAGREE {fixture}::{r.test} {r.target} {r.input}: {why}"
    IO.println s!"GEN {fixture} {target.name} sequences={sequences} deployed={deployed} agree={agree} disagree={disagree} outOfGas={outOfGas} returned={returned}"

end Fe.EVM.Diff
