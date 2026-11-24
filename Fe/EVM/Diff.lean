import Fe.EVM.SpecHost

/-!
# Differential tests of exported models

The `#[test]` functions of a Fe file compile to one object, which runs the test its calldata
selects: code that deploys contracts and calls them.  `runTest` runs a test in EVMLean.  At each
creation and message call the test makes on a contract
with an exported model, it runs the model on the inputs EVMLean gives the callee and compares
the two results at profile `P1`: outcome kind, return data, account map, event logs and revert
payload.  Each comparison is an instance of `RefinesFor`, or of `RefinesDeploy` for a creation.

The model's feed is read off the EVM run: the word of each `GAS`, and the gas and substate of
each call or creation the contract makes.

Only the calls the test code itself makes are compared.  What a contract calls in turn runs
inside EVMLean's `Θ` on both sides.

A target with the serialized IR of its contract is also run a third way, by fe-spec's
interpreter on `specHost` (`SpecHost.lean`), from the same world and feed, and compared with
both at `P1`: each call agrees three ways, or one of the pairs (interpreter and model,
interpreter and bytecode, model and bytecode) disagrees, or the interpreter gives up
(`SpecError`).
-/

namespace Fe.EVM.Diff

open Ethereum Ethereum.EVM

/-- The bytes a string of hex digits spells, empty if it is not one. -/
def hex (digits : String) : ByteArray :=
  (ByteArray.ofBlob digits).toOption.getD ByteArray.empty

/-! ## Running a frame step by step -/

/-- What a frame did that its model cannot compute. -/
inductive Event where
  /-- `GAS` pushed this word. -/
  | gas (word : UInt256)
  /-- A call or creation: the instruction, the state it ran in after its memory expansion was
      paid for, the rest of its cost, and the state after it. -/
  | boundary (op : Operation) (before : State) (cost : Nat) (after : State)

structure Run where
  result : Except ExecutionException (ExecutionResult State)
  events : Array Event

def isBoundary : Operation → Bool
  | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL | .CREATE | .CREATE2 => true
  | _ => false

/-- Run `initial` to its end as `X` does, recording the frame's events. -/
def run (initial : State) (fuel : Nat) : Run := Id.run do
  let jumps := D_J initial.executionEnv.code 0
  let mut state := initial
  let mut events : Array Event := #[]
  for _ in [:fuel] do
    let op := (decode state.executionEnv.code state.machineState.pc).map Prod.fst |>.getD .STOP
    match Xstep jumps state with
    | .error e => return ⟨.error e, events⟩
    | .ok (next, halt) =>
      let next := { next with executionEnv.depth := state.executionEnv.depth }
      if op == .GAS then
        events := events.push (.gas (next.machineState.stack.getD 0 ⟨0⟩))
      if isBoundary op then
        if let .ok (paid, cost) := Z jumps op state then
          events := events.push (.boundary op paid cost next)
      match halt with
      | some (.success, out) => return ⟨.ok (.success next out), events⟩
      | some (.revert, out) =>
        return ⟨.ok (.revert next.machineState.gasAvailable.toUInt256 out), events⟩
      | none => state := next
  return ⟨.error .OutOfFuel, events⟩

/-- The state `Ξ` starts a frame in. -/
def fresh (σ σ₀ : AccountMap) (g : Nat) (A : Substate) (I : ExecutionEnv) : State :=
  let s : State := default
  { s with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      machineState.gasAvailable := .ofUInt256 (.ofNat g) }

/-! ## What the EVM hands a callee -/

/-- A message call as `EVM.call` makes it: the gas, the code's address, the recipient, the
    value moved and the value shown, the input, and the permission. -/
structure Message where
  gasArg : UInt256
  t : AccountAddress
  recipient : AccountAddress
  source : AccountAddress
  value : UInt256
  value' : UInt256
  input : ByteArray
  perm : Bool

/-- The message call of a boundary, `none` for a creation. -/
def message? (op : Operation) (s : State) : Option Message :=
  let st := s.machineState.stack
  let at' (i : Nat) := st.getD i ⟨0⟩
  let I := s.executionEnv
  let slice (off len : UInt256) := s.machineState.memory.readWithPadding off.toNat len.toNat
  let addr (w : UInt256) := AccountAddress.ofUInt256 w
  match op with
  | .CALL => some ⟨at' 0, addr (at' 1), addr (at' 1), I.codeOwner, at' 2, at' 2,
      slice (at' 3) (at' 4), I.perm⟩
  | .CALLCODE => some ⟨at' 0, addr (at' 1), I.codeOwner, I.codeOwner, at' 2, at' 2,
      slice (at' 3) (at' 4), I.perm⟩
  | .DELEGATECALL => some ⟨at' 0, addr (at' 1), I.codeOwner, I.source, ⟨0⟩, I.weiValue,
      slice (at' 2) (at' 3), I.perm⟩
  | .STATICCALL => some ⟨at' 0, addr (at' 1), addr (at' 1), I.codeOwner, ⟨0⟩, ⟨0⟩,
      slice (at' 2) (at' 3), false⟩
  | _ => none

/-- What the feed must hold for the model to make the call or creation the EVM made. -/
def supply : Event → Supply
  | .gas word => { gas := word, substate := default, orig := ∅ }
  | .boundary op s cost _ =>
    match message? op s with
    | some m =>
      { gas := .ofNat (Cgascap m.t m.recipient m.value m.gasArg s.accountMap s.machineState
          s.substate)
        substate := (s.addAccessedAccount m.t).substate
        orig := s.σ₀ }
    | none =>
      { gas := .ofNat (L (s.machineState.gasAvailable.toNat - cost))
        substate := s.substate
        orig := s.σ₀ }

def balanceOf (σ : AccountMap) (a : AccountAddress) : UInt256 :=
  σ.get? a |>.option ⟨0⟩ (·.balance)

/-- The frame `Θ` runs for a message call that is made: its accounts, gas, substate and
    environment.  `none` when the call is not made, or runs a precompile. -/
def messageFrame (s : State) (m : Message) : Option (AccountMap × Nat × Substate × ExecutionEnv) :=
  let σ := s.accountMap
  let I := s.executionEnv
  if ¬ (m.value ≤ balanceOf σ I.codeOwner ∧ I.depth < 1024) then none
  else
    match toExecute I.header.fork σ m.t with
    | .Precompiled _ => none
    | .Code code =>
      let credited :=
        match σ.get? m.recipient with
        | none =>
          if m.value != UInt256.ofNat 0 then
            σ.insert m.recipient { (default : Account) with balance := m.value }
          else σ
        | some acc => σ.insert m.recipient { acc with balance := acc.balance + m.value }
      let σ₁ :=
        match credited.get? m.source with
        | none => credited
        | some acc => credited.insert m.source { acc with balance := acc.balance - m.value }
      let callee : ExecutionEnv :=
        { codeOwner := m.recipient
          sender := I.sender
          gasPrice := I.gasPrice
          calldata := m.input
          source := m.source
          weiValue := m.value'
          depth := I.depth + 1
          perm := m.perm
          code := code
          header := I.header
          blobVersionedHashes := I.blobVersionedHashes
          blocks := I.blocks }
      some (σ₁, Ccallgas m.t m.recipient m.value m.gasArg σ s.machineState s.substate,
        (s.addAccessedAccount m.t).substate, callee)

/-- A creation: the address, and the frame `Lambda` runs for the init code.  `none` when the
    creation is not made or the address is taken. -/
def creationFrame (op : Operation) (s : State) (cost : Nat) :
    Option (AccountAddress × ByteArray × AccountMap × Nat × Substate × ExecutionEnv) :=
  let st := s.machineState.stack
  let at' (i : Nat) := st.getD i ⟨0⟩
  let value := at' 0
  let init := s.machineState.memory.readWithPadding (at' 1).toNat (at' 2).toNat
  let salt : Option ByteArray := if op == .CREATE2 then some (at' 3).toByteArray else none
  let I := s.executionEnv
  let σ := s.accountMap
  let self : Account := σ.get? I.codeOwner |>.getD default
  if ¬ (self.nonce.toNat < 2 ^ 64 - 1 ∧ value ≤ balanceOf σ I.codeOwner ∧ I.depth < 1024
      ∧ init.size ≤ 49152) then none
  else
    let σ := σ.insert I.codeOwner { self with nonce := self.nonce + ⟨1⟩ }
    let a : AccountAddress :=
      (KEC (Lambda.L_A I.codeOwner self.nonce salt init)).extract 12 32
        |> fromByteArrayBigEndian |> Fin.ofNat _
    let existing := σ.getD a default
    if existing.nonce ≠ ⟨0⟩ || existing.code.size ≠ 0 || existing.storage != default then none
    else
      let A := s.substate.addAccessedAccount a
      let A := { A with createdAccounts := s.substate.createdAccounts.insert a }
      let created : Account :=
        { existing with nonce := existing.nonce + ⟨1⟩, balance := value + existing.balance }
      let creator : Account := σ.getD I.codeOwner default
      let σ := σ.insert I.codeOwner { creator with balance := creator.balance - value }
        |>.insert a created
      let callee : ExecutionEnv :=
        { codeOwner := a
          sender := I.sender
          source := I.codeOwner
          weiValue := value
          calldata := default
          code := init
          gasPrice := I.gasPrice
          header := I.header
          depth := I.depth + 1
          perm := I.perm
          blobVersionedHashes := I.blobVersionedHashes
          blocks := I.blocks }
      some (a, init, σ, L (s.machineState.gasAvailable.toNat - cost), A, callee)

/-! ## Comparing -/

inductive Verdict where
  | agree (how : String)
  /-- The EVM ran out of gas: nothing is required of the model. -/
  | outOfGas
  /-- The EVM overflowed its stack: nothing is required of the model. -/
  | stackOverflow
  | disagree (why : String)
  /-- The target has no model: the exporter stopped at a construct of the contract. -/
  | noModel

/-- Where two account maps differ, in a few words, the sides named `left` and `right`. -/
def accountsDiff (evm model : AccountMap) (left := "EVM") (right := "model") : String := Id.run do
  let mut notes : Array String := #[]
  for a in (evm.keys ++ model.keys).eraseDups do
    let e := evm.getD a default
    let m := model.getD a default
    if evm.contains a != model.contains a then
      notes := notes.push s!"account {a.val} exists on one side only"
    if e.balance != m.balance then
      notes := notes.push s!"balance of {a.val}: {left} {e.balance.toNat}, {right} {m.balance.toNat}"
    if e.nonce != m.nonce then
      notes := notes.push s!"nonce of {a.val}: {left} {e.nonce.toNat}, {right} {m.nonce.toNat}"
    if e.code != m.code then
      notes := notes.push s!"code of {a.val}"
    for (label, es, ms) in [("slot", e.storage, m.storage), ("transient slot", e.tstorage, m.tstorage)] do
      for k in (es.keys ++ ms.keys).eraseDups do
        let ev := es.getD k ⟨0⟩
        let mv := ms.getD k ⟨0⟩
        if ev != mv then
          notes := notes.push
            s!"{label} {Ethereum.toHex k.toByteArray} of {a.val}: {left} {Ethereum.toHex ev.toByteArray}, {right} {Ethereum.toHex mv.toByteArray}"
  let shown := notes.toList.take 4
  return ", ".intercalate shown ++ (if notes.size > 4 then s!", and {notes.size - 4} more" else "")

def describeExit : Exit World → String
  | .revert data => s!"reverts with {Ethereum.toHex data}"
  | .panic code => s!"panics with code {code}"
  | .static => "fails on a write under a static call"
  | .trap => "traps"
  | .oob => "reads past the return data"
  | .stop data _ => s!"stops with {Ethereum.toHex data}"

def describeEvm : Except ExecutionException (ExecutionResult State) → String
  | .error e => s!"halts with {repr e}"
  | .ok (.success _ out) => s!"returns {Ethereum.toHex out}"
  | .ok (.revert _ out) => s!"reverts with {Ethereum.toHex out}"

/-- `Agrees .P1`, decided.  The model's side is named `label`. -/
def compare (evm : Except ExecutionException (ExecutionResult State))
    (model : Option (Except (Exit World) (ByteArray × World))) (label := "model") : Verdict :=
  let differ (m : String) := Verdict.disagree s!"EVM {describeEvm evm}, {label} {m}"
  let success (out : ByteArray) (w : World) (m : String) : Verdict :=
    match evm with
    | .ok (.success s o) =>
      if o != out then differ m
      else if s.accountMap != w.accounts then
        .disagree s!"accounts differ: {accountsDiff s.accountMap w.accounts (right := label)}"
      else if s.substate.logSeries != w.logs then
        .disagree s!"logs differ: EVM {repr s.substate.logSeries}, {label} {repr w.logs}"
      else .agree "success"
    | _ => differ m
  match evm with
  | .error .OutOfGass | .error .OutOfFuel => .outOfGas
  | .error .StackOverflow => .stackOverflow
  | _ =>
    match model with
    | none => differ "does not terminate"
    | some (.ok (out, w)) => success out w s!"returns {Ethereum.toHex out}"
    | some (.error (.stop out w)) => success out w s!"stops with {Ethereum.toHex out}"
    | some (.error (.revert data)) =>
      match evm with
      | .ok (.revert _ o) => if o == data then .agree "revert" else differ s!"reverts with {Ethereum.toHex data}"
      | _ => differ s!"reverts with {Ethereum.toHex data}"
    | some (.error (.panic code)) =>
      match evm with
      | .ok (.revert _ o) =>
        if o == panicData code then .agree "panic" else differ s!"panics with code {code}"
      | _ => differ s!"panics with code {code}"
    | some (.error .static) =>
      match evm with
      | .error .StaticModeViolation => .agree "static"
      | _ => differ (describeExit .static)
    | some (.error .trap) =>
      match evm with
      | .error .InvalidInstruction => .agree "trap"
      | _ => differ (describeExit .trap)
    | some (.error .oob) =>
      match evm with
      | .error .InvalidMemoryAccess => .agree "oob"
      | _ => differ (describeExit .oob)

/-- `compare`, for a target that may have no model. -/
def compareModel (evm : Except ExecutionException (ExecutionResult State))
    (model : Option (Option (Except (Exit World) (ByteArray × World)))) : Verdict :=
  match model, evm with
  | some m, _ => compare evm m
  | none, .error .OutOfGass | none, .error .OutOfFuel => .outOfGas
  | none, .error .StackOverflow => .stackOverflow
  | none, _ => .noModel

/-! ## The interpreter -/

/-- How a run of the model, or of the interpreter, ends. -/
abbrev Outcome := Option (Except (Exit World) (ByteArray × World))

/-- What `P1` observes of an outcome: a panic is the revert it is on the EVM. -/
inductive Observed where
  | diverges
  | success (out : ByteArray) (accounts : AccountMap) (logs : LogSeries)
  | revert (data : ByteArray)
  | static
  | trap
  | oob

def observe : Outcome → Observed
  | none => .diverges
  | some (.ok (out, w)) | some (.error (.stop out w)) => .success out w.accounts w.logs
  | some (.error (.revert data)) => .revert data
  | some (.error (.panic code)) => .revert (panicData code)
  | some (.error .static) => .static
  | some (.error .trap) => .trap
  | some (.error .oob) => .oob

/-- Bytes as hex, cut short past 64 digits. -/
def shortHex (bytes : ByteArray) : String :=
  let digits := Ethereum.toHex bytes
  if digits.length ≤ 72 then digits else s!"{digits.take 64}…({bytes.size} bytes)"

def Observed.describe : Observed → String
  | .diverges => "does not terminate"
  | .success out .. => s!"returns {shortHex out}"
  | .revert data => s!"reverts with {shortHex data}"
  | .static => "fails on a write under a static call"
  | .trap => "traps"
  | .oob => "reads past the return data"

/-- Where the interpreter's outcome differs from the model's, if it does. -/
def differs (model interp : Outcome) : Option String :=
  match observe model, observe interp with
  | .success mo ma ml, .success io ia il =>
    if mo != io then some s!"model returns {shortHex mo}, interpreter {shortHex io}"
    else if ma != ia then
      some s!"accounts differ: {accountsDiff ma ia "model" "interpreter"}"
    else if ml != il then some s!"logs differ: model {repr ml}, interpreter {repr il}"
    else none
  | .revert md, .revert id => if md == id then none else
      some s!"model reverts with {shortHex md}, interpreter with {shortHex id}"
  | .diverges, .diverges | .static, .static | .trap, .trap | .oob, .oob => none
  | m, i => some s!"model {m.describe}, interpreter {i.describe}"

/-- The error the specification gave up with, as the line that reports it shows it. -/
def describeSpec : Fe.Sem.SpecError → String
  | .unsupported what => s!"unsupported {what}"
  | .malformed what => s!"malformed {what}"

/-- How the interpreter's run went, for one creation or call. -/
inductive Interp where
  /-- Not run: the contract has no IR, or the bytecode ran out of gas or of stack. -/
  | notRun
  /-- The specification gave up. -/
  | spec (why : String)
  /-- It ran: how it compares with the bytecode, and where it differs from the model. -/
  | ran (bytecode : Verdict) (model : Option String) (shown : String)

/-- The steps each call the entry code makes may take in the interpreter. -/
def interpFuel : Nat := 10000000

/-- The interpreter's outcome: a Fe outcome, or the error the specification gave up with.  A run
    with no result is one that did not finish within its bound on the steps of a call, or one whose
    host diverged (`alloc` past `2 ^ 256`, the feed run dry), which the model's would too. -/
def interpOutcome : Option (Except (Exit World) (Except Fe.Sem.SpecError ByteArray × World)) →
    Except String Outcome
  | none => .error "no result: more steps in a call than the bound, or the host diverges"
  | some (.error e) => .ok (some (.error e))
  | some (.ok (.error e, _)) => .error (describeSpec e)
  | some (.ok (.ok out, w)) => .ok (some (.ok (out, w)))

/-- Compare the interpreter's run, if there is one, with the bytecode's and the model's. -/
def compareInterp (evm : Except ExecutionException (ExecutionResult State))
    (model : Option Outcome) (interp : Option (Unit → Except String Outcome)) : Interp :=
  match evm, interp with
  | .error .OutOfGass, _ | .error .OutOfFuel, _ | .error .StackOverflow, _ | _, none => .notRun
  | _, some run =>
    match run () with
    | .error why => .spec why
    | .ok i => .ran (compare evm i "interpreter") (model.bind (differs · i)) (observe i).describe

/-! ## Tests -/

/-- An entry point: its selector, the canonical tuple type of its arguments as in a selector
    signature (empty when the compiler does not know it), and whether it takes value. -/
structure Arm where
  selector : Nat
  inputs : String
  payable : Bool

/-- What generated calls (`Fe/EVM/Generate.lean`) are made from: the constructor's argument
    types and the entry points. -/
structure Interface where
  init : String := "()"
  initPayable : Bool := false
  arms : List Arm := []

/-- A contract: its creation code without arguments, its runtime code without immutable
    fields, its exported model if the exporter exports it, and its interface.  `ir` is where the corpus driver
    wrote the contract's IR, `<ir>.ir.json`, or why it is not serialized, `<ir>.ir.refused`; empty
    when the interpreter is not run on the target.  `load` reads it into `spec`: the program, or
    why there is none. -/
structure Target where
  name : String
  creation : ByteArray
  runtime : ByteArray
  model : Option ContractModel
  interface : Interface := {}
  ir : String := ""
  spec : Option (Except String Fe.IR.Program) := none
  /-- The creation codes of the contracts the contract may deploy, by name. -/
  creations : List (String × ByteArray) := []
  /-- Whether the interpreter checks the machine's typing after every step (`runChecked`). -/
  checked : Bool := false
  /-- The steps each entry call may take in the interpreter. -/
  fuel : Nat := interpFuel

/-- Read the target's IR. -/
def Target.load (t : Target) : IO Target := do
  if t.ir.isEmpty then return t
  let json : System.FilePath := t.ir ++ ".ir.json"
  let refused : System.FilePath := t.ir ++ ".ir.refused"
  let spec ←
    if ← json.pathExists then
      pure (match Fe.IR.Program.ofJson (← IO.FS.readFile json) with
        | .ok prog => .ok prog
        | .error e => .error s!"the IR does not read: {e}")
    else if ← refused.pathExists then
      pure (.error s!"the serializer refused: {← IO.FS.readFile refused}")
    else pure (.error s!"no IR at {t.ir}")
  let fuel := ((← IO.getEnv "SPEC_FUEL").bind String.toNat?).getD interpFuel
  return { t with spec := some spec, checked := (← IO.getEnv "SPEC_CHECKED").isSome, fuel }

/-- The interpreter's runtime entry on the target, from the world `w`. -/
def Target.interpRuntime (t : Target) (I : Env) (w : World) :
    Option (Unit → Except String Outcome) :=
  match t.spec with
  | some (.ok prog) => some fun _ => interpOutcome
      ((specRuntime prog t.runtime.size t.creations t.checked t.fuel >>= fun r =>
        pure (r.map fun e => nomatch e)).exec I w)
  | _ => none

/-- The interpreter's deployment entry on the target, from the world `w`: the deployed code. -/
def Target.interpInit (t : Target) (I : Env) (w : World) :
    Option (Unit → Except String Outcome) :=
  match t.spec with
  | some (.ok prog) => some fun _ => interpOutcome
      ((specInit prog t.creation.size t.creations t.checked t.fuel >>= fun r =>
        pure (r.map (t.runtime ++ ·))).exec I w)
  | _ => none

/-- A Fe test: the selector that runs it, and the balance it starts with. -/
structure Test where
  name : String
  selector : Nat
  balance : Nat := 0

/-- One comparison. -/
structure Report where
  test : String
  target : String
  /-- `init`, or the calldata of the call. -/
  input : String
  verdict : Verdict
  interp : Interp := .notRun
  /-- The three outcomes, in a few words. -/
  outcomes : String := ""

/-- The EVM's outcome, cut short. -/
def describeEvmShort : Except ExecutionException (ExecutionResult State) → String
  | .error e => s!"halts with {repr e}"
  | .ok (.success _ out) => s!"returns {shortHex out}"
  | .ok (.revert _ out) => s!"reverts with {shortHex out}"

/-- The three outcomes of a creation or call, in a few words. -/
def outcomes (evm : Except ExecutionException (ExecutionResult State)) (model : Option Outcome)
    (interp : Interp) : String :=
  let i := match interp with
    | .notRun => "not run"
    | .spec why => s!"gives up: {why}"
    | .ran _ _ shown => shown
  let m := model.elim "none: not exported" (observe · |>.describe)
  s!"EVM {describeEvmShort evm} | model {m} | interp {i}"

/-- The comparisons of some calls, counted. -/
structure Tally where
  agree : Nat := 0
  disagree : Nat := 0
  outOfGas : Nat := 0
  stackOverflow : Nat := 0
  /-- The interpreter agrees with the model and the bytecode, which agree. -/
  agree3 : Nat := 0
  /-- The interpreter disagrees with the model or the bytecode. -/
  interpDisagree : Nat := 0
  /-- The specification gave up. -/
  spec : Nat := 0
  /-- The target has no model: compared with the interpreter only. -/
  noModel : Nat := 0
  /-- On a target without a model, the interpreter agrees with the bytecode. -/
  agree2 : Nat := 0
  /-- The interpreter did not run: the contract has no IR, or the harness could not rebuild the
      frame. -/
  notRun : Nat := 0

/-- Count the report, and print its lines: `DISAGREE` when the model and the bytecode disagree,
    `DIFF3` when the interpreter disagrees with either, `SPEC` when it gives up. -/
def Tally.add (t : Tally) (fixture : String) (r : Report) : IO Tally := do
  let at_ := s!"{fixture}::{r.test} {r.target} {r.input}"
  let mut t := t
  match r.verdict with
  | .agree _ => t := { t with agree := t.agree + 1 }
  | .outOfGas => return { t with outOfGas := t.outOfGas + 1 }
  | .stackOverflow => return { t with stackOverflow := t.stackOverflow + 1 }
  | .disagree why =>
    t := { t with disagree := t.disagree + 1 }
    IO.println s!"DISAGREE {at_}: {why}"
  | .noModel => t := { t with noModel := t.noModel + 1 }
  let modelBytecode := match r.verdict with
    | .disagree why => [s!"model≠bytecode ({why})"]
    | _ => []
  match r.interp with
  | .notRun => return { t with notRun := t.notRun + 1 }
  | .spec why =>
    IO.println s!"SPEC {at_}: {why}"
    return { t with spec := t.spec + 1 }
  | .ran bytecode model _ =>
    let pairs := (model.map (s!"interp≠model ({·})")).toList
      ++ (match bytecode with
        | .disagree why => [s!"interp≠bytecode ({why})"]
        | _ => [])
    if pairs.isEmpty then
      return match r.verdict with
        | .noModel => { t with agree2 := t.agree2 + 1 }
        | _ => if modelBytecode.isEmpty then { t with agree3 := t.agree3 + 1 } else t
    IO.println s!"DIFF3 {at_}: {"; ".intercalate (pairs ++ modelBytecode)}"
    return { t with interpDisagree := t.interpDisagree + 1 }

def Tally.fields (t : Tally) : String :=
  s!"agree={t.agree} disagree={t.disagree} outOfGas={t.outOfGas} stackOverflow={t.stackOverflow} agree3={t.agree3} interpDisagree={t.interpDisagree} spec={t.spec} notRun={t.notRun} noModel={t.noModel} agree2={t.agree2}"

/-- Print a line `NOIR <fixture> <target>: <why>` for each target meant to run on the
    interpreter that has no program. -/
def reportIr (fixture : String) (targets : List Target) : IO Unit := do
  for t in targets do
    if let some (.error why) := t.spec then
      IO.println s!"NOIR {fixture} {t.name}: {why.replace "\n" " "}"

def isPrefix (p b : ByteArray) : Bool := p.size ≤ b.size && b.extract 0 p.size == p

/-- The gas a test runs with, and the bound on the steps of a contract's frame. -/
def testGas : Nat := 1000000000
def stepBound : Nat := 100000000

/-- The environment the frames of a test start from: an Osaka block, the fork Fe compiles for,
    so that `CLZ` runs. -/
def env : ExecutionEnv := { (default : ExecutionEnv) with header.fork := .Osaka }

/-- The bound on the steps of the test's own frame.  A test that runs longer is cut short: the
    interpreter takes minutes for it, and the calls it made so far are compared. -/
def testSteps : Nat := 2000000

/-- Compare the model, and the interpreter, with what the EVM did at one event of the test's
    frame.  Returns the report, if the event concerns a target, and the contract a creation
    deployed. -/
def check (test : String) (targets : List Target) (deployed : List (AccountAddress × Target)) :
    Event → Option Report × Option (AccountAddress × Target)
  | .gas _ => (none, none)
  | .boundary op s cost after =>
    let x := after.machineState.stack.getD 0 ⟨0⟩
    match message? op s with
    | some m =>
      if op != .CALL && op != .STATICCALL then (none, none) else
      match deployed.find? (·.1 == m.t), messageFrame s m with
      | some (_, target), some (σ, g, A, I) =>
        let r := run (fresh σ s.σ₀ g A I) stepBound
        let feed := r.events.toList.map supply
        let w := World.init σ A feed
        let model := target.model.map (·.runtime.exec I w)
        -- The frame as rebuilt here must end as the one `Θ` ran inside the test.
        let made : Bool := match r.result with
          | .ok (.success s' _) => x == ⟨1⟩ && after.accountMap == s'.accountMap
          | _ => x == ⟨0⟩
        let report : Report :=
          if made then
            let interp := compareInterp r.result model (target.interpRuntime I w)
            ⟨test, target.name, Ethereum.toHex m.input, compareModel r.result model, interp,
              outcomes r.result model interp⟩
          else
            ⟨test, target.name, Ethereum.toHex m.input,
              .disagree s!"harness: the rebuilt frame {describeEvm r.result}, the test's call gave {x.toNat}",
              .notRun, ""⟩
        (some report, none)
      | _, _ => (none, none)
    | none =>
      match creationFrame op s cost with
      | none => (none, none)
      | some (a, init, σ, g, A, I) =>
        match targets.find? (isPrefix ·.creation init) with
        | none => (none, none)
        | some target =>
          let args := init.extract target.creation.size init.size
          let r := run (fresh σ s.σ₀ g A I) stepBound
          let feed := r.events.toList.map supply
          let w := World.init σ A feed
          let model := target.model.map fun model =>
            (model.init args >>= fun tail => pure (target.runtime ++ tail)).exec I w
          let made : Bool := match r.result with
            | .ok (.success _ _) => x == ⟨0⟩ || x == .ofNat a.val
            | _ => x == ⟨0⟩
          let input := s!"init {Ethereum.toHex args}"
          let report : Report :=
            if made then
              let interp := compareInterp r.result model (target.interpInit I w)
              ⟨test, target.name, input, compareModel r.result model, interp,
                outcomes r.result model interp⟩
            else
              ⟨test, target.name, input,
                .disagree s!"harness: the rebuilt creation {describeEvm r.result}, the test's gave {x.toNat}",
                .notRun, ""⟩
          (some report, if x == ⟨0⟩ then none else some (AccountAddress.ofUInt256 x, target))

/-- Deploy the tests' object with `suite`, its init code, and run the test, comparing at every
    call on a target.  Returns the reports and how the test ended. -/
def runTest (targets : List Target) (suite : ByteArray) (t : Test) : Array Report × String := Id.run do
  let caller : AccountAddress := Fin.ofNat _ 0xca11e7
  let self : AccountAddress := Fin.ofNat _ 0x7e57
  let σ : AccountMap := (∅ : AccountMap)
    |>.insert caller { (default : Account) with balance := .ofNat 1000000000 }
    |>.insert self { (default : Account) with nonce := ⟨1⟩, balance := .ofNat t.balance }
  let I : ExecutionEnv :=
    { env with codeOwner := self, sender := caller, source := caller, code := suite, perm := true }
  match Ξ σ σ (.ofNat testGas) default I with
  | .ok (.success (σ, _, _) code) =>
    let σ := σ.insert self { σ.getD self default with code := code }
    let calldata := (UInt256.ofNat t.selector).toByteArray.extract 28 32
    let r := run (fresh σ σ testGas default { I with code := code, calldata := calldata }) testSteps
    let mut deployed : List (AccountAddress × Target) := []
    let mut reports : Array Report := #[]
    for event in r.events do
      let (report, created) := check t.name targets deployed event
      if let some report := report then reports := reports.push report
      if let some created := created then deployed := created :: deployed
    return (reports, describeEvm r.result)
  | other =>
    let ended := match other with
      | .error e => s!"halts with {repr e}"
      | .ok (.revert _ out) => s!"reverts with {Ethereum.toHex out}"
      | .ok (.success _ _) => ""
    return (#[], s!"is not deployed: its init code {ended}")

/-- Run every test of a fixture and print one line per comparison that does not agree, one per
    test, and a total. -/
def main (fixture : String) (targets : List Target) (suite : ByteArray) (tests : List Test) :
    IO Unit := do
  let targets ← targets.mapM Target.load
  let mut tally : Tally := {}
  let mut covered : List String := []
  for t in tests do
    let (reports, ended) := runTest targets suite t
    IO.println s!"TEST {fixture}::{t.name} {ended}; {reports.size} compared"
    for r in reports do
      if let .agree _ := r.verdict then
        if !covered.contains r.target then covered := r.target :: covered
      IO.println s!"CALL3 {fixture}::{r.test} {r.target} {r.input}: {r.outcomes}"
      tally ← tally.add fixture r
  IO.println s!"DIFF {fixture} tests={tests.length} {tally.fields} targets={targets.length} covered={covered.length}"

end Fe.EVM.Diff
