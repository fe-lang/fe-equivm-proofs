import Fe.Sonatina.FrameSafe
import Fe.Sonatina.Diff

/-!
# `FrameSafe`, tested

`FrameSafe s` says the machine IR with its spills (`Sidecar.spilledModel` under
`Sidecar.spillPlan`) ends as the machine IR does.  Where no proof of it exists, running the two
models on the same inputs is the evidence: `frameSafeCalldata` runs both on call data and
counts the runs, the instrumented runs that panic with `spillClobbered` (a word changed while
the bytes still reload it: the plan or the protection rule is wrong, or the bytes are), and the
other disagreements (the bytes, if they match the instrumented model, would differ from the
machine IR: a miscompile).  `Sidecar.pairedModel` runs both inside the differential harnesses
of `Fe/EVM/Diff.lean`, where a disagreement shows as a revert with a payload that names it.
`scripts/frame_safe_diff.sh` runs them.
-/

namespace Fe.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- `EndsAs`, decided, but for the recorded calls, which have no equality to decide: `none`
    when the first run ends as the second, else how they differ. -/
def endsAsDiff (a b : Option (Except (Exit World) (ByteArray × World))) : Option String :=
  let same (out out' : ByteArray) (w w' : World) : Option String :=
    if out != out' then some "return data"
    else if w.accounts != w'.accounts then some "accounts"
    else if w.logs != w'.logs then some "logs"
    else if w.calls.length != w'.calls.length then some "calls"
    else none
  match a, b with
  | none, none => none
  | some (.ok (o, w)), some (.ok (o', w')) | some (.ok (o, w)), some (.error (.stop o' w'))
  | some (.error (.stop o w)), some (.ok (o', w'))
  | some (.error (.stop o w)), some (.error (.stop o' w')) => same o o' w w'
  | some (.error (.revert d)), some (.error (.revert d')) =>
    if d == d' then none else some "revert data"
  | some (.error (.panic c)), some (.error (.panic c')) => if c == c' then none else some "panic"
  | some (.error (.panic c)), some (.error (.revert d)) =>
    if panicData c == d then none else some "panic"
  | some (.error .static), some (.error .static) | some (.error .trap), some (.error .trap)
  | some (.error .oob), some (.error .oob) => none
  | _, _ => some "outcome"

/-- How a run ends, in a word. -/
def describeEnd : Option (Except (Exit World) (ByteArray × World)) → String
  | none => "does not terminate"
  | some (.ok (o, _)) => s!"returns {Ethereum.toHex o}"
  | some (.error e) => Diff.describeExit e

/-- What the two models do on one run: agree, the instrumented model panics with
    `spillClobbered`, or they differ. -/
inductive PairVerdict where
  | agree
  | clobber
  | differ (how : String)

def pairVerdict (machine spilled : Option (Except (Exit World) (ByteArray × World))) :
    PairVerdict :=
  match spilled with
  | some (.error (.panic c)) => if c == spillClobbered then .clobber else
    match endsAsDiff machine spilled with
    | none => .agree
    | some how => .differ s!"{how}: machine {describeEnd machine}, spilled {describeEnd spilled}"
  | _ =>
    match endsAsDiff machine spilled with
    | none => .agree
    | some how => .differ s!"{how}: machine {describeEnd machine}, spilled {describeEnd spilled}"

/-- Both models run beside each other: the machine IR's run where the instrumented model ends
    as it does, else a revert whose payload says how they differ (`SPILL CLOBBER` or
    `SPILL DIFFER …`). -/
def Sidecar.pairedModel (s : Sidecar) : ContractModel :=
  let init := s.spillPlan "init"
  let runtime := s.spillPlan "runtime"
  let spilled := s.spilledModel fun n => if n == "init" then init else runtime
  let pair (m x : FeM ByteArray) : FeM ByteArray := fun I w =>
    match pairVerdict (m.exec I w) (x.exec I w) with
    | .agree => m I w
    | .clobber => ExceptT.mk (some (.error (.revert "SPILL CLOBBER".toUTF8)))
    | .differ how => ExceptT.mk (some (.error (.revert s!"SPILL DIFFER {how}".toUTF8)))
  { init := fun args => pair ((s.model .machine).init args) (spilled.init args)
    runtime := pair (s.model .machine).runtime spilled.runtime }

/-- `targetsOf` with the paired model of each sidecar for its target. -/
def spillTargetsOf (file : String) (sidecars : List (String × Diff.Interface)) :
    IO (List Diff.Target) :=
  sidecars.filterMapM fun (path, interface) => do
    match Parse.parseSidecar (← IO.FS.readFile path) with
    | .ok s => return some { s.target interface .machine with model := s.pairedModel }
    | .error e =>
      IO.println s!"UNSUPPORTED {file}::{path}: {e}"
      return none

/-- The plan of each section of the sidecar, a line per function: its spilled values, their
    reloads, and whether the reload-liveness sets satisfy their equations. -/
def printPlan (name : String) (s : Sidecar) : IO Unit := do
  for (sec, _) in Check.entries s do
    let some code := s.section? sec | continue
    let some low := code.lowering | continue
    for (fn, p) in s.spillPlan sec do
      let some f := (low.machine.instrument (s.spillPlan sec)).func? fn | continue
      let reloads := p.foldl (· + ·.reloads.length) 0
      let unreloaded := (p.filter (·.reloads.isEmpty)).length
      IO.println s!"PLAN {name} {sec} {fn} spills={p.length} reloads={reloads} \
        unreloaded={unreloaded} closed={f.liveClosed p (f.reloadLive p)}"

/-- Run the machine IR and the instrumented model of the sidecar's runtime on each call data,
    at an account with no state in an Osaka block, and print a line per run that does not agree
    and a total. -/
def frameSafeCalldata (name path : String) (inputs : List (String × ByteArray))
    (prefix_ : ByteArray := .empty) : IO Unit := do
  let s ← IO.ofExcept ((Parse.parseSidecar (← IO.FS.readFile path)).mapError (s!"{path}: " ++ ·))
  printPlan name s
  -- The plan, found once: the model finds it on each run otherwise.
  let plan := s.spillPlan "runtime"
  let spilled := s.spilledModel fun n => if n == "runtime" then plan else s.spillPlan n
  let mut agree := 0
  let mut clobber := 0
  let mut differ := 0
  -- Each line also goes to `FRAMESAFE_LOG`, if set, as it is found: `#eval` prints at the end.
  let log ← IO.getEnv "FRAMESAFE_LOG"
  let say (line : String) : IO Unit := do
    IO.println line
    if let some path := log then
      IO.FS.withFile path .append fun h => h.putStrLn line
  for (kind, d) in inputs do
    let I : ExecutionEnv := { Diff.env with calldata := prefix_ ++ d }
    let w := World.init ∅ default
    let m := (s.model .machine).runtime.exec I w
    match pairVerdict m (spilled.runtime.exec I w) with
    | .agree => agree := agree + 1
    | .clobber =>
      clobber := clobber + 1
      say s!"CLOBBER {name} {kind} {Ethereum.toHex d}: machine {describeEnd m}"
    | .differ how =>
      differ := differ + 1
      say s!"DIFFER {name} {kind} {Ethereum.toHex d}: {how}"
    if let some path := log then
      IO.FS.withFile path .append fun h => h.putStrLn s!"RUN {name} {kind}"
  say s!"FRAMESAFE {name} runs={inputs.length} agree={agree} clobber={clobber} \
    differ={differ}"

end Fe.Sonatina
