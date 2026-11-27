import Fe.Sonatina.Stage3.Place.Check
import Fe.Sonatina.Steps.Machine

/-!
# The S14 check on sidecars

`lake lean scripts/Place.lean -- --run scripts/Place.lean SIDECAR SECTION [RECORD.json]`: the
first rule `Place.diagnose` reports for the section, or `accepted`.  The record is read from an
interim JSON form (`{"arena": n, "funcs": [{"name", "allocas": [[v, "scratch"|"stable", w]],
"mallocs": [[v, "fixed", base] | [v, "heap", min, exact|null, update]]}]}`) until the
compiler's placement record exists; without one, the record is empty.
-/

open Lean Fe.Sonatina Fe.Sonatina.Stage3.Place Fe.Sonatina.H

def readRecord (j : Json) : Except String Record := do
  let funcs ← (← j.getObjValAs? (Array Json) "funcs").toList.mapM fun f => do
    let allocas ← (← f.getObjValAs? (Array Json) "allocas").toList.mapM fun a => do
      let x ← a.getArrVal? 0 >>= (·.getNat?)
      let k ← a.getArrVal? 1 >>= (·.getStr?)
      let w ← a.getArrVal? 2 >>= (·.getNat?)
      return (x, if k == "stable" then Loc.stable w else Loc.scratch w)
    let mallocs ← (← f.getObjValAs? (Array Json) "mallocs").toList.mapM fun m => do
      let x ← m.getArrVal? 0 >>= (·.getNat?)
      let k ← m.getArrVal? 1 >>= (·.getStr?)
      if k == "fixed" then return (x, Malloc.fixed (← m.getArrVal? 2 >>= (·.getNat?)) .terminal)
      let mb ← m.getArrVal? 2 >>= (·.getNat?)
      let eb := (m.getArrVal? 3 >>= (·.getNat?)).toOption
      let up ← m.getArrVal? 4 >>= (·.getBool?)
      return (x, Malloc.heap mb eb up)
    return ({ name := ← f.getObjValAs? String "name", allocas, mallocs } : FuncRec)
  return { arenaBase := ← j.getObjValAs? Nat "arena", funcs }

def runOne (path sec : String) (rec : Record) : IO Unit := do
  let text ← IO.FS.readFile path
  let .ok h := H.Parse.objectOfSidecar text | IO.println s!"{path} {sec}: no H object"
  let .ok s := Parse.parseSidecar text | IO.println s!"{path} {sec}: no sidecar"
  let src := if sec == "init" then h.init else h.runtime
  let low := s.asLowered.machineOf sec
  let efp := ((s.section? sec).bind (·.lowering)).bind (·.entryFreePtr)
  let t0 ← IO.monoMsNow
  let d := diagnose src low efp (rec.withHints src low)
  let t1 ← IO.monoMsNow
  IO.println s!"{path} {sec}: {(d.getD "accepted")} ({t1 - t0} ms)"

def main (args : List String) : IO Unit := do
  let rec ← match args[2]? with
    | some (p : String) => match Json.parse (← IO.FS.readFile p) >>= readRecord with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    | none => pure { arenaBase := 0, funcs := [] }
  runOne (args[0]!) (args[1]!) rec
