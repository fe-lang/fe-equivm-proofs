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

/-- `--manifest FILE FEP T265 RECS`: one line per section, `label<TAB>sidecar<TAB>section<TAB>record`,
    the sidecar path starting with `FEP/` or `T265/` (replaced by the two corpus roots) and the
    record a file under `RECS`; prints `label<TAB>sidecar<TAB>section<TAB>verdict`. -/
def manifest (file fep t265 recs : String) : IO Unit := do
  for line in (← IO.FS.readFile file).splitOn "\n" do
    match line.splitOn "\t" with
    | [label, sc, sec, recFile] =>
      let path := (sc.replace "FEP/" (fep ++ "/")).replace "T265/" (t265 ++ "/")
      let text ← IO.FS.readFile path
      let recE := Json.parse (← IO.FS.readFile (recs ++ "/" ++ recFile)) >>= readRecord
      let verdict := match recE, H.Parse.objectOfSidecar text, Parse.parseSidecar text with
        | .error e, _, _ => s!"no record: {e}"
        | .ok rec, .ok h, .ok s =>
          let src := if sec == "init" then h.init else h.runtime
          let low := s.asLowered.machineOf sec
          let efp := ((s.section? sec).bind (·.lowering)).bind (·.entryFreePtr)
          (diagnose src low efp (rec.withHints src low)).getD "accepted"
        | _, .error e, _ => s!"no H object: {e}"
        | _, _, .error e => s!"no sidecar: {e}"
      IO.println s!"{label}\t{sc}\t{sec}\t{verdict}"
    | _ => pure ()

def main (args : List String) : IO Unit := do
  if args[0]? == some "--manifest" then
    return ← manifest args[1]! args[2]! args[3]! args[4]!
  let rec ← match args[2]? with
    | some (p : String) => match Json.parse (← IO.FS.readFile p) >>= readRecord with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    | none => pure { arenaBase := 0, funcs := [] }
  runOne (args[0]!) (args[1]!) rec
