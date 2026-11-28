import Fe.Sonatina.Stage3.Place.Check
import Fe.Sonatina.Stage3.Place.Read
import Fe.Sonatina.Steps.Machine

/-!
# The S14 check on sidecars

`lake lean scripts/Place.lean -- --run scripts/Place.lean SIDECAR SECTION`: the first rule
`Place.diagnose` reports for the section of a version-6 sidecar under its placement record
(`placementOf`), or `accepted`, or why the record cannot be read (`reader: …`); then how the
record's `alloca` words compare with the sizes of the `alloca`s' types (`words`).

`--manifest FILE FEP T265`: the same for each line `label<TAB>sidecar<TAB>section` of `FILE`, the
sidecar path starting with `FEP/` or `T265/` (replaced by the two corpus roots); prints
`label<TAB>sidecar<TAB>section<TAB>verdict<TAB>words`.
-/

open Lean Fe.Sonatina Fe.Sonatina.Stage3.Place Fe.Sonatina.H

/-- Each source `alloca` whose record words are not its type's size in words, and each record
    `alloca` with no source `alloca`: `ok N` (N compared) or the mismatches. -/
def wordsReport (src : HSection) (pl : Placement) : String := Id.run do
  let mut bad : List String := []
  let mut n := 0
  for f in src.module.funcs do
    let ws := (pl.words.lookup f.name).getD []
    let sites := f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst, s.dsts with
      | .base (.alloca t), [(x, _)] => some (x, t)
      | _, _ => none
    for (x, t) in sites do
      n := n + 1
      let ty := (sizeOf src.module.structs sizeFuel t).map ((· + 31) / 32)
      match ws.lookup x with
      | some w => if ty != some w then bad := bad ++ [s!"{f.name} v{x} record {w} type {ty}"]
      | none => bad := bad ++ [s!"{f.name} v{x} not in the record"]
    for (x, _) in ws do
      unless sites.any (·.1 == x) do bad := bad ++ [s!"{f.name} v{x} recorded, no alloca"]
  return if bad.isEmpty then s!"words ok {n}" else s!"words {bad.length} of {n}: {"; ".intercalate bad}"

/-- The verdict and the words report of section `sec` of the sidecar `text`. -/
def verdictOf (text sec : String) : String × String :=
  match placementOf text sec, H.Parse.objectOfSidecar text, Parse.parseSidecar text with
  | .error e, _, _ => (s!"reader: {e}", "-")
  | .ok pl, .ok h, .ok s =>
    let src := if sec == "init" then h.init else h.runtime
    let low := s.asLowered.machineOf sec
    let efp := ((s.section? sec).bind (·.lowering)).bind (·.entryFreePtr)
    ((diagnose src low efp (pl.record.withHints src low)).getD "accepted", wordsReport src pl)
  | _, .error e, _ => (s!"no H object: {e}", "-")
  | _, _, .error e => (s!"no sidecar: {e}", "-")

def manifest (file fep t265 : String) : IO Unit := do
  for line in (← IO.FS.readFile file).splitOn "\n" do
    match line.splitOn "\t" with
    | [label, sc, sec] =>
      let path := (sc.replace "FEP/" (fep ++ "/")).replace "T265/" (t265 ++ "/")
      let (v, w) := verdictOf (← IO.FS.readFile path) sec
      IO.println s!"{label}\t{sc}\t{sec}\t{v}\t{w}"
    | _ => pure ()

def main (args : List String) : IO Unit := do
  if args[0]? == some "--manifest" then
    return ← manifest args[1]! args[2]! args[3]!
  let path := args[0]!
  let sec := args[1]!
  let t0 ← IO.monoMsNow
  let (v, w) := verdictOf (← IO.FS.readFile path) sec
  let t1 ← IO.monoMsNow
  IO.println s!"{path} {sec}: {v} ({t1 - t0} ms)\n{w}"
