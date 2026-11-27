import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Parse

/-!
# Tests of the sidecar reader's records

`ReadTests/gen.py` writes mutations of the record of a real sidecar's runtime section
(`SccpPruneTests/real_is_null_O1.sidecar.json`) and `ReadTests/cases.txt`, each with the error
the reader must give it: a version-5 lowering without `machine_steps` or with a `null` one, a
record in a version-4 sidecar, a malformed field, an unknown step kind, a key the writer does
not write (in the record, a pass, a step, a function step, a snapshot, a summary, the facts, the
SCCP and GVN facts, an inserted phi, a finite loop), a key it always writes missing, a function
twice in the lowered functions or in a step.  A version-4 sidecar without a record reads, with
the empty record.  Evaluated at elaboration, not proved.
-/

namespace Fe.Sonatina.Steps.ReadTests

open Lean

-- Each case of `cases.txt`: read with the error it names, or read if it names none.
#eval show IO Unit from do
  let dir := "Fe/Sonatina/Steps/ReadTests"
  for line in (← IO.FS.readFile s!"{dir}/cases.txt").splitOn "\n" do
    let [name, why] := line.splitOn "\t" | continue
    match Parse.parseSidecar (← IO.FS.readFile s!"{dir}/{name}.sidecar.json"), why with
    | .ok s, "" =>
      unless ["init", "runtime"].all fun n => (s.stepsOf n).lowered.isEmpty &&
          (s.stepsOf n).passes.isEmpty do
        throw (IO.userError s!"{name}: a record in a version-4 sidecar")
    | .ok _, _ => throw (IO.userError s!"{name}: read, expected {why}")
    | .error e, "" => throw (IO.userError s!"{name}: {e}")
    | .error e, _ =>
      unless (e.splitOn why).length > 1 do throw (IO.userError s!"{name}: {e}, expected {why}")

-- A fact key the record does not have is an error, `ranges` is kept unread.
#guard (Schemas.readFacts [("foo", "1")]).toOption.isNone
#guard (Schemas.readFacts [("ranges", "{}")]).toOption.map (·.unread) == some ["ranges"]

end Fe.Sonatina.Steps.ReadTests
