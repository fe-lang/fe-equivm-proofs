import Fe.Sonatina.FrameSafe
import Fe.Sonatina.Parse

/-!
Runs the sidecar reader and the byte checker (`Check.check`, `Check.checkSpills`) over every
`*.sidecar.json` under the directory `SWEEP_DIR` names, searched recursively, interpreted, and
prints one tab-separated line per sidecar and per section:

- `UNREAD <file> <error>`: the reader rejects the sidecar;
- `LEVELS <file> postopt=<ok|error> <section>.source=<ok|error> …`: whether the module after
  optimization and each section's IR after the pipeline are in the subset (the checker reads
  neither), with the first error;
- `SECTION <file> <section> check=<verdict> checkSpills=<verdict>`: the verdict of each section,
  `check` under the empty plan and only without memory spills, `checkSpills` under the walked
  plan (`CodeSection.spillPlan`);
- `RECORD <file> <section> <disagreement>`: where the lowering record's spill stores and reloads
  disagree with the walked plan, by block;
- `SIDECAR <file> check=<bool> checkSpills=<bool> fixedSlots=<bool>`: the verdicts of the whole
  sidecar, as the certificates evaluate them.

Run with `SWEEP_DIR=<dir> lake env lean scripts/DialectSweep.lean`.
-/

open Fe.Sonatina Lean

/-- The block a code point is in; the entry block for the function's entry. -/
def Fe.Sonatina.CodePoint.blockOf (entry : Nat) : CodePoint → Nat
  | .entry => entry
  | .before b _ | .after b _ | .case b _ _ => b

/-- Where the record's spill points and the walked plan disagree, by block, per function. -/
def disagreements (code : CodeSection) (plan : SpillPlan) : List String := Id.run do
  let some low := code.lowering | return []
  let mut out := []
  for hint in low.funcs do
    let some p := plan.lookup hint.name | continue
    let some f := low.machine.func? hint.name | continue
    let entry := (f.blocks.head?.map (·.id)).getD 0
    let fi := f.instrument p.words
    let reloads := norm (hint.spills.flatMap fun sp =>
      sp.reloads.map fun pt => (sp.value, pt.blockOf entry))
    let walked := norm (p.flatMap fun sp => sp.reloads.map fun (b, _) => (sp.value, b))
    let stores := norm (hint.spills.flatMap fun sp => match p.words.lookup sp.value with
      | some w => sp.stores.map fun pt => (w, pt.blockOf entry)
      | none => [])
    let stored := norm (fi.blocks.flatMap fun b =>
      b.body.filterMap fun s => (storedValue fi p.words b s).map fun (w, _) => (w, b.id))
    for (what, r, m) in [("reloads (value, block)", reloads, walked),
        ("stores (word, block)", stores, stored)] do
      unless r == m do
        out := out ++ [s!"{hint.name} {what}: record only {r.filter (!m.contains ·)}, \
          plan only {m.filter (!r.contains ·)}"]
  return out
where
  norm (xs : List (Nat × Nat)) : List (Nat × Nat) :=
    (xs.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)).eraseDups

/-- The sidecars under a directory, recursively, sorted. -/
partial def sidecars (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← sidecars e.path)
    else if e.fileName.endsWith ".sidecar.json" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

def say : Except String Unit → String
  | .ok () => "accepted"
  | .error e => s!"rejected: {e}"

def okOr {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => s!"error: {e}"

#eval show IO Unit from do
  let some dir ← IO.getEnv "SWEEP_DIR" | throw (IO.userError "SWEEP_DIR is not set")
  for path in ← sidecars dir do
    let text ← IO.FS.readFile path
    match Parse.parseSidecar text with
    | .error e => IO.println s!"UNREAD\t{path}\t{e}"
    | .ok s =>
      -- The levels the checker does not read, with the reader's first error.
      let json := (Json.parse text).toOption.getD .null
      let ir := (json.getObjValAs? String "ir").toOption.getD ""
      let (_, moduleLines) := Parse.splitObjects (Parse.lines ir)
      let mut levels := s!"postopt={okOr (Parse.parseLines moduleLines)}"
      for sec in (json.getObjValAs? (Array Json) "sections").toOption.getD #[] do
        let name := (sec.getObjValAs? String "name").toOption.getD "?"
        let src := ((sec.getObjVal? "lowering").bind (·.getObjValAs? String "source_ir"))
        levels := levels ++ s!"\t{name}.source={okOr (src.bind Parse.parseModule)}"
      IO.println s!"LEVELS\t{path}\t{levels}"
      let plans := (Check.entries s).map fun (n, _) => (n, s.spillPlan n)
      let plan := fun n => (plans.lookup n).getD []
      for (name, fn) in Check.entries s do
        let some code := s.section? name | continue
        let spills := !(code.lowering.map (·.funcs.all (·.spills.isEmpty))).getD true
        let plain := match Check.checkSection code fn [] with
          | .ok () => if spills then .error "memory spills" else .ok ()
          | e => e
        let withSpills := if spills then Check.checkSection code fn (plan name) else plain
        IO.println s!"SECTION\t{path}\t{name}\tcheck={say plain}\tcheckSpills={say withSpills}"
        if spills then
          for d in disagreements code (plan name) do
            IO.println s!"RECORD\t{path}\t{name}\t{d}"
      IO.println s!"SIDECAR\t{path}\tcheck={Check.check s}\tcheckSpills={Check.checkSpills s}\t\
        fixedSlots={fixedSlotsSafe s plan}"
