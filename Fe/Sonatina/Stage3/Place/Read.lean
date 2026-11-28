import Fe.Sonatina.Stage3.Place.Record
import Fe.Sonatina.Parse

/-!
# Reading the placement record from a sidecar (version 6)

`readPlacement` reads the placement record of a section from its `lowering` JSON, as the
compiler writes it (format note `s3/placement-record-format.md`), and `placementOf` from a
sidecar's text and a section name.  The record is untrusted (`Record.lean`): a misread record is
a different record, which then fails the check.  The reader is strict where the record is its
own: an `alloca`'s or malloc's object, a location, a placement, a fixed rule and a spill reserve
range must have exactly the keys the format note gives.

Field by field (`Record`, `FuncRec`):
- `arenaBase` is `arena_base`, `fixedSlots` is `fixed_slot_spills`; `funcs` are `funcs`, one per
  name (a name twice is an error).
- `allocas`: `{"scratch_abs": w}` is `Loc.scratch w`, `{"stable_abs": w}` is `Loc.stable w`.  A
  `{"stable_frame": w}` alloca lives in a dynamic frame, outside rule set S (S1), and has no
  `Loc`: reading it is an error, so the section has no record and is rejected.  (Leaving the
  alloca out would also be rejected, by S2's "no location", and its function's `dynFrame` by S1;
  the error does not depend on either.)
- `mallocs`: `{"heap": …}` is `Malloc.heap min_base exact_base update_free_ptr`,
  `{"fixed": {"base", "rule"}}` is `Malloc.fixed base rule`.
- `restoresFp` is `restores_free_ptr`, `lazyFrame` is `frame.lazy_frame`; `dynFrame` is
  `frame.stable == "dynamic_frame"`; `callPreserves` is the length of `frame.call_preserves`;
  `dynSpClamp` is whether some heap malloc of the function has `needs_dyn_sp_clamp` (the
  compiler's flag is per function and copied to each heap malloc); `reserves` are the spill
  reserves `spill_reserve.scratch` and `spill_reserve.stable` (unless `null`) as frame word
  ranges `[start, start + words)`, without the empty ones; `blockMap` is `lowered_blocks`.
- Not read into the `Record`: `allocas[].words` (the checker sizes an `alloca` by its type,
  `rangesOf`; `Placement.words` keeps them for the measurement to compare) and a heap malloc's
  `free_ptr_floor` (the translation accepts the heap template with and without the raise to
  `min_base`).  The hints and certificates are computed by `Record.withHints`.
-/

namespace Fe.Sonatina.Stage3.Place

open Lean

/-- A section's placement record, and per function each `alloca`'s words as the record gives
    them (`(value, words)`). -/
structure Placement where
  record : Record
  words : List (String × List (Nat × Nat))

/-- A frame word range `{"start": w, "words": n}`, as `[w, w + n)`. -/
def readRange (what : String) (j : Json) : Except String (Nat × Nat) := do
  Steps.Schemas.exactKeys what ["start", "words"] j
  let s ← j.getObjValAs? Nat "start"
  return (s, s + (← j.getObjValAs? Nat "words"))

def readFixedRule : String → Except String FixedRule
  | "terminal" => pure .terminal
  | "program" => pure .program
  | "exact_entry" => pure .exactEntry
  | "private_static" => pure .privateStatic
  | r => throw s!"unknown fixed malloc rule {r}"

/-- One function's record, and its `alloca`s' words. -/
def readFuncRec (f : Json) : Except String (FuncRec × List (Nat × Nat)) := do
  let name ← f.getObjValAs? String "name"
  let allocas ← (← f.getObjValAs? (Array Json) "allocas").toList.mapM fun a => do
    Steps.Schemas.exactKeys s!"alloca of {name}" ["value", "loc", "words"] a
    let x ← a.getObjValAs? Nat "value"
    let loc ← match ← Parse.variant (← a.getObjVal? "loc") with
      | ("scratch_abs", w) => Loc.scratch <$> w.getNat?
      | ("stable_abs", w) => Loc.stable <$> w.getNat?
      | ("stable_frame", w) =>
        throw s!"S1: alloca v{x} of {name} is in a dynamic frame (stable_frame {w.compress})"
      | (k, _) => throw s!"alloca v{x} of {name}: unknown location {k}"
    return ((x, loc), (x, ← a.getObjValAs? Nat "words"))
  let mallocs ← (← f.getObjValAs? (Array Json) "mallocs").toList.mapM fun m => do
    Steps.Schemas.exactKeys s!"malloc of {name}" ["value", "placement"] m
    let x ← m.getObjValAs? Nat "value"
    match ← Parse.variant (← m.getObjVal? "placement") with
    | ("heap", h) =>
      Steps.Schemas.exactKeys s!"heap malloc v{x} of {name}"
        ["min_base", "exact_base", "update_free_ptr", "needs_dyn_sp_clamp", "free_ptr_floor"] h
      let _ ← h.getObjValAs? (Option Nat) "free_ptr_floor"
      return ((x, Malloc.heap (← h.getObjValAs? Nat "min_base")
        (← h.getObjValAs? (Option Nat) "exact_base") (← h.getObjValAs? Bool "update_free_ptr")),
        ← h.getObjValAs? Bool "needs_dyn_sp_clamp")
    | ("fixed", p) =>
      Steps.Schemas.exactKeys s!"fixed malloc v{x} of {name}" ["base", "rule"] p
      return ((x, Malloc.fixed (← p.getObjValAs? Nat "base")
        (← readFixedRule (← p.getObjValAs? String "rule"))), false)
    | (k, _) => throw s!"malloc v{x} of {name}: unknown placement {k}"
  let frame ← f.getObjVal? "frame"
  let sr ← f.getObjVal? "spill_reserve"
  Steps.Schemas.exactKeys s!"spill_reserve of {name}" ["scratch", "stable"] sr
  let scratch ← readRange s!"scratch reserve of {name}" (← sr.getObjVal? "scratch")
  let stable ← match ← sr.getObjVal? "stable" with
    | .null => pure none
    | r => some <$> readRange s!"stable reserve of {name}" r
  let blockMap ← (← f.getObjValAs? (Array Json) "lowered_blocks").toList.mapM fun p => do
    let some #[s, l] := p.getArr?.toOption | throw s!"lowered_blocks of {name}: {p.compress}"
    return (← s.getNat?, ← l.getNat?)
  return ({ name
            allocas := allocas.map (·.1)
            mallocs := mallocs.map (·.1)
            restoresFp := ← f.getObjValAs? Bool "restores_free_ptr"
            dynFrame := (← Parse.variant (← frame.getObjVal? "stable")).1 == "dynamic_frame"
            lazyFrame := ← frame.getObjValAs? Bool "lazy_frame"
            callPreserves := (← frame.getObjValAs? (Array Json) "call_preserves").size
            dynSpClamp := mallocs.any (·.2)
            reserves := (scratch :: stable.toList).filter fun (lo, hi) => lo != hi
            blockMap := some blockMap }, allocas.map (·.2))

/-- The placement record of a section, from its `lowering` JSON (sidecar version 6). -/
def readPlacement (lowering : Json) : Except String Placement := do
  let fs ← (← lowering.getObjValAs? (Array Json) "funcs").toList.mapM readFuncRec
  Parse.distinctNames "placement record" (fs.map (·.1.name))
  return { record := { arenaBase := ← lowering.getObjValAs? Nat "arena_base"
                       funcs := fs.map (·.1)
                       fixedSlots := ← lowering.getObjValAs? Bool "fixed_slot_spills" }
           words := fs.map fun (fr, ws) => (fr.name, ws) }

/-- The placement record of section `sec` of the sidecar `text`, which must be of version 6
    (earlier versions have none). -/
def placementOf (text sec : String) : Except String Placement := do
  let json ← Json.parse text
  let version ← json.getObjValAs? Nat "version"
  unless version == 6 do throw s!"sidecar version {version} has no placement record"
  let some s := (← json.getObjValAs? (Array Json) "sections").find?
      (·.getObjValAs? String "name" == .ok sec)
    | throw s!"no section {sec}"
  readPlacement (← s.getObjVal? "lowering")

end Fe.Sonatina.Stage3.Place
