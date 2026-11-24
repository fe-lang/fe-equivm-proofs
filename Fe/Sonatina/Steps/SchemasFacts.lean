import Lean.Data.Json
import Lean.ToExpr

/-!
# The facts of a machine step, read

`StepFacts` is what the `known_bits_simplify` and `sccp_fold` checkers read of a function step's
facts (design §3.1, §3.3); `readFacts` reads them from the record as `Read.parseFacts` keeps
them (each key with its JSON), at elaboration.  A key no checker reads is kept in `unread`, and
a checker handed one for its own kind rejects.  This module imports neither the schema library
nor `Validate`, so that the record's reader can import it.
-/

namespace Fe.Sonatina.Steps.Schemas


/-- The facts of a step that these checkers read. -/
structure StepFacts where
  /-- `(v, kz, ko)`. -/
  knownBits : List (Nat × Nat × Nat) := []
  /-- `(v, mask)`, for a round of demand rewrites; a value not listed has no bit demanded. -/
  demanded : Option (List (Nat × Nat)) := none
  /-- SCCP's constants `(v, c)`, if the step has SCCP facts. -/
  consts : Option (List (Nat × Nat)) := none
  /-- SCCP's dead edges `(block, slot)`. -/
  deadEdges : List (Nat × Nat) := []
  /-- The keys of the record these checkers do not read (`ranges`, `gvn`, `finite_loops`). -/
  unread : List String := []
  deriving Repr, Inhabited, Lean.ToExpr

section Read

open Lean

def jNat (j : Json) : Except String Nat :=
  match j with
  | .str s => match s.toNat? with
    | some n => pure n
    | none => throw s!"not a number: {s}"
  | _ => match j.getNat? with
    | .ok n => pure n
    | .error e => throw e

def jPairs (j : Json) : Except String (List (Nat × Nat)) := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    unless a.size == 2 do throw "expected a pair"
    return (← jNat a[0]!, ← jNat a[1]!)

/-- Read the facts of a function step, as `Read.parseFacts` keeps them (key and JSON); a key twice
    is an error. -/
def readFacts (fs : List (String × String)) : Except String StepFacts := do
  unless (fs.map (·.1)).eraseDups.length == fs.length do throw "duplicate fact keys"
  fs.foldlM (fun F (k, v) => do
    let j ← Json.parse v
    match k with
    | "known_bits" =>
      let kb ← (← j.getArr?).toList.mapM fun e => do
        let a ← e.getArr?
        unless a.size == 3 do throw "known_bits: expected a triple"
        return (← jNat a[0]!, ← jNat a[1]!, ← jNat a[2]!)
      return { F with knownBits := kb }
    | "demanded_bits" => return { F with demanded := some (← jPairs j) }
    | "sccp" =>
      let cs ← jPairs (← j.getObjVal? "consts")
      let de ← match j.getObjVal? "dead_edges" with
        | .ok d => jPairs d
        | .error _ => pure []
      return { F with consts := some cs, deadEdges := de }
    | k => return { F with unread := F.unread ++ [k] }) {}

end Read

end Fe.Sonatina.Steps.Schemas
