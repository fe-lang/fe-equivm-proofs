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

/-- A GVN operand of the record (`GvnOperand`): a value, or an immediate word. -/
inductive GOp where
  | val (v : Nat)
  | imm (w : Nat)
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

/-- A `GvnTerm` of the record: a value, an immediate word, or the operation of the step input's
    instruction of id `id` on `args` in place of its operands. -/
inductive GTerm where
  | val (v : Nat)
  | imm (w : Nat)
  | inst (id : Nat) (args : List GTerm)
  deriving Repr, Inhabited, Lean.ToExpr

/-- GVN's facts (`GvnFacts`). -/
structure GvnFacts where
  /-- `(block, slot)`. -/
  deadEdges : List (Nat × Nat) := []
  /-- `(value, representative)`. -/
  cls : List (Nat × GOp) := []
  /-- `(block, slot, lhs, rhs)`: `lhs = rhs` once the edge is taken. -/
  preds : List (Nat × Nat × GOp × GOp) := []
  /-- The phis a `gvn_rewrite` inserted: `(phi, block, term)`. -/
  phis : List (Nat × Nat × Option GTerm) := []
  /-- `(value, phi)`: the value the rewrite replaced by an inserted phi. -/
  valuePhis : List (Nat × Nat) := []
  deriving Repr, Inhabited, Lean.ToExpr

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
  /-- GVN's facts (`gvn_prune`, `gvn_rewrite`). -/
  gvn : Option GvnFacts := none
  /-- The keys of the record these checkers do not read (`ranges`, `finite_loops`). -/
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

def jOp (j : Json) : Except String GOp :=
  match j.getObjVal? "value" with
  | .ok v => return .val (← jNat v)
  | .error _ => return .imm (← jNat (← j.getObjVal? "imm"))

/-- A `GvnTerm`, at most `n` levels deep. -/
def jTerm : Nat → Json → Except String GTerm
  | 0, _ => throw "gvn: term too deep"
  | n + 1, j =>
    match j.getObjVal? "inst" with
    | .ok i => do
      let args ← (← (← i.getObjVal? "args").getArr?).toList.mapM (jTerm n)
      return .inst (← jNat (← i.getObjVal? "inst")) args
    | .error _ => match j.getObjVal? "value" with
      | .ok v => return .val (← jNat v)
      | .error _ => return .imm (← jNat (← j.getObjVal? "imm"))

def jList (j : Json) (key : String) : Except String (List Json) :=
  match j.getObjVal? key with
  | .ok a => return (← a.getArr?).toList
  | .error _ => return []

def readGvn (j : Json) : Except String GvnFacts := do
  let de ← (← jList j "dead_edges").mapM fun e => do
    let a ← e.getArr?
    unless a.size == 2 do throw "gvn: dead edge"
    return (← jNat a[0]!, ← jNat a[1]!)
  let cls ← (← jList j "class").mapM fun e => do
    let a ← e.getArr?
    unless a.size == 2 do throw "gvn: class"
    return (← jNat a[0]!, ← jOp a[1]!)
  let preds ← (← jList j "preds").mapM fun e => do
    let a ← e.getArr?
    unless a.size == 4 do throw "gvn: predicate"
    return (← jNat a[0]!, ← jNat a[1]!, ← jOp a[2]!, ← jOp a[3]!)
  let phis ← (← jList j "phis").mapM fun e => do
    let t ← match e.getObjVal? "term" with
      | .ok .null | .error _ => pure none
      | .ok t => some <$> jTerm 64 t
    return (← jNat (← e.getObjVal? "phi"), ← jNat (← e.getObjVal? "block"), t)
  let vp ← (← jList j "value_phis").mapM fun e => do
    let a ← e.getArr?
    unless a.size == 2 do throw "gvn: value phi"
    return (← jNat a[0]!, ← jNat a[1]!)
  return { deadEdges := de, cls, preds, phis, valuePhis := vp }

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
    | "gvn" => return { F with gvn := some (← readGvn j) }
    | k => return { F with unread := F.unread ++ [k] }) {}

end Read

end Fe.Sonatina.Steps.Schemas
