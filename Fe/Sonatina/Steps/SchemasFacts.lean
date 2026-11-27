import Lean.Data.Json
import Lean.ToExpr

/-!
# The facts of a machine step, read

`StepFacts` is what the `known_bits_simplify`, `sccp_fold` and `adce` checkers read of a function
step's facts (design §3.1, §3.3); `readFacts` reads them from the record as `Parse.parseFacts`
keeps them (each key with its JSON), at elaboration, strictly: a key the record's writer does
not write is an error, and so is a missing one (`exactKeys`).  The record's one key no checker
reads (`ranges`) is kept in `unread`, and a checker handed it for its own kind rejects.  This
module imports neither the schema library nor `Validate`, so that the record's reader can
import it.
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
  /-- ADCE's loops proven finite, `(header, latch, iv, step, exit)` (`FiniteLoop` of the
      record): read for `adce`, which does not use them: it removes no loop. -/
  finiteLoops : List (Nat × Nat × Nat × Nat × Nat) := []
  /-- GVN's facts (`gvn_prune`, `gvn_rewrite`). -/
  gvn : Option GvnFacts := none
  /-- The keys of the record these checkers do not read: `ranges`, if not empty. -/
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

/-- `j` is an object with exactly the keys `keys`: those the record's writer (Fe's
    `sidecar.rs`) writes for it, every one of them always. -/
def exactKeys (what : String) (keys : List String) (j : Json) : Except String Unit := do
  let .obj kvs := j | throw s!"{what}: not an object: {j.compress}"
  let ks := kvs.toList.map (·.1)
  for k in ks do unless keys.contains k do throw s!"{what}: unknown key {k}"
  for k in keys do unless ks.contains k do throw s!"{what}: no key {k}"

/-- A `GvnOperand`: `{"value": v}` or `{"imm": w}`. -/
def jOp (j : Json) : Except String GOp := do
  match (← j.getObj?).toList with
  | [("value", v)] => return .val (← jNat v)
  | [("imm", w)] => return .imm (← jNat w)
  | _ => throw s!"gvn: not an operand: {j.compress}"

/-- A `GvnTerm`, at most `n` levels deep: `{"value": v}`, `{"imm": w}` or
    `{"inst": {"inst": id, "args": [...]}}`. -/
def jTerm : Nat → Json → Except String GTerm
  | 0, _ => throw "gvn: term too deep"
  | n + 1, j => do
    match (← j.getObj?).toList with
    | [("inst", i)] =>
      exactKeys "gvn term" ["inst", "args"] i
      let args ← (← (← i.getObjVal? "args").getArr?).toList.mapM (jTerm n)
      return .inst (← jNat (← i.getObjVal? "inst")) args
    | [("value", v)] => return .val (← jNat v)
    | [("imm", w)] => return .imm (← jNat w)
    | _ => throw s!"gvn: not a term: {j.compress}"

def jList (j : Json) (key : String) : Except String (List Json) := do
  return (← (← j.getObjVal? key).getArr?).toList

def readGvn (j : Json) : Except String GvnFacts := do
  exactKeys "gvn" ["dead_edges", "class", "preds", "phis", "value_phis"] j
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
    exactKeys "gvn phi" ["phi", "block", "term"] e
    let t ← match ← e.getObjVal? "term" with
      | .null => pure none
      | t => some <$> jTerm 64 t
    return (← jNat (← e.getObjVal? "phi"), ← jNat (← e.getObjVal? "block"), t)
  let vp ← (← jList j "value_phis").mapM fun e => do
    let a ← e.getArr?
    unless a.size == 2 do throw "gvn: value phi"
    return (← jNat a[0]!, ← jNat a[1]!)
  return { deadEdges := de, cls, preds, phis, valuePhis := vp }

/-- Read the facts of a function step, as `Parse.parseFacts` keeps them (key and JSON); a key twice
    is an error, and so is a key the record does not have (`Parse.factKeys`).  `ranges` is kept
    unread, as no checker reads it. -/
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
      exactKeys "sccp" ["consts", "dead_edges"] j
      return { F with consts := some (← jPairs (← j.getObjVal? "consts"))
                      deadEdges := ← jPairs (← j.getObjVal? "dead_edges") }
    | "gvn" => return { F with gvn := some (← readGvn j) }
    | "finite_loops" =>
      let ls ← (← j.getArr?).toList.mapM fun e => do
        exactKeys "finite loop" ["header", "latch", "iv", "step", "exit"] e
        let n (k : String) : Except String Nat := do jNat (← e.getObjVal? k)
        return (← n "header", ← n "latch", ← n "iv", ← n "step", ← n "exit")
      return { F with finiteLoops := ls }
    | "ranges" => return { F with unread := F.unread ++ ["ranges"] }
    | k => throw s!"unknown fact key {k}") {}

end Read

end Fe.Sonatina.Steps.Schemas
