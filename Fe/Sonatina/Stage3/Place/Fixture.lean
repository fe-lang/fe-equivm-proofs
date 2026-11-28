import Fe.Sonatina.Stage3.Place.Check
import Fe.Sonatina.Stage3.Place.Read
import Fe.Sonatina.Steps.Machine

/-!
# Fixtures for the S14 check

`place_fixture name "sidecar" "section"` defines, from a sidecar file of version 6 (path from
the project root), `name.src : HSection` (the section's `source_ir`, read by
`H.Parse.objectOfSidecar`), `name.low : Module` (the lowered machine IR, `s.asLowered`),
`name.efp : Option Nat` and `name.rec : Record` (the section's placement record, read by
`placementOf`, its hints filled in, `Record.withHints`), for tests that run `Place.check` in the
kernel.  `slice1_fixture name "sidecar"` defines the arguments of `slice1_sound` from a sidecar
file, and `hex_bytes name "file"` the bytes of a `.bin` file, for the examples (`Examples.lean`).
-/

namespace Fe.Sonatina.Stage3.Place

open Lean Elab Command Fe.Sonatina.H

deriving instance Lean.ToExpr for HInst
deriving instance Lean.ToExpr for HTerm
deriving instance Lean.ToExpr for HStmt
deriving instance Lean.ToExpr for HBlock
deriving instance Lean.ToExpr for HFunc
deriving instance Lean.ToExpr for HModule
deriving instance Lean.ToExpr for HSection
deriving instance Lean.ToExpr for H.Object
deriving instance Lean.ToExpr for Loc
deriving instance Lean.ToExpr for FixedRule
deriving instance Lean.ToExpr for Malloc
deriving instance Lean.ToExpr for FuncRec
deriving instance Lean.ToExpr for Record

/-- What a fixture defines: a section, its lowered machine IR and entry free pointer, a record. -/
def fixtureOf (text sec : String) : Except String (HSection × Module × Option Nat × Record) := do
  let h ← H.Parse.objectOfSidecar text
  let s ← Parse.parseSidecar text
  let r := (← placementOf text sec).record
  let src := if sec == "init" then h.init else h.runtime
  let low := s.asLowered.machineOf sec
  return (src, low, ((s.section? sec).bind (·.lowering)).bind (·.entryFreePtr),
    r.withHints src low)

private def defConst (name : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| addAndCompile <| .defnDecl
    { name, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe }

/-- `place_fixture name "sidecar" "section"`. -/
elab "place_fixture " name:ident path:str sec:str : command => do
  let text ← IO.FS.readFile path.getString
  match fixtureOf text sec.getString with
  | .error e => throwError "{path.getString}: {e}"
  | .ok (src, low, efp, r) =>
    let n := (← getCurrNamespace) ++ name.getId
    defConst (n ++ `src) (mkConst ``HSection) (toExpr src)
    defConst (n ++ `low) (mkConst ``Module) (toExpr low)
    defConst (n ++ `efp) (toTypeExpr (Option Nat)) (toExpr efp)
    defConst (n ++ `rec) (mkConst ``Record) (toExpr r)

/-- What `slice1_sound` takes of a sidecar: the sidecar, its handover object, and the placement
    records of its runtime and init sections, each with its hints filled in against its section of
    the object and the section's lowered machine IR. -/
def slice1FixtureOf (text : String) : Except String (Sidecar × H.Object × Record × Record) := do
  let s ← Parse.parseSidecar text
  let h ← H.Parse.objectOfSidecar text
  let recOf (sec : String) (hs : HSection) : Except String Record := do
    return (← placementOf text sec).record.withHints hs (s.asLowered.machineOf sec)
  return (s, h, ← recOf "runtime" h.runtime, ← recOf "init" h.init)

/-- `slice1_fixture name "sidecar"` defines, from a sidecar file of version 6 (path from the
    project root), `name.s : Sidecar` (`Parse.parseSidecar`), `name.h : H.Object`
    (`H.Parse.objectOfSidecar`), and `name.rr`, `name.ri : Record`, the placement records of its
    runtime and init sections (`placementOf`, `Record.withHints`): the arguments of
    `slice1_sound`. -/
elab "slice1_fixture " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  match slice1FixtureOf text with
  | .error e => throwError "{path.getString}: {e}"
  | .ok (s, h, rr, ri) =>
    let n := (← getCurrNamespace) ++ name.getId
    defConst (n ++ `s) (mkConst ``Sidecar) (toExpr s)
    defConst (n ++ `h) (mkConst ``H.Object) (toExpr h)
    defConst (n ++ `rr) (mkConst ``Record) (toExpr rr)
    defConst (n ++ `ri) (mkConst ``Record) (toExpr ri)

/-- `hex_bytes name "file"` defines `name : ByteArray`, the bytes of a file of hex digits such as
    a `.bin` file the compiler writes (path from the project root), surrounding whitespace
    ignored. -/
elab "hex_bytes " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  match Parse.hexBytes text.trimAscii.toString with
  | .error e => throwError "{path.getString}: {e}"
  | .ok b => defConst ((← getCurrNamespace) ++ name.getId) (mkConst ``ByteArray) (toExpr b)

end Fe.Sonatina.Stage3.Place
