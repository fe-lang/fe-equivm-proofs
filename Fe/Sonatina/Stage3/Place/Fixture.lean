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
kernel.
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

end Fe.Sonatina.Stage3.Place
