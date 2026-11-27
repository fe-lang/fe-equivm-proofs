import Fe.Sonatina.Stage3.Place.Check
import Fe.Sonatina.Steps.Machine

/-!
# Fixtures for the S14 check

`place_fixture name "sidecar" "section" "record"` defines, from a sidecar file and a placement
record file (paths from the project root), `name.src : HSection` (the section's `source_ir`, read
by `H.Parse.objectOfSidecar`), `name.low : Module` (the lowered machine IR, `s.asLowered`),
`name.efp : Option Nat` and `name.rec : Record` (its hints filled in, `Record.withHints`), for tests that run `Place.check` in the kernel.

The record is read from an interim JSON form, until the compiler's placement record and its
format note exist: `{"arena": n, "funcs": [{"name": f, "allocas": [[v, "scratch" | "stable", w]],
"mallocs": [[v, "fixed", base] | [v, "heap", min, exact | null, update]]}]}`.
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

/-- The interim JSON form of a placement record. -/
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

/-- What a fixture defines: a section, its lowered machine IR and entry free pointer, a record. -/
def fixtureOf (text recText sec : String) : Except String (HSection × Module × Option Nat × Record) := do
  let h ← H.Parse.objectOfSidecar text
  let s ← Parse.parseSidecar text
  let r ← Json.parse recText >>= readRecord
  let src := if sec == "init" then h.init else h.runtime
  let low := s.asLowered.machineOf sec
  return (src, low, ((s.section? sec).bind (·.lowering)).bind (·.entryFreePtr),
    r.withHints src low)

private def defConst (name : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| addAndCompile <| .defnDecl
    { name, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe }

/-- `place_fixture name "sidecar" "section" "record"`. -/
elab "place_fixture " name:ident path:str sec:str recPath:str : command => do
  let text ← IO.FS.readFile path.getString
  let recText ← IO.FS.readFile recPath.getString
  match fixtureOf text recText sec.getString with
  | .error e => throwError "{path.getString}: {e}"
  | .ok (src, low, efp, r) =>
    let n := (← getCurrNamespace) ++ name.getId
    defConst (n ++ `src) (mkConst ``HSection) (toExpr src)
    defConst (n ++ `low) (mkConst ``Module) (toExpr low)
    defConst (n ++ `efp) (toTypeExpr (Option Nat)) (toExpr efp)
    defConst (n ++ `rec) (mkConst ``Record) (toExpr r)

end Fe.Sonatina.Stage3.Place
