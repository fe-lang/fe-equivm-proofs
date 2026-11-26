import Fe.Sonatina.FrameSafe
import Fe.Sonatina.Parse

/-!
Mutants for the checker's reading of the backend's `ISZERO` peepholes after a flag
(`Canon.flagNodes`).  For each sidecar `MUTANT_SIDECARS` names (separated by `:`), each section
the checker accepts in which a block has `is_zero` of `is_zero` of a message call's flag or of a
comparison: the section with the inner `is_zero` replaced by `not`, and with the outer one
reading the flag itself, both of which the bytes contradict.  Then value numbering itself: two
`is_zero`s of a call's flag are the flag, of a storage read are not.
Run with `MUTANT_SIDECARS=<path>:… lake lean scripts/DialectMutants.lean`.
-/

open Fe.Sonatina

/-- The block's statements with `f` applied to the statement at each position. -/
def mapStmts (b : Block) (f : Nat → Stmt → Stmt) : Block :=
  { b with body := b.body.zipIdx.map fun (s, i) => f i s }

/-- The positions in block `b` of `v = is_zero u` with `u = is_zero r`, `r` a flag or a
    comparison of the block: the inner and the outer statement's positions and `r`. -/
def flagPairs (b : Block) : List (Nat × Nat × Nat) :=
  let defs := b.body.zipIdx.filterMap fun (s, i) => s.def?.map fun (id, inst) => (id, inst, i)
  let boolish := fun (r : Nat) => match defs.find? (·.1 == r) with
    | some (_, inst, _) => inst.flag || (inst matches .cmp _ _ _)
    | none => false
  defs.filterMap fun (_, inst, o) => match inst with
    | .isZero (.var u) => match defs.find? (·.1 == u) with
      | some (_, .isZero (.var r), j) => if boolish r then some (j, o, r) else none
      | _ => none
    | _ => none

/-- The section with block `bid` of function `fn` changed by `g`. -/
def mapBlockIn (fn : String) (bid : Nat) (g : Block → Block) (c : CodeSection) : CodeSection :=
  { c with lowering := c.lowering.map fun l => { l with machine := { l.machine with
      funcs := l.machine.funcs.map fun f => if f.name == fn then
        { f with blocks := f.blocks.map fun b => if b.id == bid then g b else b } else f } } }

def verdict (code : CodeSection) (entry : String) : String :=
  match Check.checkSection code entry (code.spillPlan entry) with
  | .ok () => "ACCEPTED"
  | .error e => s!"rejected: {e}"

#eval show IO Unit from do
  let some paths ← IO.getEnv "MUTANT_SIDECARS" | throw (IO.userError "MUTANT_SIDECARS is not set")
  for path in paths.splitOn ":" do
    let s ← IO.ofExcept (Parse.parseSidecar (← IO.FS.readFile path))
    for (name, entry) in Check.entries s do
      let some code := s.section? name | continue
      let some low := code.lowering | continue
      IO.println s!"SECTION {path} {name}: {verdict code entry}"
      for f in low.machine.funcs do
        for b in f.blocks do
          for (j, o, r) in flagPairs b do
            -- The inner `is_zero` as `not`.
            let notInner := mapBlockIn f.name b.id (mapStmts · fun i s =>
              if i == j then match s.inst with
                | .isZero a => { s with inst := .not a }
                | _ => s
              else s) code
            -- The outer `is_zero` of the flag itself: one `ISZERO` too few.
            let outerOfFlag := mapBlockIn f.name b.id (mapStmts · fun i s =>
              if i == o then match s.inst with
                | .isZero _ => { s with inst := .isZero (.var r) }
                | _ => s
              else s) code
            IO.println s!"  {f.name} block{b.id} flag v{r}: inner not: {verdict notInner entry}; \
              outer of the flag: {verdict outerOfFlag entry}"
  -- Value numbering: two `is_zero`s of a call's flag are the flag, of a storage read are not.
  let call : Inst := .evm .call (List.replicate 7 (.imm 256 0))
  let load : Inst := .evm .sload [.imm 256 0]
  for (what, inst) in [("call", call), ("sload", load)] do
    let k := Check.Canon.ofDefs [] [(1, inst), (2, .isZero (.var 1)), (3, .isZero (.var 2))]
    IO.println s!"CANON is_zero is_zero of {what}: {repr (k.expand 3)}"
