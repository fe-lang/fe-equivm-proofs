import Fe.Sonatina.Stage3.Place.Analysis

/-!
# The S14 check: rule set S and the translation (design §5.2)

`Place.check src low efp rec` accepts the lowering of section `src` (H dialect, the sidecar's
`source_ir`) to the module `low` (the lowered machine IR, link 4's start), whose run stores the
entry free pointer `efp` at `0x40` first (`Sidecar.runSectionWith`), under the placement record
`rec`.  `diagnose` names the first rule that fails.

The rules, in the order `diagnose` tries them (PLAN §3):

- **S1** no dynamic or lazy frame, call preserves or dynamic stack pointer clamp; if the section
  has a heap site, an entry free pointer `e ≥ 0x60`, and no `alloca` range meets `[0x40, 0x60)`.
- **S2** `alloca`s with a location; heap mallocs that bump the free pointer; terminal fixed
  mallocs; no free-pointer restore.  **First-stage switch** (`Stage1`): transient heap mallocs
  (S10a) and `exact_base` heap mallocs are rejected, each with its own reason.
- **S4** every `alloca` range ends at or below `e` when the section has a heap site.
- **S5** `e`, every `min_base`, fixed base and `alloca` end below `2 ^ 32`.
- **translation** (`funcLower`), for every source function against the machine function of its
  name.
- **liveness** certificate (`liveOk`), and no machine value a statement defines is the image of
  a source value live across it (`clobberOk`).
- **S3** origins certificate and flags; no value with origins is stored as data or returned.
- **S6** terminal fixed buffers: everything reachable after the site is pure, stores through
  the buffer, or halts with a payload in it.
- **S7** footprints certificate; A1 at each `alloca`, A2 at each call (PLAN §3).
- **S8** when an `alloca` or fixed buffer is at address 0: derived certificate, no derived
  value observed.
- **entry**: the section entry is a source function without parameters.

S9 (spill reserves) is not checked: the lowered machine IR has no spills, and
`place_lower_sound` does not use it (PLAN F1); it belongs to the spilled-sidecar slice, with the
record's reserve ranges.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The first-stage switch: when set, the check rejects transient heap mallocs (S10a) and
    heap mallocs at an exact base, which `place_lower_sound` does not cover yet. -/
def Stage1 : Bool := true

/-- The record of function `name`, or an empty one. -/
def Record.frec (r : Record) (name : String) : FuncRec := (r.func? name).getD { name }

/-- The source statements of a module. -/
def _root_.Fe.Sonatina.H.HModule.stmts (m : HModule) : List HStmt := m.funcs.flatMap fun f => f.blocks.flatMap (·.body)

/-- The section has a heap malloc. -/
def hasHeap (src : HSection) (r : Record) : Bool :=
  src.module.funcs.any fun f => (r.frec f.name).mallocs.any fun (x, m) =>
    (m matches .heap ..) && f.blocks.any fun b => b.body.any (·.defs == [x])

/-- Every `alloca` range of the section. -/
def allRanges (src : HSection) (r : Record) : List Range :=
  src.module.funcs.flatMap (ownRanges r src.module.structs r.frec)

/-- Every source `alloca` has a record location and a range; every `evm_malloc` a placement. -/
def sitesRecorded (src : HSection) (r : Record) : Option String :=
  src.module.funcs.findSome? fun f =>
    let fr := r.frec f.name
    f.blocks.findSome? fun b => b.body.findSome? fun s => match s.inst, s.dsts with
      | .base (.alloca _), [(x, _)] =>
        if (allocaRange r fr src.module.structs f x).isSome then none
        else some s!"S2: alloca v{x} of {f.name} has no location"
      | .base (.malloc _), [(x, _)] => match fr.mallocs.lookup x with
        | none => some s!"S2: evm_malloc v{x} of {f.name} has no placement"
        | some (.heap _ (some _) _) =>
          if Stage1 then some s!"stage 1: exact_base heap malloc v{x} of {f.name}" else none
        | some (.heap _ none false) =>
          if Stage1 then some s!"stage 1: transient heap malloc v{x} of {f.name} (S10a)" else none
        | some (.fixed _ .terminal) | some (.heap _ none true) => none
        | some (.fixed _ _) => some s!"S2: fixed malloc v{x} of {f.name} is not terminal"
      | _, _ => none

/-- Rule S1, on the record's frame facts and the entry free pointer. -/
def ruleS1 (src : HSection) (r : Record) (efp : Option Nat) : Option String :=
  match src.module.funcs.find? fun f => let fr := r.frec f.name
      fr.dynFrame || fr.lazyFrame || fr.callPreserves != 0 || fr.dynSpClamp with
  | some f => some s!"S1: {f.name} has a dynamic or lazy frame, call preserves or a stack clamp"
  | none =>
    if hasHeap src r then
      match efp with
      | some e =>
        if e < 0x60 then some "S1: entry free pointer below 0x60"
        else if (allRanges src r).all (disjoint (0x40, 0x60)) then none
        else some "S1: an alloca range meets the free-pointer slot [0x40, 0x60)"
      | none => some "S1: a heap malloc without an entry free pointer"
    else none

/-- Rule S2's function facts: no free-pointer restore. -/
def ruleS2 (src : HSection) (r : Record) : Option String :=
  match src.module.funcs.find? fun f => (r.frec f.name).restoresFp with
  | some f => some s!"S2: {f.name} restores the free pointer"
  | none => sitesRecorded src r

/-- Rules S4 and S5. -/
def ruleS45 (src : HSection) (r : Record) (efp : Option Nat) : Option String :=
  let rs := allRanges src r
  let bases := src.module.funcs.flatMap fun f => (r.frec f.name).mallocs.map fun (_, m) => match m with
    | .heap b _ _ => b
    | .fixed b _ => b
  if hasHeap src r && !(rs.all fun x => x.2 ≤ efp.getD 0) then
    some "S4: an alloca range ends above the heap floor"
  else if !(efp.all (· < 2 ^ 32) && bases.all (· < 2 ^ 32) && rs.all (·.2 < 2 ^ 32)) then
    some "S5: an address of the record is not below 2^32"
  else none

/-- No machine value a source statement defines is the machine value of a source value live
    before or after it, other than the statement's own results; nor a machine phi's of a source
    value live at its block's start other than the block's phis.  (With this the machine
    environment keeps every live value's machine value; PLAN §2.) -/
def clobberOk (f : HFunc) (L : Live) (fl : FuncLower) : Bool :=
  let hits (live : List Nat) (own : List Nat) (ms : List Nat) : Bool :=
    live.any fun y => !own.contains y && ms.any fun m => fl.vm.find? y == some (.var m)
  f.blocks.all fun b =>
    let pts := livePoints f L b
    let dss := (fl.defs.find? b.id).getD []
    !hits (liveGet L b.id) (b.phis.map (·.dst)) (b.phis.filterMap fun p => match fl.vm.find? p.dst with
      | some (.var m) => some m
      | _ => none) &&
    (b.body.zipIdx.zip dss).all fun ((s, k), ds) =>
      !hits ((pts[k]?).getD [] ++ (pts[k + 1]?).getD []) s.defs ds

/-- Rule S3's two uses: no value with origins is the value operand of a store, or returned. -/
def s3Uses (O : Orig) (f : HFunc) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun s => match s.inst with
      | .base (.mstore _ v _) | .base (.evm .mstore [_, v]) => (origOf O v).isEmpty
      | _ => true) &&
    match b.term with
    | .base (.ret vs) => vs.all fun v => (origOf O v).isEmpty
    | _ => true

/-- The blocks reachable from the successors of `b`, by rounds. -/
def reachIter (f : HFunc) : Nat → List Nat → List Nat
  | 0, R => R
  | n + 1, R =>
    let R' := normSet (R ++ R.flatMap fun b => ((f.block? b).map (·.term.succs)).getD [])
    if R'.length == R.length then R else reachIter f n R'

/-- The values whose address is derived only from fixed buffer `t`: its result, and `gep`s,
    `add`s, `sub`s of an integer, word casts and `black_box`es of them; never a `phi`. -/
def mustStep (M : List Nat) (s : HStmt) : Bool :=
  let m := fun (a : Operand) => match a with
    | .var y => M.contains y
    | .imm .. => false
  match s.inst with
  | .gep _ b _ => m b
  | .base (.bin .add a b) => m a || m b
  | .base (.bin .sub a _) => m a
  | .base (.cast op a _) => (op == .ptrToInt || op == .bitcast || op == .intToPtr) && m a
  | .base (.blackBox a) => m a
  | _ => false

def mustIter (f : HFunc) : Nat → List Nat → List Nat
  | 0, M => M
  | n + 1, M =>
    let M' := normSet (M ++ f.blocks.flatMap fun b => b.body.flatMap fun s =>
      if mustStep M s then s.defs else [])
    if M'.length == M.length then M else mustIter f n M'

/-- Rule S6 for terminal fixed buffer `t` at statement `k` of block `b` of `f`. -/
def s6Site (O : Orig) (f : HFunc) (b : HBlock) (k t : Nat) : Bool :=
  let R := reachIter f (f.blocks.length + 1) (normSet b.term.succs)
  let M := mustIter f (f.blocks.length + 1) [t]
  let inM := fun (a : Operand) => match a with
    | .var y => M.contains y
    | .imm .. => false
  let noT := fun (a : Operand) => !(origOf O a).contains (t + 1)
  let stmtOk := fun (s : HStmt) => match s.inst with
    | .base (.bin ..) | .base (.not _) | .base (.neg _) | .base (.clz _) | .base (.ctz _)
    | .base (.ovf ..) | .base (.sat ..) | .base (.cast ..) | .base (.blackBox _)
    | .base (.symAddr _) | .base (.symSize _) | .gep .. | .truncNuw .. => true
    | .base (.cmp _ x y) => noT x && noT y
    | .base (.isZero x) => noT x
    | .base (.mstore a _ _) => inM a
    | .base (.evm .mstore [a, _]) | .base (.evm .mstore8 [a, _]) => inM a
    | _ => false
  let termOk := fun (tm : HTerm) => match tm with
    | .base (.jump _) | .base .evmStop | .base .evmInvalid | .base .unreachable | .returnCode .. => true
    | .base (.br c _ _) => noT c
    | .base (.brTable s _ _) => noT s
    | .base (.evmReturn a l) | .base (.evmRevert a l) => inM a || isZeroImm l
    | _ => false
  -- The must-origin set is justified member by member; the reach set is closed.
  (M.all fun y => y == t || f.blocks.any fun b => b.body.any fun s => s.defs.contains y && mustStep M s) &&
  (R.all fun c => match f.block? c with
    | some cb => cb.term.succs.all R.contains && cb.body.all stmtOk && termOk cb.term
    | none => false) &&
  (b.body.drop (k + 1)).all stmtOk && termOk b.term

/-- Rule S6 for every terminal fixed buffer of `f`. -/
def ruleS6 (O : Orig) (fr : FuncRec) (f : HFunc) : Bool :=
  f.blocks.all fun b => b.body.zipIdx.all fun (s, k) => match s.inst, s.dsts with
    | .base (.malloc _), [(x, _)] => !fr.isFixed x || s6Site O f b k x
    | _, _ => true

/-- Rule S7 as A1 and A2 (PLAN §3): at an `alloca` with a nonempty range, the origins of every
    other value live after it are ranges disjoint from its own; at a call, those of every value
    live after it other than its results, and of every argument, are disjoint from the callee's
    footprint.  A fixed buffer's origin conflicts with everything. -/
def ruleS7 (prec : Record) (structs : List (String × List Ty)) (fr : FuncRec) (P : FP) (O : Orig)
    (L : Live) (f : HFunc) : Bool :=
  let range := allocaRange prec fr structs f
  let ok (y : Nat) (good : Range → Bool) : Bool :=
    (origOf O (.var y)).all fun o => o == 0 || (range (o - 1)).any good
  f.blocks.all fun b =>
    let pts := livePoints f L b
    b.body.zipIdx.all fun (s, k) => match s.inst, s.dsts with
      | .base (.alloca _), [(x, _)] => match range x with
        | some r => r.1 == r.2 || ((pts[k + 1]?).getD []).all fun y => y == x || ok y (disjoint r)
        | none => false
      | .base (.call g args), _ =>
        (((pts[k + 1]?).getD []).filter (!s.defs.contains ·) ++ varsOf args).all fun y =>
          ok y fun r => (fpOf P g).all (disjoint r)
      | _, _ => true

/-- Some `alloca` or fixed buffer of the section is at address 0 (rule S8 applies). -/
def zeroMode (src : HSection) (r : Record) : Bool :=
  (allRanges src r).any (·.1 == 0) ||
    src.module.funcs.any fun f => (r.frec f.name).mallocs.any fun (_, m) => m matches .fixed 0 _

/-- The analyses of a section, computed once. -/
structure Facts where
  flags : Flags
  orig : List (String × Orig)
  fp : FP
  derived : Derived

/-- Compute the analyses (untrusted: `diagnose` checks each). -/
def facts (src : HSection) (r : Record) : Facts :=
  let fs := src.module.funcs
  let n := fs.length + 2
  let origAll (F : Flags) : List (String × Orig) := fs.map fun f =>
    (f.name, origIter (r.frec f.name) F f (f.blocks.length + 2) .empty)
  let rec flagIter : Nat → Flags → Flags
    | 0, F => F
    | k + 1, F =>
      let O := origAll F
      let F' := fs.map fun g => (g.name, normSet (((F.lookup g.name).getD []) ++
        fs.flatMap fun f => (callFlags f ((O.lookup f.name).getD .empty)).flatMap fun (g', is) =>
          if g' == g.name then is else []))
      if F'.map (·.2.length) == F.map (·.2.length) then F' else flagIter k F'
  let F := flagIter n (fs.map fun f => (f.name, []))
  let own := fun name => match fs.find? (·.name == name) with
    | some f => ownRanges r src.module.structs r.frec f
    | none => []
  { flags := F, orig := origAll F, fp := fpIter own fs n (fs.map fun f => (f.name, []))
    derived := derivedIter fs n ⟨fs.map fun f => (f.name, []), fs.map fun f => (f.name, []), []⟩ }

/-- The context of function `f`'s translation check. -/
def fctx (src : HSection) (r : Record) (f : HFunc) (mf : Func) : FCtx :=
  { prec := r, frec := r.frec f.name, src := src.module, symbols := src.symbols
    decls := declsOf f, bm := blockMapOf (r.frec f.name) f, mf }

/-- The per-function rules: translation, liveness and clobbering, S3, S6, S7, S8. -/
def funcDiag (src : HSection) (low : Module) (r : Record) (X : Facts) (z : Bool) (f : HFunc) :
    Option String :=
  match low.func? f.name with
  | none => some s!"translation: no machine function {f.name}"
  | some mf =>
  match funcLower (fctx src r f mf) f with
  | none => some s!"translation: {f.name}"
  | some fl =>
    let fr := r.frec f.name
    let L := liveOf f
    let O := (X.orig.lookup f.name).getD .empty
    if !liveOk f L then some s!"liveness: {f.name}"
    else if !clobberOk f L fl then some s!"translation: {f.name} redefines a live value's machine value"
    else if !(origOk fr X.flags f O && flagsOk X.flags f O) then some s!"S3: origins of {f.name}"
    else if !s3Uses O f then some s!"S3: {f.name} stores or returns a value with origins"
    else if !ruleS6 O fr f then some s!"S6: a terminal buffer of {f.name}"
    else if !ruleS7 r src.module.structs fr X.fp O L f then some s!"S7: {f.name}"
    else if z && !notObserved X.derived f then some s!"S8: {f.name} observes a derived value"
    else none

/-- The first rule the lowering of `src` to `low` under `r` fails, if any. -/
def diagnose (src : HSection) (low : Module) (efp : Option Nat) (r : Record) : Option String :=
  let fs := src.module.funcs
  (ruleS1 src r efp) <|> (ruleS2 src r) <|> (ruleS45 src r efp) <|>
  (let X := facts src r
   let z := zeroMode src r
   let own := fun name => match fs.find? (·.name == name) with
     | some f => ownRanges r src.module.structs r.frec f
     | none => []
   if !fpOk own fs X.fp then some "S7: footprints"
   else if z && !derivedOk fs X.derived then some "S8: derived values"
   else fs.findSome? (funcDiag src low r X z) <|>
     match src.module.func? src.entry with
     | some e => if e.params.isEmpty then none else some "entry: the section entry has parameters"
     | none => some "entry: no section entry")

/-- S14 for one section: the placement record `r` and the rules of S accept lowering `src` (H
    dialect) to `low` (machine IR), entered with the free pointer `efp`. -/
def check (src : HSection) (low : Module) (efp : Option Nat) (r : Record) : Bool :=
  (diagnose src low efp r).isNone

end Fe.Sonatina.Stage3.Place
