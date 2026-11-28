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

Before the rules, the record's hints are checked (`hintsOk`): its functions are the source
module's, in order; each one's machine function is the first of its name in the lowered module;
each call's callee is the first source function of its name.  After that the check names
functions by place, never by comparing names again: comparing names is what costs the most when
the kernel runs the check.

S9 (spill reserves) is not checked: the lowered machine IR has no spills, and
`place_lower_sound` does not use it (PLAN F1); it belongs to the spilled-sidecar slice, with the
record's reserve ranges.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The first-stage switch: when set, the check rejects transient heap mallocs (S10a) and
    heap mallocs at an exact base, which `place_lower_sound` does not cover yet. -/
def Stage1 : Bool := true

/-- Each function of the section with its place and its record. -/
def placed (src : HSection) (r : Record) : List (Nat × HFunc × FuncRec) :=
  src.module.funcs.zipIdx.map fun (f, k) => (k, f, (r.funcs[k]?).getD { name := f.name })

/-- The `k`-th of a list of functions is the first of its name. -/
def firstOf {α : Type} (name : α → String) (l : List α) (k : Nat) (n : String) : Bool :=
  match l[k]? with
  | some x => name x == n && (l.take k).all fun y => name y != n
  | none => false

/-- The record's hints: its functions are the source module's in order, by name; each one's
    machine function (`mfunc`) is the first of its name in `low`; each call's callee (`calls`) is
    the first source function of its name, once per callee place used. -/
def hintsOk (src : HSection) (low : Module) (r : Record) : Bool :=
  let fs := src.module.funcs
  r.funcs.length == fs.length &&
  (r.funcs.zip fs).all (fun (fr, f) => fr.name == f.name && firstOf (·.name) low.funcs fr.mfunc f.name) &&
  let used := (r.funcs.flatMap fun fr => fr.calls.flatten).dedupB
  used.all fun k => match fs[k]? with
    | some g => firstOf (·.name) fs k g.name
    | none => false

/-- The section has a heap malloc. -/
def hasHeap (P : List (Nat × HFunc × FuncRec)) : Bool :=
  P.any fun (_, f, fr) => fr.mallocs.any fun (x, m) =>
    (m matches .heap ..) && f.blocks.any fun b => b.body.any (·.defs == [x])

/-- Every source `alloca` has a record location and a range; every `evm_malloc` a placement of
    rule set S. -/
def sitesRecorded (src : HSection) (r : Record) (P : List (Nat × HFunc × FuncRec)) : Option String :=
  P.findSome? fun (_, f, fr) =>
    let R := rangesOf r fr src.module.structs f
    f.blocks.findSome? fun b => b.body.findSome? fun s => match s.inst, s.dsts with
      | .base (.alloca _), [(x, _)] =>
        if (R.find? x).isSome then none else some s!"S2: alloca v{x} of {f.name} has no location"
      | .base (.malloc _), [(x, _)] => match fr.mallocs.lookup x with
        | none => some s!"S2: evm_malloc v{x} of {f.name} has no placement"
        | some (.heap _ (some _) _) =>
          if Stage1 then some s!"stage 1: exact_base heap malloc v{x} of {f.name}" else none
        | some (.heap _ none false) =>
          if Stage1 then some s!"stage 1: transient heap malloc v{x} of {f.name} (S10a)" else none
        | some (.fixed _ .terminal) | some (.heap _ none true) => none
        | some (.fixed _ _) => some s!"S2: fixed malloc v{x} of {f.name} is not terminal"
      | _, _ => none

/-- Rule S1, on the record's frame facts and the entry free pointer; `rs` are the section's
    `alloca` ranges. -/
def ruleS1 (P : List (Nat × HFunc × FuncRec)) (rs : List Range) (efp : Option Nat) : Option String :=
  match P.find? fun (_, _, fr) =>
      fr.dynFrame || fr.lazyFrame || fr.callPreserves != 0 || fr.dynSpClamp with
  | some (_, f, _) => some s!"S1: {f.name} has a dynamic or lazy frame, call preserves or a stack clamp"
  | none =>
    if hasHeap P then
      match efp with
      | some e =>
        if e < 0x60 then some "S1: entry free pointer below 0x60"
        else if rs.all (disjoint (0x40, 0x60)) then none
        else some "S1: an alloca range meets the free-pointer slot [0x40, 0x60)"
      | none => some "S1: a heap malloc without an entry free pointer"
    else none

/-- Rule S2's function facts: no free-pointer restore; one placement per site (review 25,
    L1). -/
def ruleS2 (src : HSection) (r : Record) (P : List (Nat × HFunc × FuncRec)) : Option String :=
  match P.find? fun (_, _, fr) => fr.restoresFp with
  | some (_, f, _) => some s!"S2: {f.name} restores the free pointer"
  | none =>
    match P.find? fun (_, _, fr) =>
        !(distinct (fr.allocas.map (·.1)) && distinct (fr.mallocs.map (·.1))) with
    | some (_, f, _) => some s!"S2: a site of {f.name} has two placements"
    | none => sitesRecorded src r P

/-- Rules S4 and S5. -/
def ruleS45 (P : List (Nat × HFunc × FuncRec)) (rs : List Range) (efp : Option Nat) : Option String :=
  let bases := P.flatMap fun (_, _, fr) => fr.mallocs.map fun (_, m) => match m with
    | .heap b _ _ => b
    | .fixed b _ => b
  if hasHeap P && !(rs.all fun x => x.2 ≤ efp.getD 0) then
    some "S4: an alloca range ends above the heap floor"
  else if !(efp.all (· < 2 ^ 32) && bases.all (· < 2 ^ 32) && rs.all (·.2 < 2 ^ 32)) then
    some "S5: an address of the record is not below 2^32"
  else none

/-- The live sets of every point of every block of `f`. -/
def pointsOf (f : HFunc) (L : Live) : NatMap (List (List Nat)) :=
  f.blocks.foldl (fun M b => M.insert b.id (livePoints f L b)) .empty

def ptsAt (pts : NatMap (List (List Nat))) (b k : Nat) : List Nat :=
  (((pts.find? b).getD [])[k]?).getD []

/-- The liveness certificate on precomputed points. -/
def liveOkAt (f : HFunc) (L : Live) (pts : NatMap (List (List Nat))) : Bool :=
  f.blocks.all (fun b => (ptsAt pts b.id 0).all (liveGet L b.id).contains) &&
    match f.blocks.head? with
    | some e => (liveGet L e.id).all fun v => f.params.any (·.1 == v)
    | none => false

/-- No machine value a source statement defines is the machine value of a source value live
    before or after it, other than the statement's own results; nor a machine phi's of a source
    value live at its block's start other than the block's phis.  (With this the machine
    environment keeps every live value's machine value; PLAN §2.) -/
def clobberOk (f : HFunc) (L : Live) (pts : NatMap (List (List Nat))) (fl : FuncLower) : Bool :=
  let hits (live : List Nat) (own : List Nat) (ms : List Nat) : Bool :=
    live.any fun y => !own.contains y && ms.any fun m => fl.vm.find? y == some (.var m)
  f.blocks.all fun b =>
    let dss := (fl.defs.find? b.id).getD []
    !hits (liveGet L b.id) (b.phis.map (·.dst)) (b.phis.filterMap fun p => match fl.vm.find? p.dst with
      | some (.var m) => some m
      | _ => none) &&
    (b.body.zipIdx.zip dss).all fun ((s, k), ds) =>
      ds.isEmpty || !hits (ptsAt pts b.id k ++ ptsAt pts b.id (k + 1)) s.defs ds

/-- Rule S3's two uses: no value with origins is the value operand of a store, or returned. -/
def s3Uses (O : Orig) (f : HFunc) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun s => match s.inst with
      | .base (.mstore _ v _) | .base (.evm .mstore [_, v]) => (origOf O v).isEmpty
      | _ => true) &&
    match b.term with
    | .base (.ret vs) => vs.all fun v => (origOf O v).isEmpty
    | _ => true

/-- The blocks reachable from the blocks `R`, by rounds. -/
def reachIter (f : HFunc) : Nat → List Nat → List Nat
  | 0, R => R
  | n + 1, R =>
    let R' := nset (R ++ R.flatMap fun b => ((f.block? b).map (·.term.succs)).getD [])
    if R'.length == R.length then R else reachIter f n R'

/-- The statement's results are integers in every run of H: a comparison, `is_zero`, an
    operation on words other than the five that may keep a pointer (`ptrBin`), a cast that does
    not keep one, `evm_mload_bytes`, `trunc_nuw`, a symbol's offset or size, a memory-free EVM
    operation (`evmH`, `ofSonatina`). -/
def intStmt (s : HStmt) : Bool :=
  match s.inst with
  | .base (.cmp ..) | .base (.isZero _) | .base (.not _) | .base (.neg _) | .base (.clz _)
  | .base (.ctz _) | .base (.ovf ..) | .base (.sat ..) | .base (.symAddr _) | .base (.symSize _)
  | .mloadBytes .. | .truncNuw .. => true
  | .base (.bin op _ _) => !(op == .add || op == .sub || op == .or || op == .xor || op == .and)
  | .base (.cast op _ t) => !keepsPtr op t
  | .base (.evm op _) => op.memFree
  | _ => false

/-- The integer operands of function `f`, whose values are integers in every run of H: an
    immediate; a value declared narrower than a word (`Val.fits`: a pointer has width 256); a
    result of an `intStmt` (each value of `f` is defined once, `funcLower`). -/
def intOperands (f : HFunc) : List Nat :=
  f.params.filterMap (fun (x, t) => if t.bits < 256 then some x else none) ++
  f.blocks.flatMap fun b =>
    b.phis.filterMap (fun p => if p.ty.bits < 256 then some p.dst else none) ++
    b.body.flatMap fun s => if intStmt s then s.defs else
      s.dsts.filterMap fun (x, t) => if t.bits < 256 then some x else none

/-- The values whose value is a pointer into fixed buffer `t` in every run of H (review 25,
    C1): its result, and `gep`s of them, `add`s of them and an integer (`I`, `intOperands`) in
    either order, `sub`s of an integer from them, the casts that keep a pointer and
    `black_box`es of them; never a `phi`. -/
def mustStep (I M : List Nat) (s : HStmt) : Bool :=
  let m := fun (a : Operand) => match a with
    | .var y => M.contains y
    | .imm .. => false
  let i := fun (a : Operand) => match a with
    | .var y => I.contains y
    | .imm .. => true
  match s.inst with
  | .gep _ b _ => m b
  | .base (.bin .add a b) => m a && i b || m b && i a
  | .base (.bin .sub a b) => m a && i b
  | .base (.cast op a t) => keepsPtr op t && m a
  | .base (.blackBox a) => m a
  | _ => false

def mustIter (f : HFunc) (I : List Nat) : Nat → List Nat → List Nat
  | 0, M => M
  | n + 1, M =>
    let M' := nset (M ++ f.blocks.flatMap fun b => b.body.flatMap fun s =>
      if mustStep I M s then s.defs else [])
    if M'.length == M.length then M else mustIter f I n M'

/-- Rule S6 for terminal fixed buffer `t` at statement `k` of block `b` of `f`. -/
def s6Site (O : Orig) (f : HFunc) (b : HBlock) (k t : Nat) : Bool :=
  let R := reachIter f (f.blocks.length + 1) (nset b.term.succs)
  let I := intOperands f
  let M := mustIter f I (f.blocks.length + 1) [t]
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
    | .base (.brTable s _ cs) => noT s && cs.all (noT ·.1)
    | .base (.evmReturn a l) | .base (.evmRevert a l) => inM a || isZeroImm l
    | _ => false
  -- The must-origin set is justified member by member; the reach set is closed.
  (M.all fun y => y == t || f.blocks.any fun b => b.body.any fun s => s.defs.contains y && mustStep I M s) &&
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
def ruleS7 (R : NatMap Range) (fr : FuncRec) (P : FP) (O : Orig) (pts : NatMap (List (List Nat)))
    (f : HFunc) : Bool :=
  let ok (y : Nat) (good : Range → Bool) : Bool :=
    (origOf O (.var y)).all fun o => o == 0 || (R.find? (o - 1)).any good
  (f.blocks.zip (withCallees fr f)).all fun (b, ss) =>
    (ss.zipIdx).all fun ((s, c), k) => match s.inst, s.dsts with
      | .base (.alloca _), [(x, _)] => match R.find? x with
        | some r => r.1 == r.2 || (ptsAt pts b.id (k + 1)).all fun y => y == x || ok y (disjoint r)
        | none => false
      | .base (.call _ args), _ => match c with
        | some g => ((ptsAt pts b.id (k + 1)).filter (!s.defs.contains ·) ++ varsOf args).all fun y =>
            ok y fun r => (fpOf P g).all (disjoint r)
        | none => false
      | _, _ => true

/-- The analyses of a section, computed once (untrusted: `diagnose` checks each). -/
structure Facts where
  ranges : NatMap (NatMap Range)
  flags : Flags
  orig : NatMap Orig
  fp : FP
  derived : Derived

def Facts.rangesAt (X : Facts) (k : Nat) : NatMap Range := (X.ranges.find? k).getD .empty
def Facts.origAt (X : Facts) (k : Nat) : Orig := (X.orig.find? k).getD .empty

/-- The functions with place, own ranges and callees, for footprints. -/
def fpInput (P : List (Nat × HFunc × FuncRec)) (ranges : NatMap (NatMap Range)) :
    List (Nat × List Range × List Nat) :=
  P.map fun (k, f, fr) => (k, ownRanges ((ranges.find? k).getD .empty) f, callees fr f)

def derivedInput (P : List (Nat × HFunc × FuncRec)) :
    List (Nat × HFunc × List (List (HStmt × Option Nat))) :=
  P.map fun (k, f, fr) => (k, f, withCallees fr f)

/-- Compute the analyses, or take the record's certificates. -/
def facts (src : HSection) (r : Record) (P : List (Nat × HFunc × FuncRec)) : Facts :=
  let n := P.length + 2
  let ranges := P.foldl (fun M (k, f, fr) => M.insert k (rangesOf r fr src.module.structs f)) .empty
  match r.flagsCert, r.fpCert, r.derivedCert,
      P.mapM (fun (k, _, fr) => fr.origCert.map fun l => (k, NatMap.ofList l)) with
  | some fl, some fp, some (dv, dp, dr), some os =>
    { ranges, flags := NatMap.ofList fl, orig := NatMap.ofList os, fp := NatMap.ofList fp
      derived := ⟨NatMap.ofList dv, NatMap.ofList dp, dr⟩ }
  | _, _, _, _ =>
  let origAll (F : Flags) : NatMap Orig := P.foldl (fun M (k, f, fr) =>
    M.insert k (origIter fr F k f (f.blocks.length + 2) .empty)) .empty
  let rec flagIter : Nat → Flags → Flags
    | 0, F => F
    | m + 1, F =>
      let O := origAll F
      let (F', changed) := P.foldl (fun (F', ch) (k, f, fr) =>
        (callFlags fr f ((O.find? k).getD .empty)).foldl (fun (F', ch) (g, is) =>
          let old := (F'.find? g).getD []
          let new := nset (old ++ is)
          (F'.insert g new, ch || new.length != old.length)) (F', ch)) (F, false)
      if changed then flagIter m F' else F'
  let F := flagIter n .empty
  { ranges, flags := F, orig := origAll F, fp := fpIter (fpInput P ranges) n .empty
    derived := derivedIter (derivedInput P) n ⟨.empty, .empty, []⟩ }

/-- Some `alloca` or fixed buffer of the section is at address 0 (rule S8 applies). -/
def zeroMode (P : List (Nat × HFunc × FuncRec)) (rs : List Range) : Bool :=
  rs.any (·.1 == 0) || P.any fun (_, _, fr) => fr.mallocs.any fun (_, m) => m matches .fixed 0 _

/-- The context of function `f`'s translation check. -/
def fctx (src : HSection) (r : Record) (fr : FuncRec) (f : HFunc) (mf : Func) : FCtx :=
  { prec := r, frec := fr, src := src.module, symbols := src.symbols
    decls := declsOf f, bm := blockMapOf fr f, mf }

/-- The per-function rules: translation, liveness and clobbering, S3, S6, S7, S8. -/
def funcDiag (src : HSection) (low : Module) (r : Record) (X : Facts) (z : Bool)
    (kf : Nat × HFunc × FuncRec) : Option String :=
  let (k, f, fr) := kf
  match low.funcs[fr.mfunc]? with
  | none => some s!"translation: no machine function {f.name}"
  | some mf =>
  match funcLower (fctx src r fr f mf) f with
  | none => some s!"translation: {f.name}"
  | some fl =>
    let L := match fr.liveCert with
      | some l => NatMap.ofList l
      | none => liveOf f
    let pts := pointsOf f L
    let O := X.origAt k
    if !liveOkAt f L pts then some s!"liveness: {f.name}"
    else if !clobberOk f L pts fl then some s!"translation: {f.name} redefines a live value's machine value"
    else if !(origOk fr X.flags k f O && flagsOk X.flags fr f O) then some s!"S3: origins of {f.name}"
    else if !s3Uses O f then some s!"S3: {f.name} stores or returns a value with origins"
    else if !ruleS6 O fr f then some s!"S6: a terminal buffer of {f.name}"
    else if !ruleS7 (X.rangesAt k) fr X.fp O pts f then some s!"S7: {f.name}"
    else if z && !notObserved X.derived k f then some s!"S8: {f.name} observes a derived value"
    else none

/-- The first rule the lowering of `src` to `low` under `r` fails, if any. -/
def diagnose (src : HSection) (low : Module) (efp : Option Nat) (r : Record) : Option String :=
  if !hintsOk src low r then some "record: functions, machine functions or callees do not match"
  else
  let P := placed src r
  let X := facts src r P
  let rs := P.flatMap fun (k, f, _) => ownRanges (X.rangesAt k) f
  (ruleS1 P rs efp) <|> (ruleS2 src r P) <|> (ruleS45 P rs efp) <|>
  (let z := zeroMode P rs
   if !fpOk (fpInput P X.ranges) X.fp then some "S7: footprints"
   else if z && !derivedOk (derivedInput P) X.derived then some "S8: derived values"
   else P.findSome? (funcDiag src low r X z) <|>
     match src.module.funcs.findIdx? (·.name == src.entry) with
     | some k => match src.module.funcs[k]? with
       | some e => if e.params.isEmpty then none else some "entry: the section entry has parameters"
       | none => some "entry: no section entry"
     | none => some "entry: no section entry")

/-- S14 for one section: the placement record `r` and the rules of S accept lowering `src` (H
    dialect) to `low` (machine IR), entered with the free pointer `efp`. -/
def check (src : HSection) (low : Module) (efp : Option Nat) (r : Record) : Bool :=
  (diagnose src low efp r).isNone

/-- The values `f` declares. -/
def declared (f : HFunc) : List Nat :=
  f.params.map (·.1) ++ f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap HStmt.defs

/-- The record with its hints filled in from `src` and `low` (compiled use: it compares names
    freely), its functions put in the source module's order (a function the record does not list
    gets an empty one), and its certificates computed.  The checker checks all of it. -/
def Record.withHints (src : HSection) (low : Module) (r : Record) : Record :=
  let fs := src.module.funcs
  let idx (n : String) : Nat := (fs.findIdx? (·.name == n)).getD fs.length
  let r1 : Record := { r with funcs := fs.map fun f =>
      let fr := (r.funcs.find? (·.name == f.name)).getD { name := f.name }
      { fr with
        mfunc := (low.funcs.findIdx? (·.name == f.name)).getD low.funcs.length
        calls := f.blocks.map fun b => b.body.filterMap fun s => match s.inst with
          | .base (.call g _) => some (idx g)
          | _ => none } }
  let P := placed src r1
  let X := facts src { r1 with flagsCert := none } P
  let keys (M : NatMap (List Nat)) (xs : List Nat) : List (Nat × List Nat) :=
    xs.filterMap fun x => (M.find? x).bind fun l => if l.isEmpty then none else some (x, l)
  let ks := P.map (·.1)
  { r1 with
    funcs := P.map fun (k, f, fr) =>
      let vm := match low.funcs[fr.mfunc]? with
        | some mf =>
          let c := fctx src r1 fr f mf
          let bcs := f.blocks.zipIdx.map fun (b, j) => (b, (fr.calls[j]?).getD [])
          let v := inferVm c f (f.blocks.length + 1) (paramVm f mf) bcs
          some ((declared f).filterMap fun x => (v.find? x).map (x, ·))
        | none => none
      let L := liveOf f
      { fr with vmCert := vm, liveCert := some (f.blocks.map fun b => (b.id, liveGet L b.id))
                origCert := some (keys (X.origAt k) (declared f)) }
    flagsCert := some (keys X.flags ks)
    fpCert := some (ks.map fun k => (k, fpOf X.fp k))
    derivedCert := some (keys X.derived.vals ks, keys X.derived.params ks, X.derived.rets) }

end Fe.Sonatina.Stage3.Place
