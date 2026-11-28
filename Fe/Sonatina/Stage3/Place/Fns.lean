import Fe.Sonatina.Stage3.Place.Static
import Fe.Sonatina.Stage3.Place.InstCall

/-!
# The section's functions, as the simulation fixes them

`mkFn src low r k` is source function `k` of the section with what `check` computed of it: its
machine function (the record's hint), its translation (`funcLower`), its frame (value map,
declarations, origins, `alloca` ranges, footprint, derived values), its liveness certificate
with the live sets of its points, and the callee places of each block.  Only a function that
is the first of its name has one: H's `call` and the section entry find a function by name
(`HModule.func?`), so the simulation reaches no other (calls by `hintsOk`, the entry by
`findIdx?`).

From `check`, each such function satisfies the static parts of `FnOk` (`fn_hname`, `fn_hsrc`,
`fn_blk`, `fn_walks`) and, at every position the walk reaches, the per-statement facts `At`
(`fn_at`) and distinct machine definitions in the statements left (`fn_nodup`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The bound of the heap bases: the entry free pointer and every heap malloc's minimum base. -/
def secF0 (P : List (Nat × HFunc × FuncRec)) (efp : Option Nat) : Nat :=
  (P.flatMap fun (_, _, fr) => fr.mallocs.map fun (_, m) => match m with
    | .heap b _ _ => b
    | .fixed _ _ => 0).foldl max (efp.getD 0)

/-- The section's facts the invariant depends on. -/
def secS (src : HSection) (r : Record) (efp : Option Nat) : SecFacts where
  e := efp.getD 0
  hasHeap := hasHeap (secP src r)
  z := secZ src r
  F0 := secF0 (secP src r) efp

/-- The frame of function place `k` under the section's facts `X` and its translation `fl`. -/
def frameOf (X : Facts) (k : Nat) (f : HFunc) (fl : FuncLower) : Frame where
  vm := fl.vm
  decls := declsOf f
  O := X.origAt k
  R := X.rangesAt k
  fpf := fpOf X.fp k
  D := X.derived.has k

/-- The callee places of the calls of the block with id `id`. -/
def callsOf (c : FCtx) (f : HFunc) (id : Nat) : List Nat :=
  (((blockCalls c f).find? (·.1.id == id)).map (·.2)).getD []

/-- Function place `k` of the section, if it is the first function of its name and has a
    machine function and a translation. -/
def mkFn (src : HSection) (low : Module) (r : Record) (k : Nat) : Option Fn := do
  let f ← src.module.funcs[k]?
  if firstOf (·.name) src.module.funcs k f.name then
    let fr := (r.funcs[k]?).getD { name := f.name }
    let mf ← low.funcs[fr.mfunc]?
    let c := fctx src r fr f mf
    let fl ← funcLower c f
    let L := liveRec fr f
    some { f, k, c, F := frameOf (secX src r) k f fl, L, pts := pointsOf f L, tb := fl.tb,
           cs := callsOf c f }
  else none

/-- What `mkFn` and `check` give about one function. -/
structure FnUnp (src : HSection) (low : Module) (r : Record) (fn : Fn) (fr : FuncRec)
    (fl : FuncLower) (e : HBlock) (me : Block) (be : Nat)
    (rs : List (Nat × Nat × List (List Nat) × List Nat)) : Prop where
  hf : src.module.funcs[fn.k]? = some fn.f
  first : firstOf (·.name) src.module.funcs fn.k fn.f.name = true
  hfr : fr = (r.funcs[fn.k]?).getD { name := fn.f.name }
  hmf : low.funcs[fr.mfunc]? = some fn.c.mf
  hc : fn.c = fctx src r fr fn.f fn.c.mf
  hfl : funcLower fn.c fn.f = some fl
  hF : fn.F = frameOf (secX src r) fn.k fn.f fl
  hL : fn.L = liveRec fr fn.f
  hpts : fn.pts = pointsOf fn.f fn.L
  htb : fn.tb = fl.tb
  hcs : fn.cs = callsOf fn.c fn.f
  rules : FnRules r (secX src r) (secZ src r) fn.k fn.f fr fl
  he : fn.f.blocks.head? = some e
  hme : fn.c.mf.blocks.head? = some me
  hbe : fn.c.bm.find? e.id = some be
  shape : funcShapeOk fn.c fn.f e me be = true
  hvm : fl.vm = funcVm fn.c fn.f
  params : paramsOk fn.c fn.f fl.vm = true
  regions : regionsOf fn.c fn.f fl.vm = some rs
  dist : distinct (trampOf me be ++ rs.flatMap (·.2.2.2)) = true
  tbOf : fl.tb = NatMap.ofList (rs.map fun (b, t, _) => (b, t))
  defsEq : fl.defs = NatMap.ofList (rs.map fun (b, _, d, _) => (b, d))
  phis : phisAllOk fn.c fn.f fl.vm fl.tb = true

theorem mem_placed {src : HSection} {r : Record} {k : Nat} {f : HFunc}
    (h : src.module.funcs[k]? = some f) :
    (k, f, (r.funcs[k]?).getD { name := f.name }) ∈ placed src r := by
  unfold placed
  exact List.mem_map.mpr ⟨(f, k), mem_zipIdx_of_getElem? h, rfl⟩

theorem fn_unp {src : HSection} {low : Module} {efp : Option Nat} {r : Record} {k : Nat} {fn : Fn}
    (hc : check src low efp r = true) (h : mkFn src low r k = some fn) :
    fn.k = k ∧ ∃ fr fl e me be rs, FnUnp src low r fn fr fl e me be rs := by
  unfold mkFn at h
  obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hfirst =>
    obtain ⟨mf, hmf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨fl, hfl, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, (r.funcs[k]?).getD { name := f.name }, fl, ?_⟩
    have hS := check_facts hc
    obtain ⟨mf', fl', hmf', hfl', hR⟩ := funcDiag_none (hS.fns _ (mem_placed (r := r) hf))
    rw [hmf] at hmf'
    cases hmf'
    rw [hfl] at hfl'
    cases hfl'
    obtain ⟨e, me, be, rs, he, hme, hbe, hsh, hvm, hp, hrs, hd, htb, hdf, hph⟩ := funcLower_some hfl
    exact ⟨e, me, be, rs, hf, hfirst, rfl, hmf, rfl, hfl, rfl, rfl, rfl, rfl, rfl, hR, he, hme, hbe,
      hsh, hvm, hp, hrs, hd, htb, hdf, hph⟩
  · cases h

/-! ## Lists with distinct keys -/

theorem find?_of_nodup {α : Type} (key : α → Nat) :
    ∀ {l : List α} {a : α}, (l.map key).Nodup → a ∈ l → l.find? (fun y => key y == key a) = some a
  | [], _, _, h => by cases h
  | y :: l, a, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : key y ≠ key a := fun he => hn.1 (he ▸ List.mem_map_of_mem h)
      simp only [List.find?_cons, show (key y == key a) = false by simpa using hne]
      exact find?_of_nodup key hn.2 h

theorem lookup_of_nodup {β : Type} :
    ∀ {l : List (Nat × β)} {p : Nat × β}, (l.map (·.1)).Nodup → p ∈ l → l.lookup p.1 = some p.2
  | [], _, _, h => by cases h
  | y :: l, p, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [List.lookup]
    · have hne : y.1 ≠ p.1 := fun he => hn.1 (he ▸ List.mem_map_of_mem h)
      have : (p.1 == y.1) = false := by simpa using Ne.symm hne
      simp only [List.lookup, this]
      exact lookup_of_nodup hn.2 h

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | [], [], .nil, _, h => by cases h
  | x :: _, y :: _, .cons hr hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hab⟩ := forall₂_mem hs h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hr hs => by rw [List.map_cons, List.map_cons, hfg _ _ hr, forall₂_map_eq hfg hs]

theorem natMap_foldl_away {α β : Type} (key : α → Nat) (val : α → β) :
    ∀ (l : List α) (M : NatMap β) {x : Nat}, (∀ p ∈ l, key p ≠ x) →
      (l.foldl (fun M q => M.insert (key q) (val q)) M).find? x = M.find? x
  | [], _, _, _ => rfl
  | p :: l, M, x, h => by
    rw [List.foldl_cons, natMap_foldl_away key val l _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      NatMap.find?_insert]
    have := h p (List.mem_cons_self ..)
    simp [Ne.symm this]

/-- A fold of inserts with distinct keys into a `NatMap`: each key has its value. -/
theorem natMap_foldl_get {α β : Type} (key : α → Nat) (val : α → β) :
    ∀ (l : List α) (M : NatMap β), (l.map key).Nodup → ∀ a ∈ l,
      (l.foldl (fun M q => M.insert (key q) (val q)) M).find? (key a) = some (val a)
  | [], _, _, a, ha => by cases ha
  | q :: l, M, hnd, a, ha => by
    rw [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [natMap_foldl_away key val l _ (fun p hp e => hnd.1 (by rw [← e]; exact List.mem_map_of_mem hp))]
      simp
    · exact natMap_foldl_get key val l _ hnd.2 a ha

theorem headD_nil_eq {α : Type} (x : List (List α)) : x.headD [] = (x[0]?).getD [] := by
  cases x <;> rfl

/-- The `i`-th of a backward chain of sets, each from the next. -/
theorem foldr_chain_get {α : Type} (h : α → List Nat → List Nat) (base : List (List Nat)) :
    ∀ (l : List α) (i : Nat) (s : α), l[i]? = some s →
      (l.foldr (fun s acc => h s (acc.headD []) :: acc) base)[i]? =
        some (h s (((l.foldr (fun s acc => h s (acc.headD []) :: acc) base)[i + 1]?).getD []))
  | [], _, _, hs => by simp at hs
  | a :: l, 0, s, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    simp only [List.foldr_cons, List.getElem?_cons_zero, List.getElem?_cons_succ, headD_nil_eq]
  | a :: l, i + 1, s, hs => by
    simp only [List.getElem?_cons_succ] at hs
    simp only [List.foldr_cons, List.getElem?_cons_succ]
    exact foldr_chain_get h base l i s hs

theorem livePoints_get {f : HFunc} {L : Live} {b : HBlock} {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) :
    ((livePoints f L b)[i]?).getD [] = stepBack s (((livePoints f L b)[i + 1]?).getD []) := by
  unfold livePoints
  rw [foldr_chain_get _ _ b.body i s hs]
  rfl

theorem go_cons (s : HStmt) (rest : List HStmt) (cs : List Nat) :
    withCallees.go (s :: rest) cs = (s, (calleeOf s cs).1) :: withCallees.go rest (calleeOf s cs).2 := by
  simp only [withCallees.go, calleeOf]
  split <;> simp_all

/-- The statement the walk reaches is paired, in `withCallees`, with the callee place the walk
    gives it. -/
theorem go_walkTo {c : FCtx} {vm : VM} :
    ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt} {cs₀ : List Nat} {i : Nat} {mb₁ : Nat}
      {ms₁ : List Stmt} {cs₁ : List Nat} {s : HStmt},
      walkTo c vm l mb ms cs₀ i = some (mb₁, ms₁, cs₁) → l[i]? = some s →
      (s, (calleeOf s cs₁).1) ∈ withCallees.go l cs₀
  | [], _, _, _, _, _, _, _, _, _, hs => by simp at hs
  | t :: rest, mb, ms, cs₀, 0, mb₁, ms₁, cs₁, s, hw, hs => by
    simp only [walkTo, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    rw [go_cons]; exact List.mem_cons_self ..
  | t :: rest, mb, ms, cs₀, i + 1, mb₁, ms₁, cs₁, s, hw, hs => by
    simp only [walkTo] at hw
    split at hw
    · rw [go_cons]
      exact List.mem_cons_of_mem _ (go_walkTo hw (by simpa using hs))
    · cases hw

/-! ## The function's static facts -/

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

theorem FnUnp.shape' (U : FnUnp src low r fn fr fl e me be rs) :
    fn.f.params.length = fn.c.mf.params.length ∧ fn.c.mf.params.all (·.2 == w256) = true ∧
    fn.f.params.all (Ty.value ·.2) = true ∧ fn.f.rets.length = fn.c.mf.rets.length ∧
    fn.c.mf.rets.all (· == w256) = true ∧ fn.f.rets.all Ty.value = true ∧ e.phis = [] ∧
    (me.id = be ∨ jumpOnly me be = true) ∧ fn.f.defs.Nodup ∧ (fn.f.blocks.map (·.id)).Nodup ∧
    (mdefs fn.c.mf).Nodup ∧
    ∀ b ∈ fn.f.blocks, ∀ d ∈ b.term.succs, ∃ b' ∈ fn.f.blocks, b'.id = d := by
  have h := U.shape
  simp only [funcShapeOk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.isEmpty_iff,
    List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, by simpa using h2, by simpa using h3, h4, by simpa using h5, by simpa using h6, h7, h8,
    distinct_nodup h9, distinct_nodup h10, distinct_nodup h11, fun b hb d hd => ?_⟩
  obtain ⟨b', hb', he⟩ := h12 b hb d hd
  exact ⟨b', hb', by simpa using he⟩

theorem blockCalls_fst (c : FCtx) (f : HFunc) : (blockCalls c f).map (·.1) = f.blocks := by
  unfold blockCalls
  simp [Function.comp_def]

theorem FnUnp.vm (U : FnUnp src low r fn fr fl e me be rs) : fn.F.vm = fl.vm := by
  rw [U.hF]; rfl

theorem FnUnp.frec (U : FnUnp src low r fn fr fl e me be rs) : fn.c.frec = fr := by
  rw [U.hc]; rfl

theorem FnUnp.hsrc (U : FnUnp src low r fn fr fl e me be rs) :
    src.module.func? fn.f.name = some fn.f := by
  obtain ⟨x, hx, hfind⟩ := find_of_firstOf U.first
  rw [U.hf] at hx
  cases hx
  exact hfind

theorem FnUnp.hname (U : FnUnp src low r fn fr fl e me be rs) (hh : hintsOk src low r = true) :
    low.func? fn.f.name = some fn.c.mf := by
  simp only [hintsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hh
  obtain ⟨⟨hlen, hall⟩, -⟩ := hh
  have hk : fn.k < r.funcs.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.mp U.hf).1
  obtain ⟨fr0, hfr0⟩ : ∃ fr0, r.funcs[fn.k]? = some fr0 := ⟨_, List.getElem?_eq_getElem hk⟩
  have hz : (fr0, fn.f) ∈ r.funcs.zip src.module.funcs := by
    rw [List.mem_iff_getElem?]
    exact ⟨fn.k, by rw [List.getElem?_zip_eq_some]; exact ⟨hfr0, U.hf⟩⟩
  obtain ⟨-, hfirst⟩ := hall _ hz
  have hfr : fr = fr0 := by rw [U.hfr, hfr0]; rfl
  subst hfr
  obtain ⟨x, hx, hfind⟩ := find_of_firstOf hfirst
  rw [U.hmf] at hx
  cases hx
  exact hfind

theorem FnUnp.blk (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    fn.f.block? b.id = some b :=
  find?_of_nodup (fun y : HBlock => y.id) U.shape'.2.2.2.2.2.2.2.2.2.1 hb

/-- The region of a block, as `regionsOf` checked it. -/
theorem FnUnp.region (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    ∃ vm' tbk dss bs, blockLower fn.c true fn.F.vm fn.f.rets b (fn.cs b.id) = some (vm', tbk, dss, bs) ∧
      (b.id, tbk, dss, bs) ∈ rs ∧ fl.tb.find? b.id = some tbk ∧ fl.defs.find? b.id = some dss := by
  have hids := U.shape'.2.2.2.2.2.2.2.2.2.1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have hmem : (b, (fn.c.frec.calls[j]?).getD []) ∈ blockCalls fn.c fn.f :=
    List.mem_map.mpr ⟨(b, j), mem_zipIdx_of_getElem? hj, rfl⟩
  have hkeys : ((blockCalls fn.c fn.f).map (·.1.id)).Nodup := by
    have : (blockCalls fn.c fn.f).map (·.1.id) = fn.f.blocks.map (·.id) := by
      rw [← blockCalls_fst fn.c fn.f, List.map_map]; rfl
    rw [this]; exact hids
  have hcs : fn.cs b.id = (fn.c.frec.calls[j]?).getD [] := by
    rw [U.hcs]
    unfold callsOf
    rw [find?_of_nodup (fun y : HBlock × List Nat => y.1.id) hkeys hmem]
    rfl
  have hF2 := mapM_some_forall₂ U.regions
  obtain ⟨x, hx, hbl0⟩ := forall₂_mem hF2 hmem
  dsimp only at hbl0
  obtain ⟨⟨vm', tbk, dss, bs⟩, hbl, hxe⟩ := Option.bind_eq_some_iff.mp hbl0
  simp only [Option.some.injEq] at hxe
  subst hxe
  have hrk : rs.map (·.1) = fn.f.blocks.map (·.id) := by
    rw [← forall₂_map_eq (f := fun y : HBlock × List Nat => y.1.id) (g := (·.1)) ?_ hF2]
    · rw [← blockCalls_fst fn.c fn.f, List.map_map]; rfl
    · intro a y hy
      obtain ⟨⟨_, t, d, q⟩, _, hy⟩ := Option.bind_eq_some_iff.mp hy
      simp only [Option.some.injEq] at hy
      subst hy; rfl
  have hrn : (rs.map (·.1)).Nodup := by rw [hrk]; exact hids
  refine ⟨vm', tbk, dss, bs, by rw [hcs, U.vm]; exact hbl, hx, ?_, ?_⟩
  · rw [U.tbOf, NatMap.find?_ofList]
    refine lookup_of_nodup (p := (b.id, tbk)) ?_ (List.mem_map.mpr ⟨_, hx, rfl⟩)
    rw [List.map_map]; exact hrn
  · rw [U.defsEq, NatMap.find?_ofList]
    refine lookup_of_nodup (p := (b.id, dss)) ?_ (List.mem_map.mpr ⟨_, hx, rfl⟩)
    rw [List.map_map]; exact hrn

/-- The walk of a block: its region starts at `fn.start`, every statement is walked, and it
    ends in the block `tb` records, with the machine values of each statement `defs` records. -/
theorem FnUnp.walkOk (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    ∃ mb mblk tbk ms cs dss tblk, fn.start b = some (mb, mblk) ∧
      fn.pos b b.body.length = some (tbk, ms, cs) ∧ fn.tb.find? b.id = some tbk ∧
      fl.defs.find? b.id = some dss ∧ fn.c.mf.block? tbk = some tblk ∧
      termOk fn.c fn.F.vm fn.f.rets b.term ms tblk.term = true ∧
      ∀ (i : Nat) (s : HStmt) (mb₁ : Nat) (ms₁ : List Stmt) (cs₁ : List Nat) (vm₂ : VM) (mb₂ : Nat)
        (ms₂ : List Stmt) (ds : List Nat), b.body[i]? = some s → fn.pos b i = some (mb₁, ms₁, cs₁) →
        stmt fn.c true fn.F.vm s mb₁ ms₁ (calleeOf s cs₁).1 = some (vm₂, mb₂, ms₂, ds) → dss[i]? = some ds := by
  obtain ⟨vm', tbk, dss, bs, hbl, -, htb, hdf⟩ := U.region hb
  obtain ⟨mb, mblk, ms, bs', tblk, hmb, hmblk, hw, htblk, ht, -⟩ := blockLower_some hbl
  obtain ⟨hv, ⟨cs', hto⟩, hds⟩ := walk_walkTo hw
  subst hv
  have hst : fn.start b = some (mb, mblk) := by simp [Fn.start, hmb, hmblk]
  refine ⟨mb, mblk, tbk, ms, cs', dss, tblk, hst, by simp [Fn.pos, hst, hto], by rw [U.htb]; exact htb,
    hdf, htblk, ht, fun i s mb₁ ms₁ cs₁ vm₂ mb₂ ms₂ ds hs hp hstm => ?_⟩
  simp only [Fn.pos, hst, Option.bind_eq_bind, Option.bind_some] at hp
  exact hds i s mb₁ ms₁ cs₁ vm₂ mb₂ ms₂ ds hs hp hstm

theorem FnUnp.walks (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    (fn.pos b b.body.length).isSome := by
  obtain ⟨_, _, _, _, _, _, _, _, hp, _⟩ := U.walkOk hb
  rw [hp]; rfl

theorem FnUnp.ids (U : FnUnp src low r fn fr fl e me be rs) : (fn.f.blocks.map (·.id)).Nodup :=
  U.shape'.2.2.2.2.2.2.2.2.2.1

/-- The callee places of the block at place `j`. -/
theorem FnUnp.csj (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} {j : Nat}
    (hj : fn.f.blocks[j]? = some b) : fn.cs b.id = (fr.calls[j]?).getD [] := by
  have hmem : (b, (fn.c.frec.calls[j]?).getD []) ∈ blockCalls fn.c fn.f :=
    List.mem_map.mpr ⟨(b, j), mem_zipIdx_of_getElem? hj, rfl⟩
  have hkeys : ((blockCalls fn.c fn.f).map (·.1.id)).Nodup := by
    have : (blockCalls fn.c fn.f).map (·.1.id) = fn.f.blocks.map (·.id) := by
      rw [← blockCalls_fst fn.c fn.f, List.map_map]; rfl
    rw [this]; exact U.ids
  rw [U.hcs, ← U.frec]
  unfold callsOf
  rw [find?_of_nodup (fun y : HBlock × List Nat => y.1.id) hkeys hmem]
  rfl

theorem FnUnp.live (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    (i : Nat) : fn.live b i = ((livePoints fn.f fn.L b)[i]?).getD [] := by
  unfold Fn.live ptsAt
  rw [U.hpts]
  unfold pointsOf
  rw [natMap_foldl_get (fun b : HBlock => b.id) (livePoints fn.f fn.L) _ _ U.ids b hb]
  rfl

theorem sublist_flatMap {α β : Type} {f : α → List β} {a : α} :
    ∀ {l : List α}, a ∈ l → List.Sublist (f a) (l.flatMap f)
  | [], h => by cases h
  | x :: l, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap h).trans (List.sublist_append_right _ _)

theorem FnUnp.dsts_nodup (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock}
    (hb : b ∈ fn.f.blocks) {s : HStmt} (hs : s ∈ b.body) : (s.dsts.map (·.1)).Nodup := by
  refine U.shape'.2.2.2.2.2.2.2.2.1.sublist ?_
  unfold HFunc.defs
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  refine List.Sublist.trans ?_ (sublist_flatMap (f := fun b : HBlock =>
    b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) hb)
  exact (sublist_flatMap (f := fun s : HStmt => s.dsts.map (·.1)) hs).trans (List.sublist_append_right _ _)

theorem FnUnp.decl (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {s : HStmt} (hs : s ∈ b.body) {d : Nat × Ty} (hd : d ∈ s.dsts) :
    (declsOf fn.f).find? d.1 = some d.2 := by
  unfold declsOf
  rw [NatMap.find?_ofList]
  refine lookup_of_nodup ?_ ?_
  · have : (fn.f.params ++ fn.f.blocks.flatMap fun b =>
        b.phis.map (fun p => (p.dst, p.ty)) ++ b.body.flatMap (·.dsts)).map (·.1) = fn.f.defs := by
      simp [HFunc.defs, List.map_flatMap, Function.comp_def]
    rw [this]; exact U.shape'.2.2.2.2.2.2.2.2.1
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, List.mem_append_right _
      (List.mem_flatMap.mpr ⟨s, hs, hd⟩)⟩)

/-- The walk's position before statement `i` of block `b`, from the block's region start. -/
theorem FnUnp.posWalk (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {i : Nat} {mb : Nat} {ms : List Stmt} {cs : List Nat} (hp : fn.pos b i = some (mb, ms, cs)) :
    ∃ (mb₀ : Nat) (mblk₀ : Block) (j : Nat), fn.start b = some (mb₀, mblk₀) ∧ fn.f.blocks[j]? = some b ∧
      walkTo fn.c fn.F.vm b.body mb₀ mblk₀.body ((fr.calls[j]?).getD []) i = some (mb, ms, cs) := by
  obtain ⟨mb₀, mblk₀, _, _, _, _, _, hst, -⟩ := U.walkOk hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  refine ⟨mb₀, mblk₀, j, hst, hj, ?_⟩
  simp only [Fn.pos, hst, Option.bind_eq_bind, Option.bind_some] at hp
  rw [U.csj hj] at hp
  exact hp

/-- The facts `At` at every statement the walk reaches. -/
theorem FnUnp.at {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r)
    {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt} (hs : b.body[i]? = some s)
    {mb : Nat} {ms : List Stmt} {cs : List Nat} (hp : fn.pos b i = some (mb, ms, cs))
    {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hst : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds)) :
    At (secS src r efp) fn.F fn.c (secX src r).derived fn.k s (calleeOf s cs).1 (fn.live b i)
      (fn.live b (i + 1)) ds := by
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have hR := U.rules
  have hLi : fn.live b i = stepBack s (fn.live b (i + 1)) := by
    rw [U.live hb, U.live hb]; exact livePoints_get hs
  have hFv : fn.F.vm = fl.vm := U.vm
  have hFO : fn.F.O = (secX src r).origAt fn.k := by rw [U.hF]; rfl
  refine ⟨?decls, ?dsts, ?uses, ?keep, ?clob, U.dsts_nodup hb hsm, ?self, ?s3, ?orig, ?D, ?obs, ?der⟩
  case decls => rw [U.hF, U.hc]; rfl
  case dsts => intro d hd; rw [U.hF]; exact U.decl hb hsm hd
  case uses =>
    intro y hy; rw [hLi]; unfold stepBack; rw [mem_nset]
    exact List.mem_append_left _ (by unfold HStmt.uses varsOf; exact List.mem_filterMap.mpr ⟨_, hy, rfl⟩)
  case keep =>
    intro y hy hn; rw [hLi]; unfold stepBack; rw [mem_nset]
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hn⟩)
  case clob =>
    obtain ⟨_, _, _, _, _, dss, _, _, _, _, hdf, _, _, hdss⟩ := U.walkOk hb
    have hdi := hdss i s mb ms cs vm' mb' ms' ds hs hp hst
    have h := hR.clob
    simp only [clobberOk, List.all_eq_true, Bool.and_eq_true] at h
    have hz : ((s, i), ds) ∈ b.body.zipIdx.zip ((fl.defs.find? b.id).getD []) := by
      rw [hdf]
      refine mem_zip_of ?_ hdi
      rw [List.getElem?_zipIdx, hs]; simp
    have h2 := (h b hb).2 _ hz
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h2
    intro y hy hn m hm heq
    rcases h2 with h2 | h2
    · subst h2; cases hm
    · have hpL : fn.pts = pointsOf fn.f (liveRec fr fn.f) := by rw [U.hpts, U.hL]
      unfold Fn.live at hy
      rw [hpL] at hy
      rw [hFv] at heq
      have : ((ptsAt (pointsOf fn.f (liveRec fr fn.f)) b.id i ++
          ptsAt (pointsOf fn.f (liveRec fr fn.f)) b.id (i + 1)).any fun y =>
            !s.defs.contains y && ds.any fun m => fl.vm.find? y == some (.var m)) = true :=
        List.any_eq_true.mpr ⟨y, by rcases hy with hy | hy <;> simp [hy],
          by simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
              decide_eq_false_iff_not, List.any_eq_true, beq_iff_eq]; exact ⟨hn, m, hm, heq⟩⟩
      rw [this] at h2; cases h2
  case self =>
    intro y hy hd
    have h := hR.self
    simp only [selfFree, List.all_eq_true, Bool.not_eq_true'] at h
    have h1 := h b hb s hsm y hd
    have : y ∈ s.uses := by unfold HStmt.uses varsOf; exact List.mem_filterMap.mpr ⟨_, hy, rfl⟩
    simp [this] at h1
  case s3 =>
    intro a v hav
    have h := hR.s3
    simp only [s3Uses, List.all_eq_true, Bool.and_eq_true] at h
    have h1 := (h b hb).1 s hsm
    rw [hFO]
    rcases hav with ⟨t, ht⟩ | ht <;> rw [ht] at h1 <;> simpa using h1
  case orig =>
    intro x t hd o ho
    have h := hR.orig
    simp only [origOk, List.all_eq_true, Bool.and_eq_true] at h
    have h1 := ((h.2 b hb).2 s hsm)
    rw [hd] at h1
    simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h1
    rw [U.frec, hFO] at ho
    rw [hFO]
    exact h1 o ho
  case D => rw [U.hF]; rfl
  case obs =>
    intro hz i a ha hd
    exact notObserved_stmt (hR.s8 hz) hb hsm ha hd
  case der =>
    intro hz hd x hx
    obtain ⟨mb₀, mblk₀, j, -, hj, hw⟩ := U.posWalk hb hp
    have hf : (fn.k, fn.f, withCallees fr fn.f) ∈ derivedInput (secP src r) := by
      have := mem_placed (r := r) U.hf
      rw [← U.hfr] at this
      exact List.mem_map.mpr ⟨_, this, rfl⟩
    have hwj : (withCallees fr fn.f)[j]? = some (withCallees.go b.body ((fr.calls[j]?).getD [])) := by
      unfold withCallees
      rw [List.getElem?_map, List.getElem?_zipIdx, hj]; simp
    exact derivedOk_stmt (hS.der hz) hf (mem_zip_of hj hwj) (go_walkTo hw hs) hd x hx

end unp


/-! ## The statements left are a suffix of a machine block's body -/

/-- Machine block `mb₁` with statements `ms₁` left is the block `mb` with a suffix of `ms`, or a
    block with a suffix of its body. -/
def PosOk (mf : Func) (mb : Nat) (ms : List Stmt) (mb₁ : Nat) (ms₁ : List Stmt) : Prop :=
  (mb₁ = mb ∧ List.IsSuffix ms₁ ms) ∨ ∃ jb, mf.block? mb₁ = some jb ∧ List.IsSuffix ms₁ jb.body

def Sfx (mf : Func) (mb : Nat) (ms : List Stmt) (o : Option Step) : Prop :=
  ∀ x, o = some x → PosOk mf mb ms x.2.1 x.2.2.1

section sfx

variable {mf : Func} {mb : Nat} {ms : List Stmt}

theorem sfx_none : Sfx mf mb ms none := fun _ h => by cases h
theorem sfx_none_bind {α : Type} {f : α → Option Step} : Sfx mf mb ms ((none : Option α) >>= f) :=
  fun _ h => by cases h
theorem sfx_same {vm : VM} {ms₁ : List Stmt} {ds : List Nat} (h : List.IsSuffix ms₁ ms) :
    Sfx mf mb ms (some (vm, mb, ms₁, ds)) := fun _ hx => by cases hx; exact Or.inl ⟨rfl, h⟩
theorem sfx_join {vm : VM} {mb₁ : Nat} {jb : Block} {ms₁ : List Stmt} {ds : List Nat}
    (hj : mf.block? mb₁ = some jb) (h : List.IsSuffix ms₁ jb.body) :
    Sfx mf mb ms (some (vm, mb₁, ms₁, ds)) := fun _ hx => by cases hx; exact Or.inr ⟨jb, hj, h⟩
theorem sfx_bind {α : Type} {a : Option α} {f : α → Option Step} (h : ∀ y, Sfx mf mb ms (f y)) :
    Sfx mf mb ms (a.bind f) := fun x hx => by
  cases a with
  | none => cases hx
  | some y => exact h y x hx
theorem sfx_ite {p : Prop} [Decidable p] {a b : Option Step} (ha : Sfx mf mb ms a)
    (hb : Sfx mf mb ms b) : Sfx mf mb ms (if p then a else b) := by
  split
  · exact ha
  · exact hb
theorem sfx_block {jn : Nat} {f : Block → Option Step}
    (h : ∀ jb, mf.block? jn = some jb → Sfx mf mb ms (f jb)) :
    Sfx mf mb ms ((mf.block? jn).bind f) := fun x hx => by
  cases hb : mf.block? jn with
  | none => rw [hb] at hx; cases hx
  | some jb => rw [hb] at hx; exact h jb hb x hx
theorem sfx_take1 {inst : Inst} {ms₁ : List Stmt} {f : Nat × List Stmt → Option Step}
    (h₁ : List.IsSuffix ms₁ ms) (h : ∀ r ms₂, List.IsSuffix ms₂ ms → Sfx mf mb ms (f (r, ms₂))) :
    Sfx mf mb ms ((take1 inst ms₁).bind f) := fun x hx => by
  cases ht : take1 inst ms₁ with
  | none => rw [ht] at hx; cases hx
  | some y =>
    rw [ht] at hx
    obtain ⟨r, ms₂⟩ := y
    have := take1_some ht
    exact h r ms₂ (List.IsSuffix.trans (by rw [this]; exact List.suffix_cons _ _) h₁) x hx
theorem sfx_take0 {inst : Inst} {ms₁ : List Stmt} {f : List Stmt → Option Step}
    (h₁ : List.IsSuffix ms₁ ms) (h : ∀ ms₂, List.IsSuffix ms₂ ms → Sfx mf mb ms (f ms₂)) :
    Sfx mf mb ms ((take0 inst ms₁).bind f) := fun x hx => by
  cases ht : take0 inst ms₁ with
  | none => rw [ht] at hx; cases hx
  | some ms₂ =>
    rw [ht] at hx
    have := take0_some ht
    exact h ms₂ (List.IsSuffix.trans (by rw [this]; exact List.suffix_cons _ _) h₁) x hx
theorem sfx_takeN {inst : Inst} {n : Nat} {ms₁ : List Stmt} {f : List Nat × List Stmt → Option Step}
    (h₁ : List.IsSuffix ms₁ ms) (h : ∀ rs ms₂, List.IsSuffix ms₂ ms → Sfx mf mb ms (f (rs, ms₂))) :
    Sfx mf mb ms ((takeN inst n ms₁).bind f) := fun x hx => by
  cases ht : takeN inst n ms₁ with
  | none => rw [ht] at hx; cases hx
  | some y =>
    rw [ht] at hx
    obtain ⟨rs, ms₂⟩ := y
    obtain ⟨_, he, _⟩ := takeN_some ht
    exact h rs ms₂ (List.IsSuffix.trans (by rw [he]; exact List.suffix_cons _ _) h₁) x hx
theorem sfx_gep {c : FCtx} {vm : VM} {addr : Operand} {k : Nat} {ty : Ty} {idxs : List Operand}
    {ms₁ : List Stmt} {f : Operand × List Stmt × List Nat → Option Step}
    (h₁ : List.IsSuffix ms₁ ms)
    (h : ∀ a ms₂ ds, List.IsSuffix ms₂ ms → Sfx mf mb ms (f (a, ms₂, ds))) :
    Sfx mf mb ms ((gepWalk c vm addr k ty idxs ms₁).bind f) := fun x hx => by
  cases ht : gepWalk c vm addr k ty idxs ms₁ with
  | none => rw [ht] at hx; cases hx
  | some y =>
    rw [ht] at hx
    obtain ⟨a, ms₂, ds⟩ := y
    obtain ⟨pre, he, _⟩ := gepWalk_shape idxs addr k ty ms₁ a ms₂ ds ht
    exact h a ms₂ ds (List.IsSuffix.trans (by rw [he]; exact List.suffix_append _ _) h₁) x hx

end sfx

theorem mallocSize_sfx {vm : VM} {a szo : Operand} {ms ms2 : List Stmt} {dsz : List Nat}
    (h : mallocSize vm a ms = some (szo, ms2, dsz)) : List.IsSuffix ms2 ms := by
  have dyn : mallocSize.dyn vm a ms = some (szo, ms2, dsz) → List.IsSuffix ms2 ms := by
    intro h
    simp only [mallocSize.dyn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨a'', -, ⟨t, r1⟩, ht, ⟨sz, r2⟩, hs, rfl, rfl, rfl⟩ := h
    have hm1 := take1_some ht
    have hm2 := take1_some hs
    simp only at hm1 hm2
    rw [hm1, hm2]
    exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  cases a with
  | imm bits n =>
    simp only [mallocSize] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact List.suffix_refl _
    · exact dyn h
  | var y => exact dyn h

/-- After a statement of the checking walk, the machine statements left are a suffix of those
    before it in the same block, or a suffix of the body of the block it continues in. -/
theorem stmt_sfx (c : FCtx) (vm : VM) (s : HStmt) (mb : Nat) (ms : List Stmt)
    (callee? : Option Nat) : Sfx c.mf mb ms (stmt c true vm s mb ms callee?) := by
  unfold stmt
  split
  case h_22 a x tx _ _ =>
    intro y hy
    obtain ⟨vm', mb', ms', ds⟩ := y
    rcases hl : c.frec.mallocs.lookup x with _ | m
    · simp [hl] at hy
    rcases m with ⟨minBase, _ | eb, _ | _⟩ | ⟨base, rule⟩
    · simp [hl] at hy
    · obtain ⟨-, -, -, b0, rest1, base, mb1, ms1, dc, szo, ms2, dsz, nf, ms3, h0, hcl, hsz, h2, h3, -,
        rfl, -⟩ := stmt_heap (s := ⟨[(x, tx)], .base (.malloc a)⟩) (c := c) (vm := vm) (mb := mb)
        (ms := ms) (callee? := callee?) rfl rfl hl hy
      have e1 : List.IsSuffix ms' ms3 := by rw [h3]; exact List.suffix_cons _ _
      have e2 : List.IsSuffix ms3 ms2 := by rw [h2]; exact List.suffix_cons _ _
      have hs3 := e1.trans (e2.trans (mallocSize_sfx hsz))
      rcases hcl with ⟨-, cnd, cur, lb, rb, mlb, mrb, jn, jb, φ, -, -, -, -, -, -, -, -, hjb, -, -, -, -,
          rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩
      · exact Or.inr ⟨jb, hjb, hs3⟩
      · exact Or.inl ⟨rfl, hs3.trans (by rw [h0]; exact List.suffix_cons _ _)⟩
    · simp [hl] at hy
    · simp [hl] at hy
    · simp [hl, bindV] at hy
      obtain ⟨-, hy⟩ := hy
      split at hy
      · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hy
        obtain ⟨-, rfl, rfl, -⟩ := hy
        exact Or.inl ⟨rfl, List.suffix_refl _⟩
      · cases hy
  all_goals
    simp only [Option.bind_eq_bind]
    repeat
      first
      | with_reducible exact sfx_none
      | with_reducible exact sfx_none_bind
      | (with_reducible refine sfx_same ?_; first | exact List.suffix_refl _ | assumption)
      | (with_reducible refine sfx_join (by assumption) (List.suffix_refl _))
      | (with_reducible refine sfx_take1 ?_ ?_; (first | exact List.suffix_refl _ | assumption); intro _ _ _)
      | (with_reducible refine sfx_take0 ?_ ?_; (first | exact List.suffix_refl _ | assumption); intro _ _)
      | (with_reducible refine sfx_takeN ?_ ?_; (first | exact List.suffix_refl _ | assumption); intro _ _ _)
      | (with_reducible refine sfx_gep ?_ ?_; (first | exact List.suffix_refl _ | assumption); intro _ _ _ _)
      | (with_reducible refine sfx_block ?_; intro _ _)
      | (with_reducible apply sfx_bind; intro _)
      | with_reducible apply sfx_ite
      | split

theorem walkTo_len {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} {j : Nat} {x : Nat × List Stmt × List Nat},
    walkTo c vm l mb ms cs j = some x → j ≤ l.length
  | _, _, _, _, 0, _, _ => Nat.zero_le _
  | [], _, _, _, _ + 1, _, h => by simp [walkTo] at h
  | s :: rest, mb, ms, cs, j + 1, x, h => by
    simp only [walkTo] at h
    split at h
    · have := walkTo_len h; simp only [List.length_cons]; omega
    · cases h

theorem PosOk.trans {mf : Func} {mb mb₁ mb₂ : Nat} {ms ms₁ ms₂ : List Stmt}
    (h₁ : PosOk mf mb ms mb₁ ms₁) (h₂ : PosOk mf mb₁ ms₁ mb₂ ms₂) : PosOk mf mb ms mb₂ ms₂ := by
  rcases h₂ with ⟨rfl, h₂⟩ | h₂
  · rcases h₁ with ⟨rfl, h₁⟩ | ⟨jb, hj, h₁⟩
    · exact Or.inl ⟨rfl, h₂.trans h₁⟩
    · exact Or.inr ⟨jb, hj, h₂.trans h₁⟩
  · exact Or.inr h₂

section unp2

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- At every position the walk reaches, the statements left are a suffix of a block's body. -/
theorem FnUnp.posOk (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks) :
    ∀ i mb ms cs, fn.pos b i = some (mb, ms, cs) →
      ∃ mblk, fn.c.mf.block? mb = some mblk ∧ List.IsSuffix ms mblk.body := by
  obtain ⟨mb₀, mblk₀, _, _, _, _, _, hst, -⟩ := U.walkOk hb
  have hP : ∀ i mb ms cs, fn.pos b i = some (mb, ms, cs) → PosOk fn.c.mf mb₀ mblk₀.body mb ms := by
    intro i
    induction i with
    | zero =>
      intro mb ms cs hp
      rw [pos_zero hst] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, -⟩ := hp
      exact Or.inl ⟨rfl, List.suffix_refl _⟩
    | succ i ih =>
      intro mb ms cs hp
      have hlen : i + 1 ≤ b.body.length := by
        simp only [Fn.pos, hst, Option.bind_eq_bind, Option.bind_some] at hp
        exact walkTo_len hp
      obtain ⟨s, hs⟩ : ∃ s, b.body[i]? = some s := ⟨b.body[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hp' : (fn.pos b i).isSome := by
        simp only [Fn.pos, hst, Option.bind_eq_bind, Option.bind_some] at hp ⊢
        exact walkTo_le (i := i) (j := i + 1) (by omega) (by rw [hp]; rfl)
      obtain ⟨⟨mb₁, ms₁, cs₁⟩, hp1⟩ := Option.isSome_iff_exists.mp hp'
      have hw1 := hp1
      simp only [Fn.pos, hst, Option.bind_eq_bind, Option.bind_some] at hw1 hp
      obtain ⟨vm', mb₂, ms₂, ds, hstm, hx⟩ := walkTo_succ hw1 hs hp
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, -⟩ := hx
      exact (ih mb₁ ms₁ cs₁ hp1).trans (stmt_sfx fn.c fn.F.vm s mb₁ ms₁ _ _ hstm)
  intro i mb ms cs hp
  rcases hP i mb ms cs hp with ⟨rfl, h⟩ | ⟨jb, hj, h⟩
  · exact ⟨mblk₀, start_block hst, h⟩
  · exact ⟨jb, hj, h⟩

/-- At every position the walk reaches, the statements left define distinct machine values. -/
theorem FnUnp.nodup (U : FnUnp src low r fn fr fl e me be rs) {b : HBlock} (hb : b ∈ fn.f.blocks)
    {i mb : Nat} {ms : List Stmt} {cs : List Nat} (hp : fn.pos b i = some (mb, ms, cs)) :
    (defsOf ms).Nodup := by
  obtain ⟨mblk, hmb, pre, hpre⟩ := U.posOk hb i mb ms cs hp
  have hmem : mblk ∈ fn.c.mf.blocks := List.mem_of_find?_eq_some hmb
  refine U.shape'.2.2.2.2.2.2.2.2.2.2.1.sublist ?_
  have hd : defsOf ms = ms.flatMap fun st => st.dsts.map (·.1) := by simp [defsOf, List.map_flatMap]
  rw [hd]
  unfold mdefs
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  refine List.Sublist.trans ?_ (sublist_flatMap (f := fun b : Block =>
    b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) hmem)
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  rw [← hpre, List.flatMap_append]
  exact List.sublist_append_right _ _

end unp2

/-- Every function of the section that is the first of its name has its `Fn`. -/
theorem mkFn_some {src : HSection} {low : Module} {efp : Option Nat} {r : Record} {k : Nat}
    {f : HFunc} (hc : check src low efp r = true) (hf : src.module.funcs[k]? = some f)
    (hfirst : firstOf (·.name) src.module.funcs k f.name = true) :
    ∃ fn, mkFn src low r k = some fn ∧ fn.f = f := by
  obtain ⟨mf, fl, hmf, hfl, -⟩ := funcDiag_none ((check_facts hc).fns _ (mem_placed (r := r) hf))
  unfold mkFn
  simp only [hf, Option.bind_eq_bind, Option.bind_some, hfirst, ite_true, hmf, hfl]
  exact ⟨_, rfl, rfl⟩

end Fe.Sonatina.Stage3.Place
