import Fe.Sonatina.Stage3.Place.Facts
import Fe.Sonatina.Stage3.Place.FixInv
import Fe.Sonatina.Stage3.Place.InstEvmCalls
import Fe.Sonatina.Stage3.Place.Bytes
import Fe.Sonatina.Stage3.Place.Clamp
import Fe.Sonatina.Stage3.Place.Term

/-!
# Every statement is one of the three kinds (`StmtObl`)

`FnUnp.stmtObl`: at every statement the checking walk reaches, the pattern `stmt` matched gives
its obligation: a plain template (`StdK`) by its pattern lemma, a diamond (`DiaK`: the dynamic
`evm_mload_bytes`, the heap base clamp), or a terminal fixed buffer (`FixK`, rule S6), whose
obligation the dispatch takes (`FixSiteOk`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

theorem stdK_of {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {CP : Oracle → Prop}
    {fn : Fn} {b : HBlock} {i : Nat} {s : HStmt} {mb : Nat} {ms : List Stmt} {mb' : Nat}
    {ms' : List Stmt}
    (h : ∀ g hst w envH envM, Inv S hst w g → EnvRel S.z fn.F g hst envH envM (fn.live b i) →
      ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧
        TemplOk P I cM S fn.F g hst w envH envM s (fn.live b (i + 1)) pre) :
    StdK P I cM S CP fn b i s mb ms mb' ms' := fun O _ g hst w envH envM hI hE => by
  obtain ⟨pre, h1, h2, h3⟩ := h g hst w envH envM hI hE
  exact ⟨pre, h1, h2, h3 O⟩

/-- The terminal fixed buffers of `fn`, as the dispatch needs their obligation. -/
def FixSiteOk (src : HSection) (low : Module) (r : Record) (efp : Option Nat) (I : Fe.EVM.Env)
    (cM : Ctx) (CP : Oracle → Prop) (fn : Fn) : Prop :=
  ∀ b ∈ fn.f.blocks, ∀ i s, b.body[i]? = some s → ∀ mb ms cs, fn.pos b i = some (mb, ms, cs) →
    ∀ a x tx base rule, s.inst = .base (.malloc a) → s.dsts = [(x, tx)] →
      fn.c.frec.mallocs.lookup x = some (.fixed base rule) →
      FixK src I cM (secS src r efp) (secX src r).derived CP FixInv fn b i mb ms

section disp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- Every statement the walk reaches is one of the three kinds. -/
theorem FnUnp.stmtObl {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hc : check src low efp r = true) {I : Fe.EVM.Env} (hcd : I.calldata.size < W) {cM : Ctx}
    (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (hFix : FixSiteOk src low r efp I cM
      (CallP src I (secS src r efp) (secX src r).derived (mkFn src low r)) fn) :
    StmtObl src I cM (secS src r efp) (secX src r).derived
      (CallP src I (secS src r efp) (secX src r).derived (mkFn src low r)) FixInv fn := by
  intro b hb i s hs mb ms cs hp vm' mb' ms' ds hst
  have hS := check_facts hc
  have hA := U.at hS hb hs hp hst
  have hnd := U.nodup hb hp
  have hmd : (mdefs fn.c.mf).Nodup := U.shape'.2.2.2.2.2.2.2.2.2.2.1
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have h0 := hst
  unfold stmt at h0
  split at h0
  next op a b' x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_bin hI hE hA hi hd hst)
  next op a b' x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_cmp hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_isZero hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_unary (mk := Inst.not) (Or.inl rfl) hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_unary (mk := Inst.neg) (Or.inr (Or.inl rfl)) hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_unary (mk := Inst.clz) (Or.inr (Or.inr (Or.inl rfl))) hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_unary (mk := Inst.ctz) (Or.inr (Or.inr (Or.inr rfl))) hI hE hA hi hd hst)
  next op a b' x tx y ty hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_ovf hI hE hA hnd hi hd hst)
  next op a b' t x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_sat hI hE hA hi hd hst)
  next op a t x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_cast hI hE hA hi hd hst)
  next a x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_blackBox hI hE hA hi hd hst)
  next sym x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_symAddr U.cSym hcM hI hE hA hi hd hst)
  next sym x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_symSize U.cSym hcM hI hE hA hi hd hst)
  next dsts op args hi =>
    cases hfree : op.memFree
    · exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_evmMem hfree hI hE hA hi hst)
    · exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_evmFree hfree hI hE hA hi hst)
  next a t x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_mload hI hE hA hi hd hst)
  next a v t hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_mstore hI hE hA hi hd hst)
  next d l hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_memzero hcd hI hE hA hi hd hst)
  next a l x tx hi hd =>
    cases l with
    | imm bits n =>
      exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_bytesImm hI hE hA hi hd hst)
    | var y => exact Or.inr (Or.inl (DiaOk.diaK (inst_bytesDyn hA hmd hi hd hst)))
  next a t x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => inst_truncNuw hI hE hA hi hd hst)
  next bt base idxs x tx hi hd =>
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_gep (by rw [U.cSrc]) hI hE hA hnd hi hd hst)
  next t x tx hi hd =>
    obtain ⟨hRx, hsec, hA1⟩ := U.allocaFacts hS hb hs hp hi hd
    exact Or.inl (stdK_of fun _ _ _ _ _ hI hE =>
      inst_alloca (by rw [U.cSrc]) hRx hsec hA1 hI hE hA hi hd hst)
  next a x tx hi hd =>
    rcases hl : fn.c.frec.mallocs.lookup x with _ | m
    · simp [hl] at h0
    rcases m with ⟨minBase, _ | eb, _ | _⟩ | ⟨base, rule⟩
    · simp [hl] at h0
    · obtain ⟨hheap, hF0, hmin⟩ := U.heapFacts hS hb hsm hd hl
      obtain ⟨hwx, hta, -, b0, rest1, base, mb1, ms1, dc, szo, ms2, dsz, nf, ms3, hms, hcl, hsz,
        hms2, hms3, hx, hmb, hds⟩ := stmt_heap hi hd hl hst
      rcases hcl with hcl | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl (DiaOk.diaK (inst_clamp hheap hF0 hmin hA hmd hnd hi hd hwx hta hms hcl
          hsz hms2 hms3 hx hmb hds)))
      · have hds' : ds.Nodup := by
          obtain ⟨pre2, hpre2, hdsz⟩ := mallocSize_defs hsz
          have : defsOf ms = ds ++ defsOf ms' := by
            rw [hms, hpre2, hms2, hms3, hds, hdsz]
            simp [defsOf, List.flatMap_append]
          rw [this] at hnd
          exact (List.nodup_append.mp hnd).1
        exact Or.inl (stdK_of fun _ _ _ _ _ hI hE => by
          obtain ⟨pre, h1, h2⟩ := inst_heap hheap hF0 hI hE hA hds' hi hd hwx hta hms hsz hms2 hms3
            hx hds
          exact ⟨pre, h1, hmb, h2⟩)
    · simp [hl] at h0
    · simp [hl] at h0
    · exact Or.inr (Or.inr (hFix b hb i s hs mb ms cs hp a x tx base rule hi hd hl))
  next gn args dsts hi =>
    exact Or.inl fun O hO g hst' w envH envM hI hE =>
      inst_call hO hI hE hA hnd hi hst (U.callFacts hc hb hs hp hi)
  next => simp at h0

end disp

/-- What the terminal fixed buffers of `fn` need: their obligation and the invariant `FixInv`
    of H's runs of `fn`. -/
structure FixObls (src : HSection) (low : Module) (r : Record) (efp : Option Nat) (I : Fe.EVM.Env)
    (cM : Ctx) (fn : Fn) : Prop where
  site : FixSiteOk src low r efp I cM
    (CallP src I (secS src r efp) (secX src r).derived (mkFn src low r)) fn
  qEntry : ∀ e, fn.f.blocks.head? = some e → ∀ vs envH, bindVals {} fn.f.params vs = some envH →
    ∀ envH₁, H.enter envH none e = some envH₁ → FixInv fn e 0 envH₁
  qStep : ∀ b ∈ fn.f.blocks, ∀ i s, b.body[i]? = some s → ∀ envH hst envH' hst', FixInv fn b i envH →
    ExecBody src I envH [s] hst (.cont envH' hst') → FixInv fn b (i + 1) envH'
  qEdge : ∀ b ∈ fn.f.blocks, ∀ envH hst d, FixInv fn b b.body.length envH →
    stepTerm I envH hst b.term = .goto d → ∀ db ∈ fn.f.blocks, db.id = d →
    ∀ envH₁, H.enter envH (some b.id) db = some envH₁ → FixInv fn db 0 envH₁

/-- Every function of the section the check accepts satisfies the simulation's obligations. -/
theorem fnOk_of {src : HSection} {low : Module} {r : Record} {efp : Option Nat} {k : Nat} {fn : Fn}
    (hc : check src low efp r = true) (hk : mkFn src low r k = some fn) {I : Fe.EVM.Env}
    (hcd : I.calldata.size < W) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (hX : FixObls src low r efp I cM fn) :
    FnOk src I cM (secS src r efp) (secX src r).derived
      (CallP src I (secS src r efp) (secX src r).derived (mkFn src low r)) FixInv low fn := by
  have hS := check_facts hc
  obtain ⟨-, fr, fl, e, me, be, rs, U⟩ := fn_unp hc hk
  exact ⟨U.hname hS.hints, U.hsrc, fun b hb => U.blk hb, fun b hb => U.walks hb, U.entryObl I,
    U.phiObl hS I, U.stmtObl hc hcd hcM hX.site, U.termObl hS I cM, hX.qEntry, hX.qStep, hX.qEdge⟩

end Fe.Sonatina.Stage3.Place
