import Fe.Sonatina.Stage3.Place.FixSfx
import Fe.Sonatina.Stage3.Place.InstPure
import Fe.Sonatina.Stage3.Place.InstGep
import Fe.Sonatina.Stage3.Place.InstMem

/-!
# After a terminal fixed buffer: one statement

`FnUnp.sfxPureStep`: a pure statement after the site keeps `SR`, by its pattern lemma against
the virtual state.  `FnUnp.sfxStoreStep`: a store through the buffer (rule S6: its address is a
must-origin value) writes the buffer's cells and the machine's bytes alike.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

section unp

variable {src : HSection} {low : Module} {r : Record} {fn : Fn} {fr : FuncRec} {fl : FuncLower}
  {e : HBlock} {me : Block} {be : Nat} {rs : List (Nat × Nat × List (List Nat) × List Nat)}

/-- The pattern lemma of a pure statement, for any frame with the function's value map. -/
theorem FnUnp.pureTempl (U : FnUnp src low r fn fr fl e me be rs) {cM : Ctx}
    (hcM : cM.symbol = fun s => src.symbols.lookup s) {I : Fe.EVM.Env} {b : HBlock}
    (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt} {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hst : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds))
    (hpure : sfxPure s.inst = true) {S' : SecFacts} {l : List Nat} {g : Ghost} {hst' : H.State}
    {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    (hI : Inv S' hst' w g) (hE : EnvRel S'.z (vF fn.F l) g hst' envH envM L)
    (hA : At S' (vF fn.F l) fn.c (secX src r).derived fn.k s (calleeOf s cs).1 L L' ds) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧
      TemplOk src I cM S' (vF fn.F l) g hst' w envH envM s L' pre := by
  have hnd := U.nodup hb hp
  have hsym : fn.c.symbols = src.symbols := by rw [U.hc]; rfl
  have hstr : fn.c.src.structs = src.module.structs := by rw [U.hc]; rfl
  have h0 := hst
  unfold stmt at h0
  split at h0
  next op a b' x tx hi hd => exact inst_bin hI hE hA hi hd hst
  next op a b' x tx hi hd => exact inst_cmp hI hE hA hi hd hst
  next a x tx hi hd => exact inst_isZero hI hE hA hi hd hst
  next a x tx hi hd => exact inst_unary (Or.inl rfl) hI hE hA hi hd hst
  next a x tx hi hd => exact inst_unary (Or.inr (Or.inl rfl)) hI hE hA hi hd hst
  next a x tx hi hd => exact inst_unary (Or.inr (Or.inr (Or.inl rfl))) hI hE hA hi hd hst
  next a x tx hi hd => exact inst_unary (Or.inr (Or.inr (Or.inr rfl))) hI hE hA hi hd hst
  next op a b' x tx y ty hi hd => exact inst_ovf hI hE hA hnd hi hd hst
  next op a b' t x tx hi hd => exact inst_sat hI hE hA hi hd hst
  next op a t x tx hi hd => exact inst_cast hI hE hA hi hd hst
  next a x tx hi hd => exact inst_blackBox hI hE hA hi hd hst
  next sym x tx hi hd => exact inst_symAddr hsym hcM hI hE hA hi hd hst
  next sym x tx hi hd => exact inst_symSize hsym hcM hI hE hA hi hd hst
  next op args dsts hi => rw [hi] at hpure; simp [sfxPure] at hpure
  next a t x tx hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next a v t hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next d l hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next a l x tx hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next a t x tx hi hd => exact inst_truncNuw hI hE hA hi hd hst
  next bt base idxs x tx hi hd => exact inst_gep hstr hI hE hA hnd hi hd hst
  next t x tx hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next a x tx hi hd => rw [hi] at hpure; simp [sfxPure] at hpure
  next gn args dsts hi => rw [hi] at hpure; simp [sfxPure] at hpure
  next => cases h0

/-- A pure statement after a terminal fixed buffer keeps `SR`. -/
theorem FnUnp.sfxPureStep {efp : Option Nat} (U : FnUnp src low r fn fr fl e me be rs)
    (hS : SecChecked src low efp r) {cM : Ctx} (hcM : cM.symbol = fun s => src.symbols.lookup s)
    (I : Fe.EVM.Env) {b : HBlock} (hb : b ∈ fn.f.blocks) {i : Nat} {s : HStmt}
    (hs : b.body[i]? = some s) {mb : Nat} {ms : List Stmt} {cs : List Nat}
    (hp : fn.pos b i = some (mb, ms, cs)) {vm' : VM} {mb' : Nat} {ms' : List Stmt} {ds : List Nat}
    (hstm : stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds))
    (hpure : sfxPure s.inst = true) {kt base n t : Nat} {bt : HBlock} {it : Nat}
    (hF : FixSite fn bt it t) {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env}
    (hR : SR (secS src r efp) fn kt base n t b i (fn.live b i) g hst w envH envM) (O : Oracle) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ ∀ res, (runBodyO O cM envM pre).exec I w = some res →
      (∃ o, (∀ rest, ExecBody src I envH (s :: rest) hst (.halt o)) ∧ Excuses o res) ∨
      ∃ envM' w', res = .ok (envM', w') ∧ ∃ envH',
        SR (secS src r efp) fn kt base n t b (i + 1) (fn.live b (i + 1)) g hst w' envH' envM' ∧
        ∀ rest o, ExecBody src I envH' rest hst o → ExecBody src I envH (s :: rest) hst o := by
  have hnd := U.defsNodup
  have hsm : s ∈ b.body := List.mem_of_getElem? hs
  have hA := (U.at hS hb hs hp hstm).virt (l := fn.live b i ++ s.defs)
    (fun x hx => List.mem_append_right _ hx) hpure
  have hI := hR.inv
  have hE := hR.envRel (l := fn.live b i ++ s.defs) (fun x hx => List.mem_append_left _ hx)
  obtain ⟨pre, h1, h2, hT⟩ := U.pureTempl (I := I) hcM hb hp hstm hpure hI hE hA
  refine ⟨pre, h1, h2, fun res hres => ?_⟩
  have hw : (vSt hst w kt n base).word = hst.word := vSt_word
  rcases hT O res hres with ⟨o, hall, hx⟩ | ⟨envM', w', rfl, envH', hst', g', hI', hE', hgl, hc⟩
  · refine Or.inl ⟨o, fun rest => ?_, hx⟩
    rcases execBody_halt_one (hall []) with ⟨ee, he, rfl⟩ | ⟨he, rfl⟩ | ⟨a, ha⟩ | ⟨gn, args, ha⟩
    · have := step_congr (c := src.ctx) (I := I) (env := envH) (st' := hst) hpure hw
      rw [he] at this
      exact ExecBody.exit this
    · have := step_congr (c := src.ctx) (I := I) (env := envH) (st' := hst) hpure hw
      rw [he] at this
      exact ExecBody.ub this
    · rw [ha] at hpure; simp [sfxPure] at hpure
    · rw [ha] at hpure; simp [sfxPure] at hpure
  · obtain ⟨vals, hbv, hk⟩ := execBody_one (hc [] _ ExecBody.nil)
    have hstep : stepInst src.ctx I envH (vSt hst w kt n base) s.inst = .ok vals hst' := by
      rcases hk with hk | ⟨_, ha⟩ | ⟨_, ha⟩ | ⟨_, _, ha⟩
      · exact hk
      all_goals (rw [ha] at hpure; simp [sfxPure] at hpure)
    obtain rfl := step_keep hpure hstep
    have hstep' : stepInst src.ctx I envH hst s.inst = .ok vals hst := by
      have := step_congr (c := src.ctx) (I := I) (env := envH) (st' := hst) hpure hw
      rw [hstep] at this; exact this
    have hexec : ∀ rest o, ExecBody src I envH' rest hst o → ExecBody src I envH (s :: rest) hst o :=
      fun rest o hr => ExecBody.step hstep' hbv hr
    have hsz : (vSt hst w kt n base).blocks.size = hst.blocks.size := vSt_size
    have hjj : ∀ bb, bb < hst.blocks.size → g'.j bb = g.j bb := fun bb hbb =>
      hgl.j bb (by rw [hsz]; exact hbb)
    have hlkt : g'.live kt := hgl.live kt ⟨hR.hkt, by rw [hR.jt]; have := hR.bn; omega⟩ (fun _ h => by cases h)
    refine Or.inr ⟨envM', w', rfl, envH', ?_, hexec⟩
    refine ⟨?world, hR.bsz, hR.exact, hR.zero, ?vals, hR.hkt, hR.ksz, hR.jt, hR.bn, ?buf,
      U.fixStep I b hb i s hs envH hst envH' hst hR.q (hexec [] _ ExecBody.nil), ?must⟩
    case world =>
      have h1 : { w' with memory := w.memory } = w := hI'.world
      rw [← hR.world, ← h1]
    case vals =>
      intro x hx
      obtain ⟨v, m, e1, e2, e3, e4, e5, e6⟩ := hE' x hx
      refine ⟨v, m, e1, e2, e3, ?_, ?_, ?_⟩
      · cases v with
        | int => exact e4
        | ptr bb o => exact ⟨by rw [← hjj bb (by rw [← hsz]; exact e5.1)]; exact e4.1, e4.2⟩
      · cases v with
        | int => trivial
        | ptr bb o => exact ⟨by rw [← hsz]; exact e5.1, e5.2⟩
      · intro bb o hv
        subst hv
        have hl : g'.live bb := by
          rcases e6 with hh | ⟨hl, -⟩
          · exact hI'.heap_live bb hh
          · exact hl
        have := hI'.bound bb hl
        rw [hjj bb (by rw [← hsz]; exact e5.1)] at this
        omega
    case buf =>
      intro k hk
      have hb' := hI'.bytes kt hlkt k (by rw [vSt_bsize, if_pos ⟨rfl, hR.hkt⟩]; exact hk)
      rw [vSt_cell hR.hkt hk, hjj kt hR.hkt, hR.jt] at hb'
      rw [hb']
      exact hR.buf k hk
    case must =>
      intro y hy v hv
      rcases bindVals_find hbv hv with ⟨d, hd, rfl, -, hvm⟩ | ⟨hold, -⟩
      · have hyd : d.1 ∈ s.defs := List.mem_map.mpr ⟨d, hd, rfl⟩
        rcases (U.s6 hF).just d.1 hy with ht | ⟨b', hb', s', hs', hy', hm⟩
        · obtain ⟨st, hst0, htd⟩ := U.siteDef hF
          obtain ⟨-, rfl⟩ := stmt_unique hnd hb hF.1 hsm (List.mem_of_getElem? hst0) hyd (ht ▸ htd)
          obtain ⟨-, st', a, tx, hst1, hi, -, -⟩ := hF
          rw [hst0] at hst1; cases hst1
          rw [hi] at hpure; simp [sfxPure] at hpure
        · obtain ⟨-, rfl⟩ := stmt_unique hnd hb' hb hs' hsm hy' hyd
          exact mustStep_ptr hm hR.must (fun y hy v hv => hR.q.1 y hy v hv) hstep' v hvm
      · exact hR.must y hy v hold

end unp

end Fe.Sonatina.Stage3.Place
