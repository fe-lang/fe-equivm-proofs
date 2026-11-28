import Fe.Sonatina.Stage3.Place.Dispatch

/-!
# S14 for one section (`place_lower_sound`, PLAN §0)

Every run of the lowered machine module that ends, from the entry free-pointer store and the
section entry (`runLowered`, the machine level of `Sidecar.runSectionWith`), is matched by a run
of H of the section: the call contract (`callP_runFunc`) at the entry's place, from the
invariant after the free-pointer store (no live block, the free pointer at the heap floor).  A
run of the entry that returns is stuck, so only halts reach the result.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Ethereum

/-- The machine run of a lowered section: the entry free pointer stored at `0x40`, then the
    entry function, which ends the call itself (`Sidecar.runSectionWith` at the machine level). -/
def runLowered (low : Module) (efp : Option Nat) (symbols : List (String × Nat × Nat))
    (entry : String) : FeM ByteArray := do
  if let some ptr := efp then
    mstore (UInt256.ofNat 0x40) (UInt256.ofNat ptr)
  let _ ← runFuncG .none low ⟨(symbols.lookup ·), low.fixedEnd, low.structs⟩ [] entry []
  stuck

theorem firstOf_of_findIdx {l : List HFunc} {n : String} {k : Nat} {f : HFunc}
    (hk : l.findIdx? (·.name == n) = some k) (hf : l[k]? = some f) :
    f.name = n ∧ firstOf (·.name) l k f.name = true := by
  obtain ⟨hlt, hp, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
  have hfk : l[k] = f := by rw [List.getElem?_eq_getElem hlt] at hf; exact Option.some.inj hf
  rw [hfk] at hp
  have hn : f.name = n := by simpa using hp
  refine ⟨hn, ?_⟩
  unfold firstOf
  rw [hf]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, bne_iff_ne, ne_eq]
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  rw [List.length_take] at hj
  have hjk : j < k := lt_of_lt_of_le hj (min_le_left _ _)
  have := hbefore j hjk
  rw [List.getElem_take]
  simpa [hn] using this

theorem exec_mstore64 (I : Fe.EVM.Env) (w : World) (ep : Nat) :
    (mstore (UInt256.ofNat 0x40) (UInt256.ofNat ep)).exec I w = some (.ok ((),
      { w with memory := (UInt256.ofNat ep).toByteArray.write 0 w.memory 64 32 })) := by
  simp [Fe.EVM.mstore, toNat_ofNat_lt (show 64 < W by unfold W; norm_num)]

/-- The invariant at the section's start, after the entry free-pointer store. -/
theorem inv_init {src : HSection} {low : Module} {efp : Option Nat} {r : Record}
    (hS : SecChecked src low efp r) (w : World) (m : ByteArray)
    (hm : ∀ e, efp = some e → fpWord m = e) :
    Inv (secS src r efp) (State.init w) { w with memory := m } ⟨fun _ => 0, fun _ => False, fun _ => False⟩ where
  world := by cases w; rfl
  live_lt _ h := h.elim
  heap_live _ h := h.elim
  heap_has _ h := h.elim
  bytes_size _ _ h := by simp [State.init] at h
  exact _ h := by simp [State.init] at h
  zero _ h := by simp [State.init] at h
  bound _ h := h.elim
  disj _ _ h := h.elim
  bytes _ h := h.elim
  frags _ h := h.elim
  e96 hh := by
    obtain ⟨e, he, h60, -⟩ := hS.s1' hh
    show 0x60 ≤ efp.getD 0
    rw [he]; exact h60
  heap_floor _ h := h.elim
  fp hh := by
    obtain ⟨e, he, -, -⟩ := hS.s1' hh
    have hfp := hm e he
    refine ⟨?_, ?_, fun _ h => h.elim⟩
    · show efp.getD 0 ≤ _; rw [he, hfp]; rfl
    · show fpWord m ≤ secF0 (secP src r) efp + 0
      rw [hfp, Nat.add_zero]
      have := secS_e_le (src := src) (r := r) (efp := efp)
      simpa [secS, he] using this
  frame _ _ h := h.elim

/-- S14 for one section, given what its terminal fixed buffers need. -/
theorem place_lower_sound_of {src : HSection} {low : Module} {efp : Option Nat} {rec : Record}
    {symbols : List (String × Nat × Nat)} {entry : String}
    (hc : check src low efp rec = true) (hsym : symbols = src.symbols) (hentry : entry = src.entry)
    (hX : ∀ I cM k fn, mkFn src low rec k = some fn → FixObls src low rec efp I cM fn) :
    ∀ I σ A feed r, I.calldata.size < 2 ^ 256 →
      (runLowered low efp symbols entry).exec I (World.init σ A feed) = some r →
      ∃ out, ExecFunc src I src.entry [] (State.init (World.init σ A feed)) (.halt out) ∧
        Matches out r := by
  intro I σ A feed r hcd h
  have hS := check_facts hc
  set cM : Ctx := ⟨(symbols.lookup ·), low.fixedEnd, low.structs⟩ with hcMdef
  have hcM : cM.symbol = fun s => src.symbols.lookup s := by rw [hcMdef, hsym]
  obtain ⟨kE, e₀, hkE, he₀, hpar⟩ := hS.entry
  obtain ⟨hname, hfirst⟩ := firstOf_of_findIdx hkE he₀
  obtain ⟨fnE, hmk, hfE⟩ := mkFn_some hc he₀ hfirst
  have hall : ∀ kg fg, mkFn src low rec kg = some fg →
      FnOk src I cM (secS src rec efp) (secX src rec).derived
        (CallP src I (secS src rec efp) (secX src rec).derived (mkFn src low rec)) FixInv low fg :=
    fun kg fg hk => fnOk_of hc hk hcd hcM (hX I cM kg fg hk)
  have hCP := callP_runFunc hall
  -- The free-pointer store.
  set w := World.init σ A feed with hw
  set w₁ : World := { w with memory := match efp with
    | some ep => (UInt256.ofNat ep).toByteArray.write 0 w.memory 64 32
    | none => w.memory } with hw₁def
  have hw₁ : (runLowered low efp symbols entry).exec I w =
      (runFuncG .none low cM [] entry [] >>= fun _ => (stuck : FeM ByteArray)).exec I w₁ := by
    cases efp with
    | none => simp only [runLowered, hw₁def, pure_bind]; rfl
    | some ep => simp only [runLowered]; rw [exec_bind_ok (exec_mstore64 I w ep)]
  have hinv : Inv (secS src rec efp) (State.init w) w₁ ⟨fun _ => 0, fun _ => False, fun _ => False⟩ := by
    refine inv_init hS w _ (fun e he => ?_)
    have hep : e < 2 ^ 32 := hS.s45'.2.1 e he
    subst he
    rw [fpWord_mstore, Nat.mod_eq_of_lt (lt_of_lt_of_le hep (by unfold W; norm_num))]
  rw [hw₁, runFuncG_none] at h
  rcases exec_bind_some h with ⟨ex, h1, rfl⟩ | ⟨v, w₂, h1, h2⟩
  · have hArg : ArgRel (secS src rec efp) fnE ⟨fun _ => 0, fun _ => False, fun _ => False⟩
        (State.init w) [] [] := by
      refine ⟨by rw [hfE, hpar]; rfl, by rw [hfE, hpar]; rfl, fun j p v a hp _ _ => ?_⟩
      rw [hfE, hpar] at hp; cases hp
    have hen : fnE.f.name = entry := by rw [hfE, hname, hentry]
    obtain ⟨fo, hex, hfr⟩ := hCP kE fnE hmk [] [] _ (State.init w) w₁ hinv hArg _
      (by rw [hen]; exact h1)
    rw [hen, hentry] at hex
    rcases hfr with ⟨o, rfl, hx⟩ | ⟨_, _, _, _, _, heq, _⟩
    · refine ⟨o, hex, ?_⟩
      rcases hx with hx | hx | ⟨e', he', hm⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · cases he'; exact hm
    · cases heq
  · simp [stuck] at h2

/-- `place_lower_sound`'s statement, for every section. -/
def PlaceLowerSound : Prop :=
  ∀ {src : HSection} {low : Module} {efp : Option Nat} {rec : Record}
    {symbols : List (String × Nat × Nat)} {entry : String},
    check src low efp rec = true → symbols = src.symbols → entry = src.entry →
    ∀ I σ A feed r, I.calldata.size < 2 ^ 256 →
      (runLowered low efp symbols entry).exec I (World.init σ A feed) = some r →
      ∃ out, ExecFunc src I src.entry [] (State.init (World.init σ A feed)) (.halt out) ∧
        Matches out r

end Fe.Sonatina.Stage3.Place
