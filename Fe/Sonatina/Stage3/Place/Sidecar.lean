import Fe.Sonatina.Stage3.Place.Sound
import Fe.Sonatina.H.Compose
import Fe.Sonatina.Steps.Machine

/-!
# Slice 1 for a sidecar (PLAN §0)

`Sidecar.placeCheck s h rr ri` checks both sections of the handover object `h` against the
sidecar as lowering made it (`s.asLowered`): S14 (`check`) of each section's source against its
lowered machine module, under its entry free pointer and the placement record (`rr` for the
runtime, `ri` for the init section), and that H's section has the sidecar's symbols and entry,
so that H's `sym_addr`/`sym_size` and the machine's agree and both run the same function, and
that its module declares the fixed memory limit 0 (`evm_fixed_memory_limit = 0x0`): H has no
fixed region, every access of nonzero length through an integer address is `ub`, which is
Sonatina's E2 for that limit and for no other, so a module that declares another limit or none
is rejected.
`place_sidecar_sound`: the lowered model then implements `h` under H; `slice1_sound` composes
it with links 4 and 5 (`machine_sound_sidecar_fut`): the bytes refine `h`.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Ethereum

/-- Section `name` of sidecar `t` against H's section `hs`, under the placement record `rec`:
    S14, the symbols and the entry, and that `hs`'s module declares an empty fixed memory region
    (`HModule.fixedLimit`), the one H is the semantics of. -/
def placeSec (t : Sidecar) (hs : HSection) (name : String) (rec : Record) : Bool :=
  match t.objects.find? (·.name == t.object) with
  | none => false
  | some obj => match obj.sections.find? (·.name == name) with
    | none => false
    | some sec => match t.section? name with
      | none => false
      | some code => match code.lowering with
        | none => false
        | some l => check hs l.machine l.entryFreePtr rec && hs.symbols == code.symbols &&
            hs.entry == sec.entry && hs.module.fixedLimit == some 0

/-- Slice 1's check of a sidecar against the handover object `h`, with the placement records
    of its runtime and init sections. -/
def _root_.Fe.Sonatina.Sidecar.placeCheck (s : Sidecar) (h : H.Object) (rr ri : Record) : Bool :=
  placeSec s.asLowered h.runtime "runtime" rr && placeSec s.asLowered h.init "init" ri

/-- A section `placeSec` accepts runs as `runLowered` of a module S14 accepts. -/
theorem placeSec_run {t : Sidecar} {hs : HSection} {name : String} {rec : Record}
    (hp : placeSec t hs name rec = true) :
    ∃ low efp symbols entry, check hs low efp rec = true ∧ symbols = hs.symbols ∧
      entry = hs.entry ∧ t.runSection name .machine = runLowered low efp symbols entry := by
  unfold placeSec at hp
  split at hp
  · cases hp
  · next obj hobj =>
    split at hp
    · cases hp
    · next sec hsec =>
      split at hp
      · cases hp
      · next code hcode =>
        split at hp
        · cases hp
        · next l hl =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          obtain ⟨⟨⟨hc, hsym⟩, hen⟩, -⟩ := hp
          refine ⟨l.machine, l.entryFreePtr, code.symbols, sec.entry, hc, hsym.symm, hen.symm, ?_⟩
          simp only [Sidecar.runSection, Sidecar.runSectionWith, hobj, hsec, hcode,
            Sidecar.moduleAt, hl, Option.map_some, Option.bind_some]
          rfl

/-- The lowered model of a sidecar `placeCheck` accepts implements the handover object under H,
    given S14 for one section. -/
theorem place_sidecar_sound_of (hL : PlaceLowerSound) {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hp : s.placeCheck h rr ri = true) :
    ImplementsH h (s.asLowered.model .machine) CalldataFits ∧
      ImplementsDeployH h (s.asLowered.model .machine) (s.code "init") .empty (fun _ => True)
        CalldataFits := by
  simp only [Sidecar.placeCheck, Bool.and_eq_true] at hp
  obtain ⟨lr, er, sr, nr, hcr, hsr, hnr, hrun⟩ := placeSec_run hp.1
  obtain ⟨li, ei, si, ni, hci, hsi, hni, hini⟩ := placeSec_run hp.2
  have hfits : ∀ I : ExecutionEnv, CalldataFits I → I.calldata.size < 2 ^ 256 := fun I hI =>
    lt_of_lt_of_le hI (by norm_num)
  refine ⟨fun I σ A feed r _ hI hr => ?_, fun I σ A feed args r _ _ _ _ hI hr => ?_⟩
  · have hr' : (runLowered lr er sr nr).exec I (World.init σ A feed) = some r := by
      rw [← hrun]; exact hr
    exact hL hcr hsr hnr I σ A feed r (hfits I hI) hr'
  · have hm : (s.asLowered.model .machine).init args = runLowered li ei si ni := hini
    rw [hm] at hr
    rcases exec_bind_some hr with ⟨ex, h1, rfl⟩ | ⟨v, w', h1, -⟩
    · exact hL hci hsi hni I σ A feed _ (hfits I hI) h1
    · rw [← hm] at h1
      exact absurd h1 (Fe.Sonatina.Check.runSectionWith_not_ok s.asLowered "init" .machine
        (fun m => (m, .none)) I _ v w')

/-- Slice 1, given S14 for one section: the bytes refine the handover object. -/
theorem slice1_sound_of (hL : PlaceLowerSound) {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hv : s.validate = true) (hc : Fe.Sonatina.Check.check s = true)
    (hp : s.placeCheck h rr ri = true) :
    RefinesOnH .P1 (s.code "runtime") h CalldataFits ∧
      RefinesDeployH .P1 (s.code "init") h (fun _ => True) CalldataFits := by
  obtain ⟨hR, hD⟩ := machine_sound_sidecar_fut hv hc
  obtain ⟨hIR, hID⟩ := place_sidecar_sound_of hL hp
  exact ⟨RefinesOnFut.toH hR hIR rfl, RefinesDeployFut.toH hD hID⟩

/-- The lowered model of a sidecar `placeCheck` accepts implements the handover object under H
    (PLAN §0). -/
theorem place_sidecar_sound {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hp : s.placeCheck h rr ri = true) :
    ImplementsH h (s.asLowered.model .machine) CalldataFits ∧
      ImplementsDeployH h (s.asLowered.model .machine) (s.code "init") .empty (fun _ => True)
        CalldataFits :=
  place_sidecar_sound_of (fun hc hsym hentry => place_lower_sound hc hsym hentry) hp

/-- Slice 1 (PLAN §0): when the machine records validate, the byte checker accepts the sidecar
    and S14 accepts both sections against the handover object, the bytes refine the handover
    object on every call and deployment. -/
theorem slice1_sound {s : Sidecar} {h : H.Object} {rr ri : Record} (hv : s.validate = true)
    (hc : Fe.Sonatina.Check.check s = true) (hp : s.placeCheck h rr ri = true) :
    RefinesOnH .P1 (s.code "runtime") h CalldataFits ∧
      RefinesDeployH .P1 (s.code "init") h (fun _ => True) CalldataFits :=
  slice1_sound_of (fun hc hsym hentry => place_lower_sound hc hsym hentry) hv hc hp

end Fe.Sonatina.Stage3.Place
