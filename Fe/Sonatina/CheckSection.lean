import Fe.Sonatina.CheckBody
import Ethereum.Theory.ProgressLemmas
import Ethereum.Theory.GasLemmas

/-!
# Towards the section

The pieces the section theorem joins: `XstepN_X_error` and `XstepN_fuel` take a run of steps
to the iterator `X` within its fuel, and `checkSection_ok` and `checkBlock_ok` take out of an
accepted section the facts the checker established of its function and of each block.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- Steps that end in an error end the iterator with it. -/
theorem XstepN_X_error {D : Array UInt256} {s : State} {e : ExecutionException} {n : Nat}
    (h : XstepN D s (.error e) n) (f : Nat) : X (f + n) D s = .error e := by
  generalize hx : (Except.error e : Except ExecutionException _) = x at h
  induction h generalizing f with
  | step s x' hs =>
    subst hx
    exact Xstep_X_X_except f s D e hs
  | trans s s' x' n hs _ ih =>
    rw [show f + (n + 1) = (f + n) + 1 by omega]
    exact Xstep_X_X_continue (f + n) s s' D _ hs (ih f hx)

/-- Steps from a state cost at most its gas, but the last. -/
theorem XstepN_fuel {D : Array UInt256} {s : State} {x : Except ExecutionException
    (State × Option (HaltCause × ByteArray))} {n f : Nat} (h : XstepN D s x n)
    (hg : s.machineState.gasAvailable.toNat < f) : n ≤ f := by
  induction h generalizing f with
  | step => omega
  | trans s s' x' n hs _ ih =>
    have := Xstep_gas_decreases_of_continues hs
    have := ih (f := f - 1) (by omega)
    omega

/-- The entry block's events lead with the free pointer's store. -/
def prologue (low : Lowering) (isEntry : Bool) (events : List Event) : List Event :=
  match low.entryFreePtr, isEntry with
  | some ptr, true => ⟨.MSTORE, [.const 0x40, .const ptr], none⟩ :: events
  | _, _ => events

theorem checkBlock_ok {code : CodeSection} {low : Lowering} {hint : FuncHint} {f : Func}
    {entryBlock : Block} {place : Nat → Option Nat} {rank : Nat → Nat} {b : Block}
    (h : checkBlock code low hint f entryBlock place rank b = .ok ()) :
    ∃ hb pc stack events exit,
      hint.blocks.find? (·.block == b.id) = some hb ∧ place b.id = some pc ∧
      (Ctx.ofBlock f b code.symbols).entryStack hb = some stack ∧
      (Ctx.ofBlock f b code.symbols).events b = some events ∧
      (Ctx.ofBlock f b code.symbols).exitOf b.term = some exit ∧
      ((b.id == entryBlock.id) = true → stack = []) ∧
      defined f b (hb.entryStack.filterMap fun | .value id => some id | _ => none) = true ∧
      (b.term.only.all fun s => place s != some pc || rank s < rank b.id) = true ∧
      run code.bytecode (Ctx.ofBlock f b code.symbols) hint.blocks place b.id
        (2 * low.codeSize + 2)
        ⟨pc, stack, prologue low (b.id == entryBlock.id) events, exit⟩ = true := by
  unfold checkBlock at h
  cases hhb : hint.blocks.find? (·.block == b.id) with
  | none => simp [hhb] at h
  | some hb =>
  simp only [hhb] at h
  cases hpc : place b.id with
  | none => simp [hpc] at h
  | some pc =>
  simp only [hpc] at h
  cases hst : (Ctx.ofBlock f b code.symbols).entryStack hb with
  | none => simp [hst] at h
  | some stack =>
  simp only [hst] at h
  cases hev : (Ctx.ofBlock f b code.symbols).events b with
  | none => simp [hev] at h
  | some events =>
  simp only [hev] at h
  cases hex : (Ctx.ofBlock f b code.symbols).exitOf b.term with
  | none => simp [hex] at h
  | some exit =>
  simp only [hex] at h
  have hthrow : ∀ {m : String} {k : PUnit → Except String Unit},
      ((throw m : Except String PUnit) >>= k) ≠ .ok () := fun h => nomatch h
  refine ⟨hb, pc, stack, events, exit, rfl, rfl, hst, rfl, rfl, ?_⟩
  by_cases h1 : (b.id == entryBlock.id) = true
  · by_cases h2 : stack.isEmpty = true
    · simp only [h1, h2, if_true, pure_bind] at h
      refine ⟨fun _ => List.isEmpty_iff.mp h2, ?_⟩
      split_ifs at h with h3 h4 h5
      · exact ⟨h3, h4, by simpa [prologue, h1] using h5⟩
      all_goals cases h
    · simp only [h1, h2, if_true] at h
      exact absurd h hthrow
  · simp only [h1, Bool.false_eq_true, if_false, pure_bind] at h
    refine ⟨fun h' => absurd h' h1, ?_⟩
    split_ifs at h with h3 h4 h5
    · exact ⟨h3, h4, by simpa [prologue, h1] using h5⟩
    all_goals cases h

theorem forM_ok {α ε : Type} {g : α → Except ε Unit} :
    ∀ {l : List α}, l.forM g = .ok () → ∀ a ∈ l, g a = .ok ()
  | [], _, a, ha => by cases ha
  | x :: l, h, a, ha => by
    simp only [List.forM] at h
    cases hx : g x with
    | error e => rw [hx] at h; cases h
    | ok u =>
      rw [hx] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact forM_ok h a ha

/-- What a section the checker accepts is. -/
theorem checkSection_ok {code : CodeSection} {entry : String}
    (h : checkSection code entry = .ok ()) :
    ∃ low hint f entryBlock, code.lowering = some low ∧ code.bytecode.size < UInt256.size ∧
      low.funcs = [hint] ∧ hint.name = entry ∧ inClass hint = true ∧
      low.machine.func? entry = some f ∧ f.blocks.head? = some entryBlock ∧
      (f.blocks.all fun b => b.phis.all (·.ty.bits == 256) &&
        b.body.all (·.dsts.all (·.2.bits == 256))) = true ∧
      nodup (f.blocks.flatMap fun b =>
        b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) = true ∧
      f.params = [] ∧ entryBlock.phis = [] ∧
      (f.blocks.all fun x => !x.term.succs.contains entryBlock.id) = true ∧
      Hints.place low 16 (.block hint.name entryBlock.id) = some 0 ∧
      ∀ b ∈ f.blocks, checkBlock code low hint f entryBlock
        (fun b => Hints.place low 16 (.block hint.name b))
        (zeroRank f (fun b => Hints.place low 16 (.block hint.name b)) f.blocks.length) b =
          .ok () := by
  unfold checkSection at h
  cases hlow : code.lowering with
  | none => simp [hlow] at h
  | some low =>
  simp only [hlow] at h
  by_cases h1 : code.bytecode.size < UInt256.size
  swap
  · simp [h1] at h; cases h
  simp only [h1, if_true, pure_bind] at h
  cases hf : low.funcs with
  | nil => simp [hf] at h
  | cons hint t =>
  cases t with
  | cons _ _ => simp [hf] at h
  | nil =>
  simp only [hf] at h
  by_cases h2 : hint.name = entry ∧ inClass hint = true
  swap
  · simp [h2] at h; cases h
  simp only [h2, Bool.and_eq_true, beq_iff_eq, and_self, if_true] at h
  cases hfn : low.machine.func? entry with
  | none => simp [hfn] at h
  | some f =>
  simp only [hfn] at h
  cases he : f.blocks.head? with
  | none => simp [he] at h
  | some eb =>
  simp only [he] at h
  split_ifs at h with c1 c2 c3 c4
  all_goals try cases h
  obtain ⟨hn, hp⟩ := h2
  subst hn
  simp only [List.isEmpty_iff] at c3
  exact ⟨low, hint, f, eb, rfl, h1, hf, rfl, hp, hfn, he, c1, c2, c3.1.1, c3.1.2, c3.2, c4,
    forM_ok h⟩

end Fe.Sonatina.Check
