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
      defined f hint.blocks b (hb.entryStack.filterMap fun | .value id => some id | _ => none) =
        true ∧
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

theorem insert_get {env : Env} {k id : Nat} {v : Val} :
    (env.insert k v)[id]? = if k = id then some v else env[id]? := by
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : k = id
  · subst h; simp
  · have : ¬compare k id = .eq := by rw [compare_eq_iff_eq]; exact h
    simp [this, h]

/-- A fold of inserts at distinct keys finds each key's last value, others as they were. -/
theorem foldl_insert_get :
    ∀ (l : List ((Nat × Ty) × Val)) (env : Env), (l.map (·.1.1)).Nodup → ∀ id,
      (l.foldl (fun env ((id, ty), v) => env.insert id (v.as ty)) env)[id]? =
        match l.find? (·.1.1 == id) with
        | some ((_, ty), v) => some (v.as ty)
        | none => env[id]?
  | [], env, _, id => by simp
  | ((k, ty), v) :: l, env, hnd, id => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons, foldl_insert_get l _ hnd.2 id]
    by_cases h : k = id
    · subst h
      have : l.find? (·.1.1 == k) = none := by
        rw [List.find?_eq_none]; intro x hx hk
        exact hnd.1 (by simp only [beq_iff_eq] at hk; exact hk ▸ List.mem_map_of_mem hx)
      simp [this]
    · simp [insert_get, h]

theorem mapM_pure {α β : Type} {F : α → FeM β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, F a = pure (g a)) → l.mapM F = pure (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_pure fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp

theorem evalOperand_some {env : Env} {ρ : Nat → UInt256} {D : List Nat} {o : Operand}
    (hw : WordsOf env ρ D) (hr : reads D [o] = true) : ∃ val, evalOperand env o = pure val := by
  cases o with
  | var id =>
    have hid : id ∈ D := by simpa [reads, Operand.var?] using hr
    exact ⟨_, by simp [evalOperand, hw id hid]; rfl⟩
  | imm bits x => exact ⟨_, rfl⟩
  | undef ty => exact ⟨_, rfl⟩

/-- Entering a block from `p`, each phi of which has a defined operand from `p`: each phi takes
    its operand's value, other values stay. -/
theorem enter_run {env : Env} {ρ : Nat → UInt256} {D : List Nat} {p : Nat} {S : Block}
    (hS : ∀ phi ∈ S.phis, ∃ o d, phi.incoming.find? (·.2 == p) = some (o, d) ∧
      reads D [o] = true)
    (hw : WordsOf env ρ D) (hnd : (S.phis.map (·.dst)).Nodup) :
    ∃ envS, enter env (some p) S = pure envS ∧
      (∀ phi ∈ S.phis, ∃ o d val, phi.incoming.find? (·.2 == p) = some (o, d) ∧
        evalOperand env o = pure val ∧ envS[phi.dst]? = some (val.as phi.ty)) ∧
      ∀ id, id ∉ S.phis.map (·.dst) → envS[id]? = env[id]? := by
  choose o d hf hr using hS
  choose val hval using fun phi hp => evalOperand_some hw (hr phi hp)
  classical
  let g : Phi → Val := fun phi => if hp : phi ∈ S.phis then val phi hp else default
  have hzip : ∀ l : List Phi, (l.map fun phi => (phi.dst, phi.ty)).zip (l.map g) =
      l.map fun phi => ((phi.dst, phi.ty), g phi) := fun l => by
    induction l <;> simp_all
  refine ⟨(S.phis.map fun phi => ((phi.dst, phi.ty), g phi)).foldl
    (fun env ((id, ty), v) => env.insert id (v.as ty)) env, ?_, ?_, ?_⟩
  · unfold enter
    rw [mapM_pure (g := g) fun phi hp => by simp only [hf phi hp, g, dif_pos hp, hval phi hp]]
    simp only [pure_bind, Fe.Sonatina.bind, List.length_map, beq_self_eq_true, if_true, hzip]
  · intro phi hp
    refine ⟨o phi hp, d phi hp, val phi hp, hf phi hp, hval phi hp, ?_⟩
    rw [foldl_insert_get _ _ (by simpa [Function.comp_def] using hnd)]
    have : (S.phis.map fun phi => ((phi.dst, phi.ty), g phi)).find? (·.1.1 == phi.dst) =
        some ((phi.dst, phi.ty), g phi) := by
      rw [List.find?_map]
      have hfind : S.phis.find? (fun q => q.dst == phi.dst) = some phi := by
        rw [List.find?_eq_some_iff_getElem]
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        refine ⟨by simp, i, hi, rfl, fun j hj => ?_⟩
        have := (List.nodup_iff_injective_get.mp hnd)
        rw [Bool.not_eq_true', beq_eq_false_iff_ne]
        intro hjq
        have := @this ⟨j, by simpa using (by omega : j < S.phis.length)⟩ ⟨i, by simpa using hi⟩
          (by simpa using hjq)
        simp at this; omega
      simp [hfind, Function.comp_def]
    simp [this, g, dif_pos hp]
  · intro id hid
    rw [foldl_insert_get _ _ (by simpa [Function.comp_def] using hnd)]
    have : (S.phis.map fun phi => ((phi.dst, phi.ty), g phi)).find? (·.1.1 == id) = none := by
      rw [List.find?_eq_none]
      intro x hx hxe
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      simp only [beq_iff_eq] at hxe
      exact hid (hxe ▸ List.mem_map_of_mem hq)
    simp [this]

/-- A block's statements define nothing defined before them. -/
theorem definedAfter_fresh : ∀ {stmts : List Stmt} {D D' : List Nat},
    definedAfter D stmts = some D' → ∀ s ∈ stmts, ∀ d ∈ s.dsts, d.1 ∉ D
  | [], _, _, _, s, hs, _, _ => by cases hs
  | t :: rest, D, D', h, s, hs, d, hd => by
    simp only [definedAfter] at h
    split_ifs at h with hok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
    rcases List.mem_cons.mp hs with rfl | hs
    · intro hm; simpa [List.contains_iff_mem, hm] using hok.2 d hd
    · exact fun hm => definedAfter_fresh h s hs d hd (List.mem_append_left _ hm)

/-- A value no statement defines is not expanded. -/
theorem lookup_none {stmts : List Stmt} {id : Nat}
    (h : ∀ s ∈ stmts, ∀ d ∈ s.dsts, d.1 ≠ id) : (stmts.filterMap Stmt.def?).lookup id = none := by
  induction stmts with
  | nil => rfl
  | cons t rest ih =>
    have ih' := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    cases ht : t.def? with
    | none => simpa [List.filterMap_cons, ht] using ih'
    | some p =>
      have hp : p.1 ≠ id := by
        unfold Stmt.def? at ht
        split at ht
        · next id' ty' hd => cases ht; exact h t (by simp) (id', ty') (by simp [hd])
        · cases ht
      have hb : (id == p.1) = false := by simpa using Ne.symm hp
      rw [List.filterMap_cons, ht]
      simp only [List.lookup, hb]
      exact ih'

theorem expand_atom {c : Ctx} {id : Nat} (h : c.defs.lookup id = none) (d : Nat) :
    c.expand (d + 1) id = some (.atom id) := by
  simp [Ctx.expand, h]

theorem mapM_forall {α β : Type} {f : α → Option β} {P : β → Prop} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (hf : ∀ x y, f x = some y → P y) : ∀ y ∈ l', P y := by
  have h2 := mapM_some_iff.mp h
  clear h
  intro y hy
  induction h2 with
  | nil => cases hy
  | cons hxy _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hf _ _ hxy
    · exact ih hy

/-- An exit the checker reads of a terminator is valid from the start. -/
theorem exitOf_valid {c : Ctx} {t : Term} {e : Exit} (h : c.exitOf t = some e)
    (ee : ExecutionEnv) (ρ : Nat → UInt256) : e.Valid ee ρ := by
  cases e with
  | table sc d cs ruled =>
    cases t with
    | brTable s' def? cases =>
      cases def? with
      | none => simp [Ctx.exitOf] at h
      | some d' =>
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cs', hcs, ex, -, h⟩ := h
      cases h
      refine ⟨mapM_forall hcs fun x y hxy => ?_, fun _ _ _ hk => by cases hk⟩
      obtain ⟨o, dest⟩ := x
      simp only at hxy
      split at hxy
      · split_ifs at hxy with hv; cases hxy; exact hv
      · cases hxy
    | _ => simp [Ctx.exitOf, Option.bind_eq_some_iff] at h
  | _ => trivial

/-- The EVM result agrees, at profile `P1`, with how the IR's run ends: out of gas or stack, or
    the same exit, the logs and the revert data compared. -/
def XAgrees (x : Except ExecutionException (ExecutionResult State))
    (r : Option (Except (Fe.Exit World) (List Val × World))) : Prop :=
  x = .error .OutOfGass ∨ x = .error .StackOverflow ∨
  match r with
  | some (.error (.stop out w)) => ∃ s', x = .ok (.success s' out) ∧
      s'.accountMap = w.accounts ∧ s'.substate.logSeries = w.logs
  | some (.error (.revert data)) => ∃ g, x = .ok (.revert g data)
  | some (.error .static) => x = .error .StaticModeViolation
  | some (.error .trap) => x = .error .InvalidInstruction
  | _ => False

/-- The bytes end from `st` as the IR's run `r` ends, in steps. -/
def Final (D : Array UInt256) (st : State)
    (r : Option (Except (Fe.Exit World) (List Val × World))) : Prop :=
  (∃ n e, XstepN D st (.error e) n ∧ (e = .OutOfGass ∨ e = .StackOverflow ∨
    (e = .StaticModeViolation ∧ r = some (.error .static)) ∨
    (e = .InvalidInstruction ∧ r = some (.error .trap)))) ∨
  (∃ n s' out w', XstepN D st (.ok (s', some (.success, out))) n ∧
    r = some (.error (.stop out w')) ∧ s'.accountMap = w'.accounts ∧
    s'.substate.logSeries = w'.logs) ∨
  (∃ n s' data, XstepN D st (.ok (s', some (.revert, data))) n ∧
    r = some (.error (.revert data)))

theorem Final.agrees {D : Array UInt256} {st : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} (h : Final D st r) {fuel : Nat}
    (hg : st.machineState.gasAvailable.toNat < fuel) : XAgrees (X fuel D st) r := by
  rcases h with ⟨n, e, hx, he⟩ | ⟨n, s', out, w', hx, hr, ha, hl⟩ | ⟨n, s', data, hx, hr⟩
  · have hn := XstepN_fuel hx hg
    have hX := XstepN_X_error hx (fuel - n)
    rw [Nat.sub_add_cancel hn] at hX
    rw [hX]
    rcases he with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
    · exact .inr (.inr rfl)
  · have hn := XstepN_fuel hx hg
    have hX := XstepN_X_halt_success (f := fuel - n) D hx
    rw [Nat.sub_add_cancel hn] at hX
    subst hr
    exact .inr (.inr ⟨s', hX, ha, hl⟩)
  · have hn := XstepN_fuel hx hg
    have hX := XstepN_X_halt_revert (f := fuel - n) D hx
    rw [Nat.sub_add_cancel hn] at hX
    subst hr
    exact .inr (.inr ⟨_, hX⟩)

end Fe.Sonatina.Check
