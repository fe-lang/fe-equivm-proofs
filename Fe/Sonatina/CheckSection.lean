import Fe.Sonatina.CheckBody
import Ethereum.Theory.ProgressLemmas
import Ethereum.Theory.GasLemmas

/-!
# The section

`section_run`, the section theorem: from the start of any block of a checked section's
function (`AtBlock`), the bytes' iterator `X` agrees at profile `P1` (`XAgrees`) with the IR's
run of the function from that block, the prologue `pre` first for the entry block.  It is an
induction on `X`'s fuel and on `zeroRank`, each block by `block_step`, which joins the block
lemma `run_ends` and the IR's run of the statements `body_run` with the IR's `enter` and
terminator.  It also gives `XOk` of the iterator for every condition on calls: the steps of
a checked block go through calm states only (`Steps`).  `XstepN_X_error` and `XstepN_fuel`
take steps to `X` within its fuel;
`checkSection_ok` and `checkBlock_ok` take out of an accepted section what the checker
established.
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
    {fr : Frame} {isRoot : Bool} {entryBlock : Block} {place : Nat → Option Nat}
    {rank : Nat → Nat} {b : Block}
    (h : checkBlock code low hint f fr isRoot entryBlock place rank b = .ok ()) :
    ∃ hb pc stack events calls exit,
      hint.blocks.find? (·.block == b.id) = some hb ∧ place b.id = some pc ∧
      (Ctx.ofBlock f b code.symbols fr).entryStack hb = some stack ∧
      (Ctx.ofBlock f b code.symbols fr).segments b.body = some (events, calls) ∧
      (Ctx.ofBlock f b code.symbols fr).exitOf b.term = some exit ∧
      ((isRoot && b.id == entryBlock.id) = true → stack = []) ∧
      defined f hint.blocks b (hb.entryStack.filterMap fun | .value id => some id | _ => none) =
        true ∧
      (b.term.only.all fun s => place s != some pc || rank s < rank b.id) = true ∧
      run code.bytecode (Ctx.ofBlock f b code.symbols fr) hint.blocks place b.id
        (2 * low.codeSize + 2)
        ⟨pc, stack, prologue low (isRoot && b.id == entryBlock.id) events, exit, calls⟩ =
          true := by
  unfold checkBlock at h
  cases hhb : hint.blocks.find? (·.block == b.id) with
  | none => simp [hhb] at h
  | some hb =>
  simp only [hhb] at h
  cases hpc : place b.id with
  | none => simp [hpc] at h
  | some pc =>
  simp only [hpc] at h
  cases hst : (Ctx.ofBlock f b code.symbols fr).entryStack hb with
  | none => simp [hst] at h
  | some stack =>
  simp only [hst] at h
  cases hev : (Ctx.ofBlock f b code.symbols fr).segments b.body with
  | none => simp [hev] at h
  | some ec =>
  obtain ⟨events, calls⟩ := ec
  simp only [hev] at h
  cases hex : (Ctx.ofBlock f b code.symbols fr).exitOf b.term with
  | none => simp [hex] at h
  | some exit =>
  simp only [hex] at h
  have hthrow : ∀ {m : String} {k : PUnit → Except String Unit},
      ((throw m : Except String PUnit) >>= k) ≠ .ok () := fun h => nomatch h
  refine ⟨hb, pc, stack, events, calls, exit, rfl, rfl, hst, rfl, rfl, ?_⟩
  by_cases h1 : (isRoot && b.id == entryBlock.id) = true
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

theorem forM_bind_ok {α ε : Type} {g : α → Except ε Unit} {l : List α} {k : Except ε Unit}
    (h : (l.forM g >>= fun _ => k) = .ok ()) : l.forM g = .ok () ∧ k = .ok () := by
  cases hl : l.forM g with
  | error e => rw [hl] at h; cases h
  | ok u => rw [hl] at h; exact ⟨rfl, h⟩

/-- What a function the checker accepts is. -/
theorem checkFunc_ok {code : CodeSection} {low : Lowering} {entry : String} {hint : FuncHint}
    (h : checkFunc code low entry hint = .ok ()) :
    ∃ f entryBlock, low.machine.func? hint.name = some f ∧ f.blocks.head? = some entryBlock ∧
      (∀ x ∈ funcChecks low entry hint f entryBlock, x.1 = true) ∧
      ∀ b ∈ f.blocks, checkBlock code low hint f (frameOf low entry f) (hint.name == entry)
        entryBlock (placeIn low hint.name) (zeroRank f (placeIn low hint.name) f.blocks.length)
          b = .ok () := by
  unfold checkFunc at h
  cases hf : low.machine.func? hint.name with
  | none => simp [hf] at h
  | some f =>
  simp only [hf] at h
  cases he : f.blocks.head? with
  | none => simp [he] at h
  | some eb =>
  simp only [he] at h
  obtain ⟨h1, h2⟩ := forM_bind_ok h
  refine ⟨f, eb, rfl, he, fun x hx => ?_, forM_ok h2⟩
  have := forM_ok h1 x hx
  obtain ⟨ok, msg⟩ := x
  cases ok
  · cases this
  · rfl

/-- What a section the checker accepts is. -/
theorem checkSection_ok {code : CodeSection} {entry : String}
    (h : checkSection code entry = .ok ()) :
    ∃ low, code.lowering = some low ∧ code.bytecode.size < UInt256.size ∧
      low.funcs.any (·.name == entry) = true ∧
      ∀ hint ∈ low.funcs, checkFunc code low entry hint = .ok () := by
  unfold checkSection at h
  cases hlow : code.lowering with
  | none => simp [hlow] at h
  | some low =>
  simp only [hlow] at h
  by_cases h1 : code.bytecode.size < UInt256.size
  swap
  · simp [h1] at h; cases h
  simp only [h1, if_true, pure_bind] at h
  by_cases h2 : low.funcs.any (·.name == entry) = true
  swap
  · simp [h2] at h; cases h
  simp only [h2] at h
  exact ⟨low, rfl, h1, h2, forM_ok h⟩

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
    (h : ∀ s ∈ stmts, ∀ d ∈ s.dsts, d.1 ≠ id) :
    (stmts.filterMap Stmt.local?).lookup id = none := by
  induction stmts with
  | nil => rfl
  | cons t rest ih =>
    have ih' := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    cases ht : t.local? with
    | none => simpa [List.filterMap_cons, ht] using ih'
    | some p =>
      have hp : p.1 ≠ id := by
        have ht := local_def ht
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
  (∃ n e, Steps D st (.error e) n ∧ (e = .OutOfGass ∨ e = .StackOverflow ∨
    (e = .StaticModeViolation ∧ r = some (.error .static)) ∨
    (e = .InvalidInstruction ∧ r = some (.error .trap)))) ∨
  (∃ n s' out w', Steps D st (.ok (s', some (.success, out))) n ∧
    r = some (.error (.stop out w')) ∧ s'.accountMap = w'.accounts ∧
    s'.substate.logSeries = w'.logs) ∨
  (∃ n s' data, Steps D st (.ok (s', some (.revert, data))) n ∧
    r = some (.error (.revert data)))

theorem Final.agrees {D : Array UInt256} {st : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} (h : Final D st r) {fuel : Nat}
    (hg : st.machineState.gasAvailable.toNat < fuel) : XAgrees (X fuel D st) r := by
  rcases h with ⟨n, e, hx, he⟩ | ⟨n, s', out, w', hx, hr, ha, hl⟩ | ⟨n, s', data, hx, hr⟩ <;>
    replace hx := hx.xstepN
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

/-- A calm state's step makes no call nor creation, so any condition on them holds of it. -/
theorem Calm.xstepOk {Q : Invariant.CallPreds} {D : Array UInt256} {s : State} (h : Calm s) :
    Invariant.XstepOk Q D s := by
  intro _ _ _
  unfold Calm at h
  unfold Invariant.stepOk
  generalize (decode s.executionEnv.code s.machineState.pc).getD (.STOP, .none) = instr at h ⊢
  split <;> simp_all [callOps]

/-- A step that keeps the environment ends in the state `XOk` goes on from. -/
theorem keep_depth {s s' : State} (h : s'.executionEnv = s.executionEnv) :
    { s' with executionEnv.depth := s.executionEnv.depth } = s' := by
  rw [← h]

/-- Calm steps that stop the iterator make no call nor creation. -/
theorem Steps.xOk_stop {Q : Invariant.CallPreds} {D : Array UInt256} {s : State}
    {r : Except ExecutionException (State × Option (HaltCause × ByteArray))} {n : Nat}
    (h : Steps D s r n) (hr : ∀ t, r ≠ .ok (t, none)) : ∀ f, Invariant.XOk Q f D s := by
  induction h with
  | step hc hx _ =>
    intro f
    cases f with
    | zero => trivial
    | succ f => exact ⟨hc.xstepOk, fun t ht => absurd (hx ▸ ht) (hr t)⟩
  | trans hc hx henv _ ih =>
    intro f
    cases f with
    | zero => trivial
    | succ f =>
      refine ⟨hc.xstepOk, fun t ht => ?_⟩
      rw [hx] at ht
      cases ht
      rw [keep_depth henv]
      exact ih hr f

/-- Calm steps to a state the iterator goes on from add to its `XOk`. -/
theorem Steps.xOk_cont {Q : Invariant.CallPreds} {D : Array UInt256} {s t : State} {n f : Nat}
    (h : Steps D s (.ok (t, none)) n) (ht : Invariant.XOk Q f D t) :
    Invariant.XOk Q (f + n) D s := by
  generalize hr : (Except.ok (t, none) : Except ExecutionException _) = r at h
  induction h generalizing f with
  | step hc hx henv =>
    refine ⟨hc.xstepOk, fun t' ht' => ?_⟩
    subst hr
    rw [hx] at ht'
    cases ht'
    rw [keep_depth (henv _ rfl)]
    exact ht
  | trans hc hx henv _ ih =>
    refine ⟨hc.xstepOk, fun t' ht' => ?_⟩
    rw [hx] at ht'
    cases ht'
    rw [keep_depth henv]
    exact ih ht hr

theorem Final.xOk {Q : Invariant.CallPreds} {D : Array UInt256} {st : State}
    {r : Option (Except (Fe.Exit World) (List Val × World))} (h : Final D st r) (f : Nat) :
    Invariant.XOk Q f D st := by
  rcases h with ⟨n, e, hx, -⟩ | ⟨n, s', out, w', hx, -⟩ | ⟨n, s', data, hx, -⟩ <;>
    exact hx.xOk_stop (by simp) f

/-- The word of an entry slot in an environment, the function's return address `ret`. -/
def SlotWord (env : Env) (ret : Option UInt256) : Slot → UInt256 → Prop
  | .value id, v => env[id]? = some (.int 256 v.toNat)
  | .imm k, v => v = .ofNat k
  | .funcReturn, v => ret = some v
  | .callReturn, _ => False

/-- The values of an entry stack. -/
def slotValues (slots : List Slot) : List Nat :=
  slots.filterMap fun | .value id => some id | _ => none

theorem slots_sub {fr : Frame} {h : BlockHint} {x : Slot} (hx : x ∈ fr.slots h) :
    x ∈ h.entryStack := by
  unfold Frame.slots at hx
  split at hx
  · exact hx
  · exact (List.mem_filter.mp hx).1

/-- Only a function that returns has a block that returns. -/
theorem exitOf_ret {c : Ctx} {t : Term} {vals : List Expr} (h : c.exitOf t = some (.ret vals)) :
    c.frame.returns = true := by
  cases t with
  | ret vs =>
    unfold Ctx.exitOf at h
    split_ifs at h with hr
    exact hr
  | brTable sc d cases =>
    cases d with
    | none => simp [Ctx.exitOf] at h
    | some d =>
      simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, h⟩ := h
      cases h
  | _ => simp [Ctx.exitOf, Option.bind_eq_some_iff] at h

theorem slotValues_filter : ∀ l : List Slot,
    slotValues (l.filter (· != .funcReturn)) = slotValues l
  | [] => rfl
  | sl :: rest => by
    have ih := slotValues_filter rest
    cases sl with
    | value id =>
      rw [List.filter_cons_of_pos (by rfl)]
      simp only [slotValues, List.filterMap_cons] at ih ⊢
      rw [ih]
    | imm v =>
      rw [List.filter_cons_of_pos (by rfl)]
      simp only [slotValues, List.filterMap_cons] at ih ⊢
      rw [ih]
    | funcReturn =>
      rw [List.filter_cons_of_neg (by decide)]
      simp only [slotValues, List.filterMap_cons] at ih ⊢
      exact ih
    | callReturn =>
      rw [List.filter_cons_of_pos (by rfl)]
      simp only [slotValues, List.filterMap_cons] at ih ⊢
      exact ih

/-- The planned entry stack has the values the lowering record's does. -/
theorem slotValues_slots (fr : Frame) (h : BlockHint) :
    slotValues (fr.slots h) = slotValues h.entryStack := by
  unfold Frame.slots
  split
  · rfl
  · exact slotValues_filter _

/-- The planned entry stack's expressions have the EVM stack's words, its values not the
    block's own. -/
theorem entryStack_rel {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {envB : Env}
    {ret : Option UInt256} (hR : ∀ v, ret = some v → ρ c.frame.retId = v) :
    ∀ {slots : List Slot} {ws : List UInt256} {es : List Expr},
      (∀ id ∈ slotValues slots, c.defs.lookup id = none) →
      (∀ id ∈ slotValues slots, envB[id]? = some (.int 256 (ρ id).toNat)) →
      List.Forall₂ (SlotWord envB ret) slots ws →
      slots.mapM c.slotExpr = some es →
      es.mapM (·.eval ee ρ) = some ws
  | [], [], es, _, _, .nil, h => by simp at h; subst h; rfl
  | sl :: slots, w :: ws, es, hl, hρ, .cons hw hrest, h => by
    have hl' : ∀ id ∈ slotValues slots, c.defs.lookup id = none := fun id hid =>
      hl id (by cases sl <;> simp_all [slotValues])
    have hρ' : ∀ id ∈ slotValues slots, envB[id]? = some (.int 256 (ρ id).toNat) := fun id hid =>
      hρ id (by cases sl <;> simp_all [slotValues])
    rw [List.mapM_cons] at h
    cases sl with
    | value id =>
      have hid : id ∈ slotValues (.value id :: slots) := by simp [slotValues]
      have he := expand_atom (hl id hid) 63
      simp only [Ctx.slotExpr, show depth = 63 + 1 from rfl, he, Option.bind_eq_bind,
        Option.bind_some] at h
      cases hs : slots.mapM c.slotExpr with
      | none => simp [hs] at h
      | some es' =>
        simp only [hs, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have hw' : w = ρ id := word_inj (Option.some.inj (hw.symm.trans (hρ id hid)))
        simp [List.mapM_cons, Expr.eval, entryStack_rel hR hl' hρ' hrest hs, hw']
    | imm k =>
      simp only [Ctx.slotExpr, Option.bind_eq_bind, Option.bind_some] at h
      cases hs : slots.mapM c.slotExpr with
      | none => simp [hs] at h
      | some es' =>
        simp only [hs, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have hw' : w = .ofNat k := hw
        simp [List.mapM_cons, Expr.eval, entryStack_rel hR hl' hρ' hrest hs, hw']
    | funcReturn =>
      by_cases hr : c.frame.returns = true
      swap
      · simp [Ctx.slotExpr, hr] at h
      simp only [Ctx.slotExpr, hr, if_true, Option.bind_eq_bind, Option.bind_some] at h
      cases hs : slots.mapM c.slotExpr with
      | none => simp [hs] at h
      | some es' =>
        simp only [hs, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, Expr.eval, entryStack_rel hR hl' hρ' hrest hs, hR w hw]
    | callReturn => cases hw

/-- The bytes are at the start of block `b`, entered from `prev` with the run's values `env`:
    the code, the pc at `b`'s offset, the world agreeing, and the planned entry stack's words on
    top of the EVM stack, as the values are once `b` is entered. -/
def AtBlock (low : Lowering) (hint : FuncHint) (f : Func) (fr : Frame) (I : ExecutionEnv)
    (b : Block) (prev : Option Nat) (env : Env) (w : World) (st : State) (ret : Option UInt256)
    (B : List UInt256) : Prop :=
  b ∈ f.blocks ∧ f.block? b.id = some b ∧ st.executionEnv = I ∧ Agree st w ∧
  ∃ hb pc envB ws, hint.blocks.find? (·.block == b.id) = some hb ∧
    placeIn low hint.name b.id = some pc ∧ st.machineState.pc.toNat = pc ∧
    enter env prev b = pure envB ∧ st.machineState.stack = ws ++ B ∧
    List.Forall₂ (SlotWord envB ret) (fr.slots hb) ws ∧
    ∀ phi ∈ b.phis, ∃ n, envB[phi.dst]? = some (.int 256 n) ∧ n < UInt256.size

/-- What the section entry's code does before the entry block: it stores the initial free
    pointer. -/
def pre (low : Lowering) (eb b : Block) : FeM Unit :=
  if b.id = eb.id then
    match low.entryFreePtr with
    | some ptr => mstore (.ofNat 0x40) (.ofNat ptr)
    | none => pure ()
  else pure ()

/-- The prologue runs to a world the prologue event traces to. -/
theorem pre_trace (low : Lowering) (eb b : Block) (I : ExecutionEnv) (w : World) :
    ∃ w₀, (pre low eb b).exec I w = some (.ok ((), w₀)) ∧
      ∀ ρ evs r, Trace I ρ evs w₀ r → Trace I ρ (prologue low (b.id == eb.id) evs) w r := by
  unfold pre prologue
  by_cases he : b.id = eb.id
  · cases hp : low.entryFreePtr with
    | none => exact ⟨w, by simp [he], fun ρ evs r h => by simpa using h⟩
    | some ptr =>
      refine ⟨_, by simp [he]; rfl, fun ρ evs r h => ?_⟩
      simp only [he, beq_self_eq_true]
      exact .ok (args := [.ofNat 0x40, .ofNat ptr]) rfl rfl h
  · refine ⟨w, by simp [he], fun ρ evs r h => ?_⟩
    have : (b.id == eb.id) = false := by simpa using he
    cases low.entryFreePtr <;> simpa [this] using h

theorem slot_word {envB : Env} {ret : Option UInt256} :
    ∀ {slots : List Slot} {ws : List UInt256} {id : Nat},
    List.Forall₂ (SlotWord envB ret) slots ws → id ∈ slotValues slots →
      ∃ v : UInt256, envB[id]? = some (.int 256 v.toNat)
  | [], [], _, .nil, h => by simp [slotValues] at h
  | sl :: slots, w :: ws, id, .cons hw hrest, h => by
    cases sl with
    | value id' =>
      by_cases he : id = id'
      · subst he; exact ⟨w, hw⟩
      · exact slot_word hrest (by simpa [slotValues, he] using h)
    | _ => exact slot_word hrest (by simpa [slotValues] using h)

/-- The words of a run's values. -/
def wordsOf (env : Env) (id : Nat) : UInt256 :=
  match env[id]? with
  | some (.int _ n) => .ofNat n
  | _ => ⟨0⟩

theorem wordsOf_words {env : Env} {D : List Nat}
    (h : ∀ id ∈ D, ∃ n, env[id]? = some (.int 256 n) ∧ n < UInt256.size) :
    WordsOf env (wordsOf env) D := fun id hid => by
  obtain ⟨n, hn, hlt⟩ := h id hid
  simp [wordsOf, hn, toNat_ofNat_lt hlt]

theorem operand_words {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D : List Nat}
    {env : Env} {o : Operand} {e : Expr} (hc : Cons ee ρ c D) (hw : WordsOf env ρ D)
    (hr : reads D [o] = true) (h : c.operand depth o = some e) :
    ∃ v, e.eval ee ρ = some v ∧ opWord ρ o = some v ∧
      evalOperand env o = pure (.int 256 v.toNat) := by
  have he := operand_eval (ee := ee) (ρ := ρ) (fun id e' ho he' => expand_eval hc depth id e'
    (by subst ho; simpa [reads, Operand.var?] using hr) he') h
  obtain ⟨v, hv⟩ := opWord_some (ρ := ρ) h
  exact ⟨v, he.trans hv, hv, evalOperand_word hw hr hv⟩

theorem exitOf_succ {c : Ctx} {t : Term} {e : Exit} {ee : ExecutionEnv} {ρ : Nat → UInt256}
    {d : Nat} (h : c.exitOf t = some e) (hn : e.next ee ρ = some d) : d ∈ t.succs := by
  cases t with
  | jump d' =>
    simp only [Ctx.exitOf, Option.some.injEq] at h; subst h
    simp only [Exit.next, Option.some.injEq] at hn; subst hn
    simp [Term.succs]
  | br cond nz z =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ce, -, rfl⟩ := h
    simp only [Exit.next, Option.map_eq_some_iff] at hn
    obtain ⟨v, -, rfl⟩ := hn
    split <;> simp [Term.succs]
  | brTable sc def? cases =>
    cases def? with
    | none => simp [Ctx.exitOf] at h
    | some d' =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs, hcs, ce, -, rfl⟩ := h
    simp only [Exit.next, Option.map_eq_some_iff] at hn
    obtain ⟨v, -, hd⟩ := hn
    simp only [Term.succs, Option.toList_some, List.cons_append, List.mem_cons, List.nil_append,
      List.mem_map]
    cases hf : cs.find? (UInt256.ofNat ·.1 == v) with
    | none => rw [hf] at hd; simp at hd; exact .inl hd.symm
    | some kd =>
      rw [hf] at hd
      simp only [Option.map_some, Option.getD_some] at hd
      subst hd
      have hm := List.mem_of_find?_eq_some hf
      have h2 := mapM_some_iff.mp hcs
      right
      clear hf hcs
      induction h2 with
      | nil => cases hm
      | cons hxy _ ih =>
        rcases List.mem_cons.mp hm with rfl | hm
        · rename_i x _ _ _
          obtain ⟨o, dest⟩ := x
          simp only at hxy
          split at hxy
          · split_ifs at hxy; cases hxy; exact ⟨_, List.mem_cons_self .., rfl⟩
          · cases hxy
        · obtain ⟨x', hx', he'⟩ := ih hm
          exact ⟨x', List.mem_cons_of_mem _ hx', he'⟩
  | _ =>
    simp [Ctx.exitOf, Option.bind_eq_some_iff] at h
    (try (obtain ⟨_, _, _, _, rfl⟩ := h))
    simp [Exit.next] at hn

/-- The halting terminators the checker reads. -/
theorem exitOf_halt {c : Ctx} {t : Term} {op : Operation} {args : List Expr}
    (h : c.exitOf t = some (.halt op args)) :
    (∃ a l ea el, t = .evmReturn a l ∧ op = .RETURN ∧ args = [ea, el] ∧
      c.operand depth a = some ea ∧ c.operand depth l = some el) ∨
    (∃ a l ea el, t = .evmRevert a l ∧ op = .REVERT ∧ args = [ea, el] ∧
      c.operand depth a = some ea ∧ c.operand depth l = some el) ∨
    (t = .evmStop ∧ op = .STOP ∧ args = []) ∨ (t = .evmInvalid ∧ op = .INVALID ∧ args = []) := by
  cases t with
  | evmReturn a l =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Exit.halt.injEq] at h
    obtain ⟨ea, hea, el, hel, rfl, rfl⟩ := h
    exact .inl ⟨a, l, ea, el, rfl, rfl, rfl, hea, hel⟩
  | evmRevert a l =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Exit.halt.injEq] at h
    obtain ⟨ea, hea, el, hel, rfl, rfl⟩ := h
    exact .inr (.inl ⟨a, l, ea, el, rfl, rfl, rfl, hea, hel⟩)
  | evmStop =>
    simp only [Ctx.exitOf, Option.some.injEq, Exit.halt.injEq] at h
    exact .inr (.inr (.inl ⟨rfl, h.1.symm, h.2.symm⟩))
  | evmInvalid =>
    simp only [Ctx.exitOf, Option.some.injEq, Exit.halt.injEq] at h
    exact .inr (.inr (.inr ⟨rfl, h.1.symm, h.2.symm⟩))
  | brTable sc def? cases =>
    cases def? <;> simp [Ctx.exitOf, Option.bind_eq_some_iff] at h
  | _ => simp [Ctx.exitOf, Option.bind_eq_some_iff] at h

theorem exitOf_only {c : Ctx} {t : Term} {e : Exit} {S : Nat} (h : c.exitOf t = some e)
    (hs : e.selected = some S) : t.only = some S := by
  cases t with
  | jump d =>
    simp only [Ctx.exitOf, Option.some.injEq] at h; subst h
    simpa [Exit.selected, Term.only] using hs
  | brTable sc def? cases =>
    cases def? with
    | none => simp [Ctx.exitOf] at h
    | some d =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cs, hcs, ce, -, rfl⟩ := h
    simp only [Exit.selected] at hs
    split_ifs at hs with hall
    cases hs
    have hl := (mapM_some_iff.mp hcs).length_eq
    cases cases with
    | nil => rfl
    | cons x xs =>
      cases cs with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.all_cons, List.contains_nil, Bool.false_and, reduceCtorEq] at hall
  | br cond nz z =>
    simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ce, -, rfl⟩ := h
    simp [Exit.selected] at hs
  | _ =>
    simp [Ctx.exitOf, Option.bind_eq_some_iff] at h
    (try (obtain ⟨_, _, _, _, rfl⟩ := h))
    simp [Exit.selected] at hs

theorem table_vals {env : Env} : ∀ {cases : List (Operand × Nat)} {cs : List (Nat × Nat)},
    cases.mapM (fun (x : Operand × Nat) => match x.1 with
      | .imm 256 v => if v < UInt256.size then some (v, x.2) else none
      | _ => none) = some cs →
    (cases.mapM fun x => do let r ← evalInt env x.1; pure (r.2, x.2) : FeM _) = pure cs
  | [], cs, h => by simp at h; subst h; rfl
  | (o, dest) :: cases, cs, h => by
    rw [List.mapM_cons] at h
    cases o with
    | imm bits k =>
      by_cases hb : bits = 256
      · subst hb
        by_cases hlt : k < UInt256.size
        · cases hcs : cases.mapM (fun (x : Operand × Nat) => match x.1 with
              | .imm 256 v => if v < UInt256.size then some (v, x.2) else none
              | _ => none) with
          | none => simp [hcs, hlt] at h
          | some cs' =>
            simp only [hcs, hlt, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at h
            subst h
            rw [List.mapM_cons, table_vals hcs]
            simp [evalInt, evalOperand]
        · simp [hlt] at h
      · simp [hb] at h
    | _ => simp at h

theorem find_table {v : UInt256} : ∀ {cs : List (Nat × Nat)},
    (∀ kd ∈ cs, kd.1 < UInt256.size) →
    cs.find? (·.1 == v.toNat) = cs.find? (UInt256.ofNat ·.1 == v)
  | [], _ => rfl
  | kd :: cs, hcs => by
    have hk := hcs kd (by simp)
    have heq : (kd.1 == v.toNat) = (UInt256.ofNat kd.1 == v) := by
      by_cases h : kd.1 = v.toNat
      · simp [h, Reasoning.Theory.u256_ofNat_toNat]
      · have : UInt256.ofNat kd.1 ≠ v := fun h' => h (by rw [← h', toNat_ofNat_lt hk])
        simp [h, this]
    simp only [List.find?_cons, heq, find_table fun kd' h' => hcs kd' (List.mem_cons_of_mem _ h')]

theorem nodup_iff : ∀ (l : List Nat), nodup l = true ↔ l.Nodup
  | [] => by simp [nodup]
  | x :: xs => by simp [nodup, nodup_iff xs]

/-- The successor's entry slots, as the predecessor's expressions give them, have the words
    its values have once entered. -/
theorem arrival_rel {ee : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {D : List Nat}
    {env envS : Env} {Sb : Block} {pred : Nat} (hc : Cons ee ρ c D) (hw : WordsOf env ρ D)
    (hphi : ∀ phi ∈ Sb.phis, phi.ty.bits = 256 ∧ ∃ o d val,
      phi.incoming.find? (·.2 == pred) = some (o, d) ∧ reads D [o] = true ∧
      evalOperand env o = pure val ∧ envS[phi.dst]? = some (val.as phi.ty))
    (hkeep : ∀ id, id ∉ Sb.phis.map (·.dst) → envS[id]? = env[id]?) {ret : Option UInt256}
    (hR : c.frame.returns = true → ret = some (ρ c.frame.retId)) :
    ∀ {slots : List Slot} {es : List Expr} {ws : List UInt256},
      slots.all (slotDefined D Sb) = true →
      slots.mapM (c.arrivalSlot Sb pred) = some es → es.mapM (·.eval ee ρ) = some ws →
      List.Forall₂ (SlotWord envS ret) slots ws
  | [], es, ws, _, h1, h2 => by
    simp at h1; subst h1; simp at h2; subst h2; exact .nil
  | sl :: slots, es, ws, hall, h1, h2 => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [List.mapM_cons] at h1
    cases he : c.arrivalSlot Sb pred sl with
    | none => simp [he] at h1
    | some e =>
    cases hes : slots.mapM (c.arrivalSlot Sb pred) with
    | none => simp [he, hes] at h1
    | some es' =>
    simp only [he, hes, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h1
    subst h1
    rw [List.mapM_cons] at h2
    cases hv : e.eval ee ρ with
    | none => simp [hv] at h2
    | some v =>
    cases hws : es'.mapM (·.eval ee ρ) with
    | none => simp [hv, hws] at h2
    | some ws' =>
    simp only [hv, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h2
    subst h2
    refine .cons ?_ (arrival_rel hc hw hphi hkeep hR hall.2 hes hws)
    cases sl with
    | value id =>
      simp only [Ctx.arrivalSlot] at he
      cases hf : Sb.phis.find? (·.dst == id) with
      | some phi =>
        rw [hf] at he
        have hp := List.mem_of_find?_eq_some hf
        have hd : phi.dst = id := by simpa using List.find?_some hf
        obtain ⟨hty, o, d, val, hio, hr, hval, hS⟩ := hphi phi hp
        simp only [hio, Option.bind_eq_bind, Option.bind_some] at he
        obtain ⟨v', hev, -, heo⟩ := operand_words hc hw hr he
        rw [hev] at hv; cases hv
        rw [hval] at heo
        have : val = .int 256 v.toNat := by
          have := congrArg (fun m => Fe.M.exec m ee (World.init ∅ default)) heo
          simpa using this
        subst this
        show envS[id]? = _
        rw [← hd, hS, as_word _ hty, Reasoning.Theory.u256_ofNat_toNat]
      | none =>
        rw [hf] at he
        have hnot : id ∉ Sb.phis.map (·.dst) := by
          intro hm
          obtain ⟨phi, hp, rfl⟩ := List.mem_map.mp hm
          rw [List.find?_eq_none] at hf
          exact hf phi hp (by simp)
        have hid : id ∈ D := by
          have h := hall.1
          simp only [slotDefined, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
            beq_iff_eq] at h
          rcases h with h | ⟨phi, hp, hd⟩
          · exact h
          · exact absurd (List.mem_map.mpr ⟨phi, hp, hd⟩) hnot
        rw [expand_eval hc depth id e hid he] at hv
        cases hv
        show envS[id]? = _
        rw [hkeep id hnot]
        exact hw id hid
    | imm k =>
      simp only [Ctx.arrivalSlot, Option.some.injEq] at he
      subst he
      simp only [Expr.eval, Option.some.injEq] at hv
      exact hv.symm
    | funcReturn =>
      simp only [Ctx.arrivalSlot] at he
      split_ifs at he with hr
      cases he
      simp only [Expr.eval, Option.some.injEq] at hv
      subst hv
      exact hR hr
    | callReturn => simp [Ctx.arrivalSlot] at he

/-- Without a function to call, a block's statements have no calls, and its events are its
    statements'. -/
theorem segments_nocall {c : Ctx} (hc : ∀ g, c.frame.callee g = none) :
    ∀ {stmts : List Stmt} {evs : List Event} {calls : List CallSeg},
      c.segments stmts = some (evs, calls) →
        calls = [] ∧ stmts.filterMapM c.eventOfStmt = some evs
  | [], evs, calls, h => by
    simp only [Ctx.segments, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | s :: rest, evs, calls, h => by
    unfold Ctx.segments at h
    cases hr : c.segments rest with
    | none => simp [hr] at h
    | some ec =>
      obtain ⟨evs', calls'⟩ := ec
      obtain ⟨h1, h2⟩ := segments_nocall hc hr
      simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · next g args hg => simp [hc g] at h
      · cases he : c.eventOfStmt s with
        | none => simp [he] at h
        | some o =>
          cases o with
          | none =>
            simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [List.filterMapM_cons, he, h2, h1]
          | some e =>
            simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [List.filterMapM_cons, he, h2, h1]

set_option maxHeartbeats 1000000 in
/-- One block of a checked section: the bytes end as the IR's run does, or reach the next
    block's code where the IR's run goes on there. -/
theorem block_step {code : CodeSection} {low : Lowering} {hint : FuncHint} {f : Func}
    {eb : Block} {I : ExecutionEnv} {tail : ByteArray} {ic : Fe.Sonatina.Ctx}
    (hI : I.code = code.bytecode ++ tail) (hsize : code.bytecode.size < UInt256.size)
    (hsym : ic.symbol = (code.symbols.lookup ·))
    (hbits : (f.blocks.all fun b => b.phis.all (·.ty.bits == 256) &&
        b.body.all (·.dsts.all (·.2.bits == 256))) = true)
    (hnd : nodup (f.blocks.flatMap fun b =>
        b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) = true)
    {fr : Frame} (hchk : ∀ b ∈ f.blocks, checkBlock code low hint f fr true eb
        (placeIn low hint.name) (zeroRank f (placeIn low hint.name) f.blocks.length) b = .ok ())
    (hpred : ∀ x ∈ f.blocks, eb.id ∉ x.term.succs) (hret : fr.returns = false)
    (hcal : ∀ g, fr.callee g = none)
    {b : Block} {prev : Option Nat} {env : Env} {w : World} {st : State} {B : List UInt256}
    (hat : AtBlock low hint f fr I b prev env w st none B) :
    Final (D_J I.code 0) st
        ((pre low eb b >>= fun _ => runBlocks low.machine ic f env prev b.id).exec I w) ∨
      ∃ S env' w' st' n B', Reach (D_J I.code 0) st st' n ∧
        (n = 0 → zeroRank f (placeIn low hint.name) f.blocks.length S.id <
          zeroRank f (placeIn low hint.name) f.blocks.length b.id) ∧
        AtBlock low hint f fr I S (some b.id) env' w' st' none B' ∧ S.id ≠ eb.id ∧
        (pre low eb b >>= fun _ => runBlocks low.machine ic f env prev b.id).exec I w =
          (runBlocks low.machine ic f env' (some b.id) S.id).exec I w' := by
  obtain ⟨hmem, hblk, henv, hw, hb, pc, envB, ws, hhb, hpc, hstpc, henter, hstk, hslots,
    hphis⟩ := hat
  obtain ⟨hb', pc', stack, events, calls, exit, hhb', hpc', hst, hseg, hex, hempty, hdef, hrank,
    hrun⟩ := checkBlock_ok (hchk b hmem)
  obtain ⟨rfl, hev⟩ := segments_nocall hcal hseg
  rw [hhb] at hhb'; cases hhb'
  rw [hpc] at hpc'; cases hpc'
  replace hdef : defined f hint.blocks b (slotValues hb.entryStack) = true := hdef
  set c := Ctx.ofBlock f b code.symbols fr with hc
  -- The block's values: the entry stack's and the phis, and after the statements `D'`.
  unfold defined at hdef
  cases hDA : definedAfter (slotValues hb.entryStack ++ b.phis.map (·.dst)) b.body with
  | none => simp [hDA] at hdef
  | some D' =>
  simp only [hDA, Bool.and_eq_true, List.all_eq_true] at hdef
  set D := slotValues hb.entryStack ++ b.phis.map (·.dst) with hD
  obtain ⟨hterm, hsucc⟩ := hdef
  have hfresh := definedAfter_fresh hDA
  have hnone : ∀ id ∈ D, c.defs.lookup id = none := fun id hid =>
    lookup_none fun s hs d hd h => hfresh s hs d hd (h ▸ hid)
  -- The values entering the block are words.
  have hwB : WordsOf envB (wordsOf envB) D := wordsOf_words fun id hid => by
    rcases List.mem_append.mp hid with h | h
    · obtain ⟨v, hv⟩ := slot_word hslots (by rw [slotValues_slots]; exact h)
      exact ⟨v.toNat, hv, v.val.isLt⟩
    · obtain ⟨phi, hp, rfl⟩ := List.mem_map.mp h
      exact hphis phi hp
  obtain ⟨w₀, hpre, htrace⟩ := pre_trace low eb b I w
  have hbitsb : ∀ s ∈ b.body, ∀ d ∈ s.dsts, d.2.bits = 256 := by
    have := List.all_eq_true.mp hbits b hmem
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
    exact fun s hs d hd => this.2 s hs d hd
  obtain ⟨x, hx, hends⟩ := body_run (ee := I) (m := low.machine) (c := c) hsym b.body [] D D'
    envB w₀ events (by simp [c, Ctx.ofBlock]) (by simp) hDA hev hbitsb ⟨_, hwB⟩
    fun ρ _ id hid inst hl => by rw [hnone id hid] at hl; cases hl
  -- The IR's run of the block from its start.
  have hR : (pre low eb b >>= fun _ => runBlocks low.machine ic f env prev b.id).exec I w =
      (runBlocks low.machine ic f env prev b.id).exec I w₀ := by
    rw [Fe.M.exec_bind, hpre]
  rw [hR]
  have hpath : ∀ ρ, WordsOf envB ρ D → PathRel code.bytecode tail I ρ B exit
      ⟨pc, stack, prologue low (true && b.id == eb.id) events, exit, []⟩ st := fun ρ hρ =>
    ⟨henv, hI, hstpc, ⟨ws,
      entryStack_rel (fun _ h => by cases h)
        (fun id hid => hnone id (List.mem_append_left _ (by rwa [slotValues_slots] at hid)))
        (fun id hid => hρ id (List.mem_append_left _ (by rwa [slotValues_slots] at hid))) hslots
        hst, hstk⟩,
      exitOf_valid hex I ρ, .inl rfl⟩
  have hends' := fun ρ r (hρ : WordsOf envB ρ D) (htr : Trace I ρ events w₀ r) =>
    run_ends (tail := tail) (e0 := exit) hsize
      (fun h => absurd h (by simp [c, Ctx.ofBlock, hret])) _ _ st w r B hrun (hpath ρ hρ) hw
      (htrace ρ _ r htr)
  cases x with
  | error e =>
    obtain ⟨envf, Df, hagr, hsub, ⟨ρ, hρ⟩, hall⟩ := hends
    have hρD : WordsOf envB ρ D := fun id hid => (hagr id hid).symm.trans (hρ id (hsub id hid))
    have hE := hends' ρ _ hρD (hall ρ hρ).2
    left
    have hIR : (runBlocks low.machine ic f env prev b.id).exec I w₀ = some (.error e) := by
      rw [runBlocks.eq_1, hblk]
      simp only [henter, pure_bind, Fe.M.exec_bind, hx]
    rw [hIR]
    rcases hE with ⟨n, e', hxs, he'⟩ | ⟨hr, n, hxs⟩ | ⟨w', hr, -⟩
    · exact .inl ⟨n, e', hxs, by rcases he' with h | h <;> simp [h]⟩
    · cases hr; exact .inl ⟨n, _, hxs, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · cases hr
  | ok p =>
    obtain ⟨env', w'⟩ := p
    obtain ⟨hagr, ⟨ρ, hρ⟩, hall⟩ := hends
    have hρD : WordsOf envB ρ D := fun id hid =>
      (hagr id hid).symm.trans (hρ id (definedAfter_mono hDA id hid))
    have hE := hends' ρ _ hρD (hall ρ hρ).2
    have hcons := (hall ρ hρ).1
    rw [runBlocks.eq_1, hblk]
    simp only [henter, pure_bind, Fe.M.exec_bind, hx]
    rcases hE with ⟨n, e', hxs, he'⟩ | ⟨hr, -⟩ | ⟨w'', hr, harr | ⟨op, args, hws, hex0, hargs, hh⟩ |
      ⟨vals, -, -, -, hex0, -⟩ | ⟨cs, more, -, -, -, -, -, -, -, -, -, hcl, -⟩ |
      ⟨cs, -, -, -, -, -, hcl, -⟩⟩
    · left; exact .inl ⟨n, e', hxs, by rcases he' with h | h <;> simp [h]⟩
    · cases hr
    · cases hr
      obtain ⟨S, n, st', pc', exprs, B', hnh, hjmp, hzero, hreach, hnext, hplS, hpcS, harr, hrel,
        -, henvS, hagS⟩ := harr
      simp only [Ctx.arrival, Option.bind_eq_bind, Option.bind_eq_some_iff] at harr
      obtain ⟨hbS, hhbS, Sb, hSb, hmapS⟩ := harr
      change f.block? S = some Sb at hSb
      have hSbmem : Sb ∈ f.blocks := List.mem_of_find?_eq_some hSb
      have hSid : Sb.id = S := by simpa using List.find?_some hSb
      -- The successor, entered from `b`, is where the bytes are.
      have key : ∀ d, exit.next I ρ = some d →
          AtBlock low hint f fr I Sb (some b.id) env' w' st' none B' ∧
          d = Sb.id := by
        intro d hd
        have hdS := hnext d hd
        subst hdS
        refine ⟨?_, hSid.symm⟩
        have hsuccS := hsucc _ (exitOf_succ hex hd)
        rw [hSb] at hsuccS
        simp only [Bool.and_eq_true, List.all_eq_true] at hsuccS
        obtain ⟨hphisS, hslotsS⟩ := hsuccS
        have hndS : (Sb.phis.map (·.dst)).Nodup := by
          have := (nodup_iff _).mp hnd
          exact ((List.nodup_flatMap.mp this).1 Sb hSbmem).of_append_left
        have hbitsS := List.all_eq_true.mp hbits Sb hSbmem
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hbitsS
        have hin : ∀ phi ∈ Sb.phis, ∃ o d, phi.incoming.find? (·.2 == b.id) = some (o, d) ∧
            reads D' [o] = true ∧ ∀ ty, o ≠ .undef ty := fun phi hp => by
          have := hphisS phi hp
          rcases hf : phi.incoming.find? (fun x => x.2 == b.id) with _ | ⟨o, d⟩
          · simp [hf] at this
          · refine ⟨o, d, hf, ?_⟩
            rw [hf] at this
            cases o <;> simp_all
        obtain ⟨envS, henterS, hphiS, hkeepS⟩ := enter_run (fun phi hp => by
          obtain ⟨o, d, hf, hr, -⟩ := hin phi hp; exact ⟨o, d, hf, hr⟩) hρ hndS
        obtain ⟨ws', hws', hstk'⟩ := hrel
        refine ⟨hSbmem, by rw [hSid]; exact hSb, henvS, hagS, hbS, pc', envS, ws',
          by rw [hSid]; exact hhbS, by rw [hSid]; exact hplS, hpcS, henterS, hstk', ?_, ?_⟩
        · have hall : (fr.slots hbS).all (slotDefined D' Sb) = true := by
            have := hslotsS
            rw [hhbS] at this
            simp only [Option.all_some] at this
            exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp this x (slots_sub hx)
          exact arrival_rel hcons hρ (ret := none) (fun phi hp => by
            obtain ⟨o, d, val, hf, hev, hS⟩ := hphiS phi hp
            obtain ⟨o', d', hf', hr', -⟩ := hin phi hp
            rw [hf] at hf'; cases hf'
            exact ⟨hbitsS.1 phi hp, o, d, val, hf, hr', hev, hS⟩) hkeepS
            (fun h => absurd h (by simp [c, Ctx.ofBlock, hret])) hall hmapS hws'
        · intro phi hp
          obtain ⟨o, d, val, hf, hev, hS⟩ := hphiS phi hp
          obtain ⟨o', d', hf', hr', hnu⟩ := hin phi hp
          rw [hf] at hf'; cases hf'
          have hval : ∃ bits k, val = .int bits k := by
            have hex' : ∀ {a b : FeM Val}, a = b →
                a.exec I (World.init ∅ default) = b.exec I (World.init ∅ default) :=
              fun h => h ▸ rfl
            cases o with
            | var id =>
              have hid : id ∈ D' := by simpa [reads, Operand.var?] using hr'
              have := hex' hev
              simp [evalOperand, hρ id hid] at this
              exact ⟨_, _, this.symm⟩
            | imm bits k =>
              have := hex' hev
              simp [evalOperand] at this
              exact ⟨_, _, this.symm⟩
            | undef ty => exact absurd rfl (hnu ty)
          obtain ⟨bits, k, rfl⟩ := hval
          exact ⟨_, by rw [hS, as_int _ _ (hbitsS.1 phi hp)]; rfl, (UInt256.ofNat k).val.isLt⟩
      -- In no step the exit selected the successor: its code is at `b`'s, so it is lower.
      have hlow : n = 0 → zeroRank f (placeIn low hint.name) f.blocks.length Sb.id <
          zeroRank f (placeIn low hint.name) f.blocks.length b.id := fun hn => by
        have hsel := hzero hn
        have honly := exitOf_only hex hsel
        rw [honly] at hrank
        simp only [Option.all_some, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hrank
        rcases hreach with ⟨-, rfl⟩ | hx
        · rcases hrank with h | h
          · exact absurd (by rw [hplS, ← hpcS, hstpc]) h
          · rw [hSid]; exact h
        · subst hn; cases hx
      have hfin : ∀ d, exit.next I ρ = some d →
          ∃ S' env'' w'' st'' n' B'', Reach (D_J I.code 0) st st'' n' ∧
            (n' = 0 → zeroRank f (placeIn low hint.name) f.blocks.length S'.id <
              zeroRank f (placeIn low hint.name) f.blocks.length b.id) ∧
            AtBlock low hint f fr I S' (some b.id) env'' w'' st'' none B'' ∧ S'.id ≠ eb.id ∧
            (runBlocks low.machine ic f env' (some b.id) d).exec I w' =
              (runBlocks low.machine ic f env'' (some b.id) S'.id).exec I w'' := fun d hd => by
        obtain ⟨hat', hdS⟩ := key d hd
        exact ⟨Sb, env', w', st', n, B', hreach, hlow, hat',
          fun h => hpred b hmem (h ▸ hdS ▸ exitOf_succ hex hd), by rw [hdS]⟩
      right
      cases ht : b.term with
      | jump d =>
        rw [ht] at hex; simp only [Ctx.exitOf, Option.some.injEq] at hex; subst hex
        simpa using hfin d rfl
      | br cond nz z =>
        rw [ht] at hex hterm
        simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hex
        obtain ⟨ce, hce, rfl⟩ := hex
        obtain ⟨v, hv, -, hev⟩ := operand_words hcons hρ (by simpa [Term.operands] using hterm) hce
        have := hfin (if v.toNat != 0 then nz else z) (by simp [Exit.next, hv])
        simpa [evalInt, hev] using this
      | brTable sc def? cases =>
        cases def? with
        | none => rw [ht] at hex; simp [Ctx.exitOf] at hex
        | some dd =>
        rw [ht] at hex hterm
        simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hex
        obtain ⟨cs, hcs, ce, hce, rfl⟩ := hex
        simp only [Term.operands, reads, List.all_cons, Bool.and_eq_true] at hterm
        obtain ⟨v, hv, -, hev⟩ := operand_words hcons hρ (by simpa [reads] using hterm.1) hce
        have hlt : ∀ kd ∈ cs, kd.1 < UInt256.size := mapM_forall hcs fun x y hxy => by
          obtain ⟨o, dest⟩ := x
          simp only at hxy
          split at hxy
          · split_ifs at hxy with hv'; cases hxy; exact hv'
          · cases hxy
        have := hfin (((cs.find? (UInt256.ofNat ·.1 == v)).map (·.2)).getD dd)
          (by simp [Exit.next, hv])
        have hei : evalInt env' sc = pure (256, v.toNat) := by simp [evalInt, hev]
        simp only [hei, pure_bind]
        rw [table_vals (env := env') hcs]
        simp only [pure_bind]
        rw [← find_table hlt] at this
        cases hf : cs.find? (·.1 == v.toNat) with
        | none => simpa [hf] using this
        | some kd => simpa [hf] using this
      | evmReturn a l | evmRevert a l =>
        rw [ht] at hex
        simp only [Ctx.exitOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hex
        obtain ⟨_, _, _, _, rfl⟩ := hex
        exact absurd rfl (hnh _ _)
      | evmStop | evmInvalid =>
        rw [ht] at hex
        simp only [Ctx.exitOf, Option.some.injEq] at hex
        subst hex
        exact absurd rfl (hnh _ _)
      | ret vs =>
        rw [ht] at hex
        unfold Ctx.exitOf at hex
        split_ifs at hex
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hex
        obtain ⟨_, _, rfl⟩ := hex
        exact hjmp.elim
      | unreachable =>
        rw [ht] at hex
        simp only [Ctx.exitOf, Option.some.injEq] at hex
        subst hex
        exact hjmp.elim
    · cases hr
      left
      subst hex0
      have hw2 : ∀ {a l : Operand} {ea el : Expr}, reads D' [a, l] = true →
          c.operand depth a = some ea → c.operand depth l = some el →
          [ea, el].mapM (·.eval I ρ) = some hws → ∃ va vl, hws = [va, vl] ∧
            evalWord env' a = pure va ∧ evalWord env' l = pure vl := by
        intro a l ea el hr ha hl hm
        simp only [reads, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hr
        obtain ⟨va, hva, -, hea⟩ := operand_words hcons hρ (by simpa [reads] using hr.1) ha
        obtain ⟨vl, hvl, -, hel⟩ := operand_words hcons hρ (by simpa [reads] using hr.2) hl
        refine ⟨va, vl, by simpa [List.mapM_cons, hva, hvl] using hm.symm, ?_, ?_⟩
        · simp [evalWord, evalInt, hea, Reasoning.Theory.u256_ofNat_toNat]
        · simp [evalWord, evalInt, hel, Reasoning.Theory.u256_ofNat_toNat]
      rcases exitOf_halt hex with ⟨a, l, ea, el, ht, rfl, rfl, hea, hel⟩ |
        ⟨a, l, ea, el, ht, rfl, rfl, hea, hel⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩
      · rw [ht] at hterm
        obtain ⟨va, vl, rfl, hva, hvl⟩ := hw2 hterm hea hel hargs
        obtain ⟨n, s', hxs, ha, hl⟩ := hh
        exact .inr (.inl ⟨n, s', _, w', hxs, by simp [ht, hva, hvl, returnData], ha, hl⟩)
      · rw [ht] at hterm
        obtain ⟨va, vl, rfl, hva, hvl⟩ := hw2 hterm hea hel hargs
        obtain ⟨n, s', hxs⟩ := hh
        exact .inr (.inr ⟨n, s', _, hxs, by simp [ht, hva, hvl, revertData]⟩)
      · simp at hargs; subst hargs
        obtain ⟨n, s', hxs, ha, hl⟩ := hh
        exact .inr (.inl ⟨n, s', _, w', hxs, by simp [ht, stopCall], ha, hl⟩)
      · simp at hargs; subst hargs
        obtain ⟨n, hxs⟩ := hh
        exact .inl ⟨n, _, hxs, .inr (.inr (.inr ⟨rfl, by simp [ht, trap]⟩))⟩
    · cases hr
      exact absurd (exitOf_ret (hex0 ▸ hex)) (by simp [c, Ctx.ofBlock, hret])
    · cases hcl
    · cases hcl

theorem XstepN_pos {D : Array UInt256} {s : State} {x : Except ExecutionException
    (State × Option (HaltCause × ByteArray))} {n : Nat} (h : XstepN D s x n) : 0 < n := by
  cases h <;> omega

/-- The section theorem: from a block's start, the bytes run as the IR's run of the section's
    function goes on from it, at profile `P1`. -/
theorem section_run {code : CodeSection} {low : Lowering} {hint : FuncHint} {f : Func}
    {eb : Block} {I : ExecutionEnv} {tail : ByteArray} {ic : Fe.Sonatina.Ctx}
    (hI : I.code = code.bytecode ++ tail) (hsize : code.bytecode.size < UInt256.size)
    (hsym : ic.symbol = (code.symbols.lookup ·))
    (hbits : (f.blocks.all fun b => b.phis.all (·.ty.bits == 256) &&
        b.body.all (·.dsts.all (·.2.bits == 256))) = true)
    (hnd : nodup (f.blocks.flatMap fun b =>
        b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))) = true)
    {fr : Frame} (hchk : ∀ b ∈ f.blocks, checkBlock code low hint f fr true eb
        (placeIn low hint.name) (zeroRank f (placeIn low hint.name) f.blocks.length) b = .ok ())
    (hpred : ∀ x ∈ f.blocks, eb.id ∉ x.term.succs) (hret : fr.returns = false)
    (hcal : ∀ g, fr.callee g = none) :
    ∀ fuel (b : Block) prev env w st B, st.machineState.gasAvailable.toNat < fuel →
      AtBlock low hint f fr I b prev env w st none B →
      XAgrees (X fuel (D_J I.code 0) st)
        ((pre low eb b >>= fun _ => runBlocks low.machine ic f env prev b.id).exec I w) ∧
      ∀ Q, Invariant.XOk Q fuel (D_J I.code 0) st := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
  intro b
  generalize hr : zeroRank f (placeIn low hint.name) f.blocks.length b.id = r
  induction r using Nat.strong_induction_on generalizing b with
  | _ r ihr =>
  intro prev env w st B hg hat
  rcases block_step hI hsize hsym hbits hnd hchk hpred hret hcal hat with hfin |
    ⟨S, env', w', st', n, B', hreach, hlow, hat', hne, hIR⟩
  · exact ⟨hfin.agrees hg, fun _ => hfin.xOk fuel⟩
  · rw [hIR]
    have hpreS : (pre low eb S >>= fun _ => runBlocks low.machine ic f env' (some b.id) S.id) =
        runBlocks low.machine ic f env' (some b.id) S.id := by
      simp [pre, hne]
    rcases hreach with ⟨rfl, rfl⟩ | hx
    · have := ihr _ (hr ▸ hlow rfl) S rfl (some b.id) env' w' _ B' hg hat'
      rwa [hpreS] at this
    · have hxs := hx.xstepN
      have hn := XstepN_fuel hxs hg
      have hpos := XstepN_pos hxs
      have hg' := XstepN_gas_lt_fuel_of_Xstep_ret_none (f := fuel - n) (D_J I.code 0)
        (by rw [Nat.sub_add_cancel hn]; exact hg) hxs
      have hX := XstepN_X_continue (f := fuel - n) (D_J I.code 0) hxs rfl
      rw [Nat.sub_add_cancel hn] at hX
      obtain ⟨hag, hok⟩ := ihf (fuel - n) (by omega) S (some b.id) env' w' st' B' hg' hat'
      refine ⟨by rw [hX]; rwa [hpreS] at hag, fun Q => ?_⟩
      have h := hx.xOk_cont (hok Q)
      rwa [Nat.sub_add_cancel hn] at h

end Fe.Sonatina.Check
