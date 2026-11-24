import Fe.Sonatina.Steps.Wf
import Fe.Sonatina.Steps.Sim

/-!
# The definedness invariant (design §5.3, review M-1)

Run a well-formed function (`Func.wf`) from its entry, its parameters bound to integers, with
calls by an oracle that returns integers on integers, and take a dominator tree `T` that
`DomTree.valid` accepts.  Then at every block state the run reaches (`BlockInv`), and at every
point of its block (`PointInv`), every value whose definition dominates the point (`DomAt`) is
bound, to an `i256`.  That needs neither the uses' check nor unique definitions: a run binds a
block's phis on entry and each statement's results after it, keeps every binding, and by D1's
edge condition a strict tree ancestor of a block is an ancestor-or-self of the block it was
entered from.  With `ssa f T`, every operand a point uses is such a value or an immediate, so
it evaluates to an `i256` (`defined`): a checker may drop an evaluation of it.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-- An environment of words: each value it binds is an `i256`, below `2 ^ 256`. -/
def EnvW (env : Env) : Prop :=
  ∀ (k : Nat) (v : Val), env[k]? = some v → ∃ n, n < 2 ^ 256 ∧ v = .int 256 n

theorem EnvW.int {env : Env} (h : EnvW env) : EnvInt env := fun k v hv => by
  obtain ⟨n, _, rfl⟩ := h k v hv; rfl

theorem fold_word : ∀ (l : List ((Nat × Ty) × Val)) (env : Env), EnvW env →
    (∀ x ∈ l, x.1.2 = .int 256 ∧ x.2.isInt = true) → EnvW (l.foldl bindStep env)
  | [], _, h, _ => h
  | x :: l, env, h, hl => by
    rw [List.foldl_cons]
    refine fold_word l _ ?_ fun y hy => hl y (List.mem_cons_of_mem _ hy)
    intro k v hv
    unfold bindStep at hv; rw [env_insert_get] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      subst hv
      obtain ⟨hty, hi⟩ := hl x (List.mem_cons_self ..)
      rw [hty]
      revert hi
      cases x.2 with
      | int b n => intro _; exact ⟨n % 2 ^ 256, Nat.mod_lt _ (by positivity), rfl⟩
      | agg => intro hi; cases hi
    · exact h k v hv

/-! ## Dominator trees -/

theorem DomTree.Anc.inv {T : DomTree} {d b : Nat} (h : T.Anc d b) :
    d = b ∨ ∃ i, T.idom.find? b = some i ∧ T.Anc d i := by
  cases h with
  | refl => exact Or.inl rfl
  | step hi ha => exact Or.inr ⟨_, hi, ha⟩

theorem DomTree.valid_entry {T : DomTree} {f : Func} (hv : T.valid f = true) {e : Block}
    (he : f.blocks.head? = some e) :
    (T.reach.find? e.id).isSome = true ∧ T.idom.find? e.id = none := by
  simp only [DomTree.valid, he, Bool.and_eq_true, Option.isNone_iff_eq_none] at hv
  exact ⟨hv.1.1.1.1, hv.1.1.1.2⟩

/-- An edge from a reachable block: its target is reachable, and the entry or a block whose
    immediate dominator is an ancestor-or-self of the edge's source. -/
theorem DomTree.valid_edge {T : DomTree} {f : Func} (hv : T.valid f = true) {p b : Nat}
    (hp : (T.reach.find? p).isSome = true) (hedge : Edge f p b) :
    (T.reach.find? b).isSome = true ∧
      (T.idom.find? b = none ∨ ∃ d, T.idom.find? b = some d ∧ T.Anc d p) := by
  rcases hh : f.blocks.head? with _ | e
  · simp [DomTree.valid, hh] at hv
  have hroot := (DomTree.valid_entry hv hh).2
  simp only [DomTree.valid, hh, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Option.isNone_iff_eq_none, decide_eq_true_eq] at hv
  obtain ⟨⟨_, hblocks⟩, _⟩ := hv
  obtain ⟨blk, hblk, hb⟩ := hedge
  have hmem := List.mem_of_find?_eq_some hblk
  have hid : blk.id = p := by simpa using List.find?_some hblk
  rcases hblocks blk hmem with h | ⟨_, hs⟩
  · rw [hid, hp] at h; cases h
  have := hs b (by rw [hid, succMap_find f p hblk]; exact hb)
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
  refine ⟨this.1, ?_⟩
  rcases this.2 with hbe | hd
  · subst hbe; exact Or.inl hroot
  · right
    cases hi : T.idom.find? b with
    | none => rw [hi] at hd; simp at hd
    | some d => rw [hi, hid] at hd; exact ⟨d, rfl, DomTree.anc_sound hd⟩

/-- An ancestor-or-self of the target of an edge from a reachable block is the target or an
    ancestor-or-self of the source. -/
theorem DomTree.anc_of_edge {T : DomTree} {f : Func} (hv : T.valid f = true) {p b d : Nat}
    (hp : (T.reach.find? p).isSome = true) (hedge : Edge f p b) (ha : T.Anc d b) :
    d = b ∨ T.Anc d p := by
  rcases ha.inv with h | ⟨i, hi, hai⟩
  · exact Or.inl h
  · right
    rcases (DomTree.valid_edge hv hp hedge).2 with h | ⟨i', hi', ha'⟩
    · rw [h] at hi; cases hi
    · rw [hi] at hi'; cases hi'; exact hai.trans ha'

/-! ## The invariant -/

/-- What holds at the point before statement `k` of block `b` (its terminator for `k` the
    statement count): the environment binds words, and every value whose definition dominates
    the point. -/
def PointInv (f : Func) (T : DomTree) (b k : Nat) (env : Env) : Prop :=
  EnvW env ∧ ∀ v, DomAt f T b k v → (env[v]?).isSome = true

/-- What holds at a block state: the environment binds words, and the parameters; the block
    is reachable; entered from nowhere, it has no immediate dominator; entered from `p`, `p` is
    reachable, `p → b` is an edge, and every value defined in an ancestor-or-self of `p` is
    bound. -/
def BlockInv (f : Func) (T : DomTree) (s : BState) : Prop :=
  EnvW s.1 ∧ (∀ p ∈ f.params, (s.1[p.1]?).isSome = true) ∧ (T.reach.find? s.2.2).isSome = true ∧
  match s.2.1 with
  | none => T.idom.find? s.2.2 = none
  | some p => (T.reach.find? p).isSome = true ∧ Edge f p s.2.2 ∧
      ∀ d v, T.Anc d p → DefinedIn f d v → (s.1[v]?).isSome = true

variable {sig : Sigs} {syms : List String} {f : Func} {T : DomTree}

/-- The parameters bound to integers: the entry's block state. -/
theorem entry_inv (hwf : f.wf sig syms = true) (hv : T.valid f = true) {e : Block}
    (he : f.blocks.head? = some e) {args : List Val} (hargs : IntVals args) :
    Returns (fun env => BlockInv f T (env, none, e.id)) (bind {} f.params args) := by
  obtain ⟨hre, hroot⟩ := DomTree.valid_entry hv he
  refine Returns.mono (returns_bind {} f.params args) ?_
  rintro env ⟨hl, rfl⟩
  exact ⟨fold_word _ _ (fun _ _ h => by simp at h) fun x hx =>
      ⟨(Func.wf_words hwf).1 x.1 (List.of_mem_zip hx).1, intVals_iff.mp hargs _ (List.of_mem_zip hx).2⟩,
    fun p hp => fold_binds _ _ _ hl p hp, hre, hroot⟩

/-- Entering a block from a block state: the point before its first statement. -/
theorem point_zero (hwf : f.wf sig syms = true) (hv : T.valid f = true) {env : Env}
    {prev : Option Nat} {b : Nat} (hi : BlockInv f T (env, prev, b)) {blk : Block}
    (hb : f.block? b = some blk) : Returns (PointInv f T b 0) (enter env prev blk) := by
  obtain ⟨hw, hpar, _, hprev⟩ := hi
  have hmem := List.mem_of_find?_eq_some hb
  obtain ⟨hph, _, _⟩ := Func.machine_block (Func.wf_machine hwf) hb
  have htys := ((Func.wf_words hwf).2 blk hmem).1
  refine Returns.mono (returns_enter env prev blk fun phi hphi p hp =>
    returns_evalOperand hw.int (hph phi hphi p hp)) ?_
  rintro env' ⟨vals, hvals, hl, rfl⟩
  refine ⟨fold_word _ _ hw fun x hx => ?_, fun v hdom => ?_⟩
  · obtain ⟨h1, h2⟩ := List.of_mem_zip hx
    obtain ⟨phi, hphi, hx1⟩ := List.mem_map.mp h1
    exact ⟨by rw [← hx1]; exact htys phi hphi, hvals _ h2⟩
  · rcases hdom with hp | ⟨blk', hb', hdef⟩ | ⟨d, hne, ha, hdef⟩
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
      exact fold_keep _ _ _ (hpar p hp')
    · rw [hb] at hb'; cases hb'
      rcases hdef with hphi | ⟨j, hj, _⟩
      · obtain ⟨phi, hphi', rfl⟩ := List.mem_map.mp hphi
        exact fold_binds _ _ _ hl (phi.dst, phi.ty) (List.mem_map_of_mem hphi')
      · exact absurd hj (Nat.not_lt_zero _)
    · refine fold_keep _ _ _ ?_
      cases prev with
      | none =>
        rcases ha.inv with h | ⟨i, hi, _⟩
        · exact absurd h hne
        · simp only at hprev; rw [hprev] at hi; cases hi
      | some p =>
        obtain ⟨hpr, hedge, hdefs⟩ := hprev
        rcases DomTree.anc_of_edge hv hpr hedge ha with h | ha'
        · exact absurd h hne
        · exact hdefs d v ha' hdef

/-- A statement of the block: from the point before it to the point after it. -/
theorem point_succ (hwf : f.wf sig syms = true) {o : Oracle} (hoi : o.IntRet) (c : Ctx)
    {b k : Nat} {blk : Block} (hb : f.block? b = some blk) {s : Stmt} (hs : blk.body[k]? = some s)
    {env : Env} (hpi : PointInv f T b k env) :
    Returns (PointInv f T b (k + 1)) (runBodyO o c env [s]) := by
  obtain ⟨hw, hdom⟩ := hpi
  have hmem := List.mem_of_find?_eq_some hb
  have hsm : s ∈ blk.body := List.mem_of_getElem? hs
  have hm := (Func.machine_block (Func.wf_machine hwf) hb).2.1 s hsm
  have htys := ((Func.wf_words hwf).2 blk hmem).2 s hsm
  simp only [runBodyO]
  refine Returns.bind (returns_runStmtO hoi c hw.int hm) fun vals hv =>
    Returns.bind (returns_bind env s.dsts vals) fun env' ⟨hl, e⟩ => Returns.pure ?_
  subst e
  refine ⟨fold_word _ _ hw fun x hx => ⟨htys x.1 (List.of_mem_zip hx).1,
    intVals_iff.mp hv _ (List.of_mem_zip hx).2⟩, fun v hd => ?_⟩
  rcases hd with hp | ⟨blk', hb', hphi | ⟨j, hj, s', hs', hv'⟩⟩ | hanc
  · exact fold_keep _ _ _ (hdom v (Or.inl hp))
  · exact fold_keep _ _ _ (hdom v (Or.inr (Or.inl ⟨blk', hb', Or.inl hphi⟩)))
  · by_cases hjk : j < k
    · exact fold_keep _ _ _ (hdom v (Or.inr (Or.inl ⟨blk', hb', Or.inr ⟨j, hjk, s', hs', hv'⟩⟩)))
    · have hjk' : j = k := by omega
      subst hjk'
      rw [hb] at hb'; cases hb'
      rw [hs] at hs'; cases hs'
      obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
      exact fold_binds _ _ _ hl dd hdd
  · exact fold_keep _ _ _ (hdom v (Or.inr (Or.inr hanc)))

theorem runBodyO_append (o : Oracle) (c : Ctx) :
    ∀ (l₁ l₂ : List Stmt) (env : Env),
      runBodyO o c env (l₁ ++ l₂) = runBodyO o c env l₁ >>= fun env' => runBodyO o c env' l₂
  | [], l₂, env => by simp only [List.nil_append, runBodyO, pure_bind]
  | s :: l₁, l₂, env => by
    simp only [List.cons_append, runBodyO, bind_assoc, runBodyO_append o c l₁ l₂]

/-- The block's first `k` statements: from the point before the first to the point `k`. -/
theorem point_take (hwf : f.wf sig syms = true) {o : Oracle} (hoi : o.IntRet) (c : Ctx)
    {b : Nat} {blk : Block} (hb : f.block? b = some blk) {env₁ : Env}
    (h₀ : PointInv f T b 0 env₁) :
    ∀ k, k ≤ blk.body.length → Returns (PointInv f T b k) (runBodyO o c env₁ (blk.body.take k))
  | 0, _ => by simp only [List.take_zero, runBodyO]; exact Returns.pure h₀
  | k + 1, hk => by
    have hlt : k < blk.body.length := by omega
    have hs : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hs, Option.toList_some, runBodyO_append]
    exact Returns.bind (point_take hwf hoi c hb h₀ k (by omega)) fun env hpi =>
      point_succ hwf hoi c hb hs hpi

/-- From a block state, the point before statement `k` of its block. -/
theorem block_point (hwf : f.wf sig syms = true) (hv : T.valid f = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {env : Env} {prev : Option Nat} {b : Nat}
    (hi : BlockInv f T (env, prev, b)) {blk : Block} (hb : f.block? b = some blk) (k : Nat)
    (hk : k ≤ blk.body.length) :
    Returns (PointInv f T b k) (enter env prev blk >>= fun env₁ => runBodyO o c env₁ (blk.body.take k)) :=
  Returns.bind (point_zero hwf hv hi hb) fun _ h₀ => point_take hwf hoi c hb h₀ k hk

/-- The block state a block goes to. -/
def NextInv (f : Func) (T : DomTree) (b : Nat) : Next → Prop
  | .goto env d => BlockInv f T (env, some b, d)
  | .done _ => True

/-- The block of a block state goes to a block state. -/
theorem stepBlock_inv (hwf : f.wf sig syms = true) (hv : T.valid f = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {s : BState} (hi : BlockInv f T s) :
    Returns (NextInv f T s.2.2) (stepBlock o c f s.1 s.2.1 s.2.2) := by
  obtain ⟨env, prev, b⟩ := s
  have hreach : (T.reach.find? b).isSome = true := hi.2.2.1
  unfold stepBlock
  cases hb : f.block? b with
  | none => exact Returns.stuck _
  | some blk =>
    have hterm := (Func.machine_block (Func.wf_machine hwf) hb).2.2
    refine Returns.bind (point_zero hwf hv hi hb) fun env₁ h₀ => ?_
    have hbody := point_take hwf hoi c hb h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    refine Returns.bind hbody fun env₂ hpi => ?_
    refine Returns.mono (returns_runTerm hpi.1.int blk.term hterm) fun n hn => ?_
    cases n with
    | done _ => trivial
    | goto env' d =>
      obtain ⟨rfl, hd⟩ := hn
      obtain ⟨hw, hdom⟩ := hpi
      have hedge : Edge f b d := ⟨blk, hb, hd⟩
      refine ⟨hw, fun p hp => hdom p.1 (Or.inl (List.mem_map_of_mem hp)),
        (DomTree.valid_edge hv hreach hedge).1, hreach, hedge, fun d' v ha hdef => ?_⟩
      by_cases hdb : d' = b
      · subst hdb
        obtain ⟨blk', hb', hdef'⟩ := hdef
        rw [hb] at hb'; cases hb'
        rcases hdef' with hphi | ⟨s, hs, hvs⟩
        · exact hdom v (Or.inr (Or.inl ⟨blk, hb, Or.inl hphi⟩))
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
          obtain ⟨hjl, _⟩ := List.getElem?_eq_some_iff.mp hj
          exact hdom v (Or.inr (Or.inl ⟨blk, hb, Or.inr ⟨j, hjl, s, hj, hvs⟩⟩))
      · exact hdom v (Or.inr (Or.inr ⟨d', hdb, ha, hdef⟩))

/-- The block states a run of `f` from `s₀` reaches, calls by `o`: each next one is where a
    block of the previous one goes. -/
inductive Reaches (o : Oracle) (c : Ctx) (f : Func) (s₀ : BState) : BState → Prop
  | start : Reaches o c f s₀ s₀
  | step {s : BState} {I : ExecutionEnv} {w w' : World} {env : Env} {d : Nat} :
      Reaches o c f s₀ s →
      (stepBlock o c f s.1 s.2.1 s.2.2).exec I w = some (.ok (.goto env d, w')) →
      Reaches o c f s₀ (env, some s.2.2, d)

theorem reaches_inv (hwf : f.wf sig syms = true) (hv : T.valid f = true) {o : Oracle}
    (hoi : o.IntRet) (c : Ctx) {s₀ s : BState} (hr : Reaches o c f s₀ s)
    (h₀ : BlockInv f T s₀) : BlockInv f T s := by
  induction hr with
  | start => exact h₀
  | step _ hx ih => exact stepBlock_inv hwf hv hoi c ih _ _ _ _ hx

/-! ## Uses -/

theorem intVal_of_wf {env : Env} (hw : EnvW env) {op : Operand} (hop : op.wf = true)
    (hb : ∀ v, op = .var v → (env[v]?).isSome = true) : ∃ n, intVal env op = some (256, n) := by
  cases op with
  | var v =>
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (hb v rfl)
    obtain ⟨n, _, rfl⟩ := hw v val hval
    exact ⟨n, by simp only [intVal, opVal, hval]⟩
  | imm bits n =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq] at hop
    obtain ⟨rfl, _⟩ := hop
    exact ⟨n, rfl⟩
  | undef => simp [Operand.wf] at hop

/-- The operands the point before statement `k` uses: statement `k`'s, or the terminator's for
    `k` the statement count. -/
def usesAt (blk : Block) (k : Nat) : List Operand :=
  match blk.body[k]? with
  | some s => s.inst.args
  | none => blk.term.args

/-- At a point of a reachable block, every operand the point uses is a word. -/
theorem uses_defined (hwf : f.wf sig syms = true) (hs : ssa f T = true) {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) (hr : (T.reach.find? b).isSome = true) {k : Nat}
    (hk : k ≤ blk.body.length) {env : Env} (hpi : PointInv f T b k env) :
    ∀ op ∈ usesAt blk k, ∃ n, intVal env op = some (256, n) := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have hn := Func.wf_ids hwf
  obtain ⟨_, hops, hterm⟩ := Func.wf_operands hwf hmem
  obtain ⟨_, hbody, hterm'⟩ := ssa_block hs hmem (hid ▸ hr)
  intro op hop
  unfold usesAt at hop
  split at hop
  · next s hks =>
    refine intVal_of_wf hpi.1 (hops s (List.mem_of_getElem? hks) op hop) fun v e => ?_
    subst e
    have := useOk_sound hn (hbody k s hks _ hop)
    rw [hid] at this
    exact hpi.2 v this
  · next hks =>
    have hkl : k = blk.body.length := by
      have := List.getElem?_eq_none_iff.mp hks; omega
    subst hkl
    refine intVal_of_wf hpi.1 (hterm op hop) fun v e => ?_
    subst e
    have := useOk_sound hn (hterm' _ hop)
    rw [hid] at this
    exact hpi.2 v this

/-- At the terminator of a reachable block, every operand it reads is a word. -/
theorem term_defined (hwf : f.wf sig syms = true) (hs : ssa f T = true) {b : Nat} {blk : Block}
    (hb : f.block? b = some blk) (hr : (T.reach.find? b).isSome = true) {env : Env}
    (hpi : PointInv f T b blk.body.length env) :
    ∀ op ∈ blk.term.args, ∃ n, intVal env op = some (256, n) := by
  intro op hop
  refine uses_defined hwf hs hb hr le_rfl hpi op ?_
  unfold usesAt
  rw [List.getElem?_eq_none le_rfl]
  exact hop

/-- Entering a reachable block from `p`, every operand its phis take from `p` is a word. -/
theorem phis_defined (hwf : f.wf sig syms = true) (hs : ssa f T = true) {env : Env} {p b : Nat}
    (hi : BlockInv f T (env, some p, b)) {blk : Block} (hb : f.block? b = some blk) :
    ∀ phi ∈ blk.phis, ∀ op ∈ phi.incoming, op.2 = p → ∃ n, intVal env op.1 = some (256, n) := by
  obtain ⟨hw, hpar, hr, hpr, _, hdefs⟩ := hi
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨hops, _, _⟩ := Func.wf_operands hwf hmem
  obtain ⟨hphis, _, _⟩ := ssa_block hs hmem (hid ▸ hr)
  intro phi hphi op hop hp
  subst hp
  refine intVal_of_wf hw (hops phi hphi op hop) fun v e => ?_
  have hu := hphis phi hphi op hop hpr
  rw [e] at hu
  rcases phiUseOk_sound (Func.wf_ids hwf) hu with hv | ⟨d, ha, hdef⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    exact hpar q hq
  · exact hdefs d v ha hdef

/-- The definedness invariant.  Run a well-formed function in SSA form on a valid dominator
    tree from its entry, its parameters bound to integers, with calls by an oracle that returns
    integers on integers.  At every block state the run reaches, and at every point `(b, k)` of
    its block, every value whose definition dominates the point is bound to an `i256`, and every
    operand the point uses evaluates to one. -/
theorem defined (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {o : Oracle} (hoi : o.IntRet) (c : Ctx) {e : Block} (he : f.blocks.head? = some e)
    {args : List Val} (hargs : IntVals args) {I : ExecutionEnv} {w w₀ : World} {env₀ : Env}
    (h₀ : (bind {} f.params args).exec I w = some (.ok (env₀, w₀)))
    {s : BState} (hr : Reaches o c f (env₀, none, e.id) s) {blk : Block}
    (hb : f.block? s.2.2 = some blk) {k : Nat} (hk : k ≤ blk.body.length) :
    Returns (fun env => (∀ v, DomAt f T s.2.2 k v → ∃ n, env[v]? = some (.int 256 n)) ∧
        ∀ op ∈ usesAt blk k, ∃ n, evalInt env op = pure (256, n))
      (enter s.1 s.2.1 blk >>= fun env₁ => runBodyO o c env₁ (blk.body.take k)) := by
  have hi := reaches_inv hwf hv hoi c hr (entry_inv hwf hv he hargs I w env₀ w₀ h₀)
  refine Returns.mono (block_point hwf hv hoi c hi hb k hk) fun env hpi =>
    ⟨fun v hd => ?_, fun op hop => ?_⟩
  · obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (hpi.2 v hd)
    obtain ⟨n, _, rfl⟩ := hpi.1 v val hval
    exact ⟨n, hval⟩
  · obtain ⟨n, hn⟩ := uses_defined hwf hs hb hi.2.2.1 hk hpi op hop
    exact ⟨n, by rw [evalInt_eq, hn]; rfl⟩

end Fe.Sonatina.Steps
