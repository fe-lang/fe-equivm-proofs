import Fe.Sonatina.Steps.Run

/-!
# L2: a pure definition holds wherever it is in scope (design §5.3, review M-1, ruling R-11.2)

Run a well-formed function in strict SSA on a valid dominator tree from its entry, its
parameters bound to integers, with calls by an oracle that returns integers on integers.  At
every point `(b, k)` of every block state the run reaches (`l2`), each statement `s` of a block
the tree reaches whose instruction is pure (`Inst.pure`: its values are a function of its
operands' values, `pureVals`, `runInst_pure`) and that comes before the point (`Before`: in a
strict tree ancestor of `b`, or earlier in `b`) has its results bound to the instruction's values
on the current environment, as their types (`Val.as`, as `bind` binds them) (`PureInv`).
`evm_add_mod` and `evm_mul_mod` count as pure: total and without effects in the model.

The argument: a statement's results are bound only by it (unique definitions); its operands'
definitions come before it (`ssa`'s uses), so an operand is rebound only where the statement
is out of scope, by D1's edge condition and the tree's antisymmetry.  The preservation lemmas
(`pureInv_enter`, `pureInv_stmt`, `pureInv_take`, `pureInv_step`) serve simulations that walk the
input themselves.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-- `evm_add_mod` and `evm_mul_mod`: total and without effects (a modulus `0` gives `0`). -/
def _root_.Fe.Sonatina.EvmOp.isMod : EvmOp → Bool
  | .addMod | .mulMod => true
  | _ => false

/-- An instruction whose values are a function of its operands' values. -/
def _root_.Fe.Sonatina.Inst.pure : Inst → Bool
  | .bin .. | .cmp .. | .isZero _ | .not _ | .neg _ | .ctz _ | .ovf .. | .cast .. | .select .. => true
  | .evm op args => op.isMod && args.length == 3
  | _ => false

/-- The value of `evm_add_mod` or `evm_mul_mod` on its operands' integers. -/
def modVals : EvmOp → List (Option (Nat × Nat)) → Option (List Val)
  | .addMod, [some (_, x), some (_, y), some (_, z)] =>
    some [word (UInt256.addMod (.ofNat x) (.ofNat y) (.ofNat z))]
  | .mulMod, [some (_, x), some (_, y), some (_, z)] =>
    some [word (UInt256.mulMod (.ofNat x) (.ofNat y) (.ofNat z))]
  | _, _ => none

/-- Two integer operands of one width. -/
def pairOpt (env : Env) (a b : Operand) : Option (Nat × Nat × Nat) := do
  let (bits, x) ← intVal env a
  let (bits', y) ← intVal env b
  if bits == bits' then some (bits, x, y) else none

theorem evalPair_opt (env : Env) (a b : Operand) : evalPair env a b = lift (pairOpt env a b) :=
  pairVal_eq env a b

/-- The values a pure instruction gives on the operands' values in `env`. -/
def pureVals (env : Env) : Inst → Option (List Val)
  | .bin op a b => (pairOpt env a b).map fun (bits, x, y) => [.int bits (op.eval bits x y)]
  | .cmp op a b => (pairOpt env a b).map fun (bits, x, y) => [bool (op.eval bits x y)]
  | .isZero a => (intVal env a).map fun p => [bool (p.2 == 0)]
  | .not a => (intVal env a).map fun (bits, x) => [.int bits (2 ^ bits - 1 - x)]
  | .neg a => (intVal env a).map fun (bits, x) => [.int bits (wrap bits (-(x : Int)))]
  | .ctz a => (intVal env a).map fun (bits, x) =>
      [.int bits (((List.range bits).find? x.testBit).getD bits)]
  | .ovf op a b => (pairOpt env a b).map fun (bits, x, y) => match op.eval bits x y with
      | (r, o) => [.int bits r, bool o]
  | .cast op a ty => (intVal env a).map fun (bits, x) => [.int ty.bits (op.eval bits x ty.bits)]
  | .select c a b => (intVal env c).bind fun (_, v) =>
      (opVal env (if v != 0 then a else b)).map fun x => [x]
  | .evm op args => modVals op (args.map (intVal env))
  | _ => none

/-- A pure instruction runs to its values, or is stuck. -/
theorem runInst_pure (c : Ctx) (env : Env) (i : Inst) (h : i.pure = true) :
    runInst c env i = lift (pureVals env i) := by
  cases i <;> simp only [Inst.pure, Bool.false_eq_true] at h
  case evm op args =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hop, hl⟩ := h
    match args, hl with
    | [a, b, m], _ =>
      simp only [runInst, pureVals, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
        evalWord, evalInt_eq]
      cases op <;> simp only [EvmOp.isMod, Bool.false_eq_true] at hop <;>
        rcases intVal env a with _ | ⟨_, x⟩ <;> rcases intVal env b with _ | ⟨_, y⟩ <;>
        rcases intVal env m with _ | ⟨_, z⟩ <;> rfl
  case bin op a b =>
    simp only [runInst, pureVals]; rw [evalPair_opt, lift_bind]
    rcases pairOpt env a b with _ | ⟨bits, x, y⟩ <;> rfl
  case cmp op a b =>
    simp only [runInst, pureVals]; rw [evalPair_opt, lift_bind]
    rcases pairOpt env a b with _ | ⟨bits, x, y⟩ <;> rfl
  case ovf op a b =>
    simp only [runInst, pureVals]; rw [evalPair_opt, lift_bind]
    rcases pairOpt env a b with _ | ⟨bits, x, y⟩ <;> rfl
  case select c a b =>
    simp only [runInst, pureVals]; rw [evalInt_eq, lift_bind]
    rcases intVal env c with _ | ⟨bits, v⟩
    · rfl
    · simp only [Option.bind_some]
      rw [evalOperand_eq, lift_bind]
      rcases opVal env (if v != 0 then a else b) with _ | x <;> rfl
  case cast op a ty =>
    simp only [runInst, pureVals]; rw [evalInt_eq, lift_bind]
    rcases intVal env a with _ | ⟨bits, x⟩ <;> rfl
  all_goals
    simp only [runInst, pureVals]; rw [evalInt_eq, lift_bind]
    rename_i a
    rcases intVal env a with _ | ⟨bits, x⟩ <;> rfl

/-- The values depend only on the operands'. -/
theorem pureVals_congr {env' env : Env} (i : Inst) (h : ∀ o ∈ i.args, opVal env' o = opVal env o) :
    pureVals env' i = pureVals env i := by
  have hi : ∀ o ∈ i.args, intVal env' o = intVal env o := fun o ho => by
    unfold intVal; rw [h o ho]
  cases i
  case evm op args =>
    simp only [Inst.args] at hi
    simp only [pureVals, List.map_congr_left hi]
  case select c a b =>
    simp only [Inst.args, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
      List.not_mem_nil, or_false] at h hi
    simp only [pureVals, hi.1]
    rcases intVal env c with _ | ⟨bits, v⟩
    · rfl
    · simp only [Option.bind_some]
      split
      · rw [h.2.1]
      · rw [h.2.2]
  all_goals simp only [Inst.args, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
    List.not_mem_nil, or_false, IsEmpty.forall_iff, implies_true] at hi
  all_goals simp only [pureVals, pairOpt, hi]

/-! ## The invariant -/

/-- Statement `j` of block `d` comes before the point `(b, k)`: `d` is a strict tree ancestor of
    `b`, or `d` is `b` and `j < k`. -/
def Before (T : DomTree) (d j b k : Nat) : Prop := (d ≠ b ∧ T.Anc d b) ∨ (d = b ∧ j < k)

/-- The results of statement `s` are bound to its pure instruction's values on `env`. -/
def PureHolds (env : Env) (s : Stmt) : Prop :=
  ∃ vals, pureVals env s.inst = some vals ∧ s.dsts.length = vals.length ∧
    ∀ x ∈ s.dsts.zip vals, env[x.1.1]? = some (x.2.as x.1.2)

/-- L2 at the point `(b, k)`: every pure statement of a block the tree reaches that comes before
    the point holds. -/
def PureInv (f : Func) (T : DomTree) (b k : Nat) (env : Env) : Prop :=
  ∀ d j blk s, f.block? d = some blk → blk.body[j]? = some s → s.inst.pure = true →
    (T.reach.find? d).isSome = true → Before T d j b k → PureHolds env s

/-- L2 at a block state: at the end of the block entered from. -/
def BlockPure (f : Func) (T : DomTree) (s : BState) : Prop :=
  match s.2.1 with
  | none => True
  | some p => ∀ pblk, f.block? p = some pblk → PureInv f T p pblk.body.length s.1

variable {sig : Sigs} {syms : List String} {f : Func} {T : DomTree}

/-- A binding that binds neither a statement's results nor its operands keeps it. -/
theorem pureHolds_keep {env : Env} {s : Stmt} (h : PureHolds env s) (l : List ((Nat × Ty) × Val))
    (hd : ∀ x ∈ s.dsts, x.1 ∉ l.map (·.1.1))
    (ho : ∀ w, Operand.var w ∈ s.inst.args → w ∉ l.map (·.1.1)) :
    PureHolds (l.foldl bindStep env) s := by
  obtain ⟨vals, hv, hl, hb⟩ := h
  refine ⟨vals, ?_, hl, fun x hx => ?_⟩
  · rw [pureVals_congr _ fun o hop => ?_, hv]
    cases o with
    | var w => exact fold_get_not _ _ _ (ho w hop)
    | imm => rfl
  · rw [fold_get_not _ _ _ (hd x.1 (List.of_mem_zip hx).1)]; exact hb x hx

/-- An operand of a statement of a reachable block, as `ssa` checks it: a value whose definition
    dominates the statement. -/
theorem stmt_operand (hwf : f.wf sig syms = true) (hs : ssa f T = true) {d j : Nat} {blk : Block}
    (hb : f.block? d = some blk) (hr : (T.reach.find? d).isSome = true) {s : Stmt}
    (hsj : blk.body[j]? = some s) {w : Nat} (hw : Operand.var w ∈ s.inst.args) :
    DomAt f T d j w := by
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = d := by simpa using List.find?_some hb
  have := (ssa_block hs hmem (hid ▸ hr)).2.1 j s hsj _ hw
  rw [hid] at this
  exact useOk_sound (Func.wf_ids hwf) this

/-- Entering a block keeps L2: statements before the block's start are before the predecessor's
    end, and the phis bind none of their results or operands. -/
theorem pureInv_enter (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {env : Env} {prev : Option Nat} {b : Nat} (hi : BlockInv f T (env, prev, b))
    (hp : BlockPure f T (env, prev, b)) {blk : Block} (hb : f.block? b = some blk) :
    Returns (PureInv f T b 0) (enter env prev blk) := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  rw [enter_eq]
  refine Returns.lift fun e₁ he₁ => ?_
  intro d j dblk s hdb hsj hpure hdr hbef
  rcases hbef with ⟨hne, ha⟩ | ⟨_, hj⟩
  swap
  · exact absurd hj (Nat.not_lt_zero _)
  obtain ⟨hw, _, hr, hprev⟩ := hi
  cases prev with
  | none =>
    rcases ha.inv with h | ⟨i, hi, _⟩
    · exact absurd h hne
    · simp only at hprev; rw [hprev] at hi; cases hi
  | some p =>
    obtain ⟨hpr, hedge, _⟩ := hprev
    have hdp : d = b ∨ T.Anc d p := DomTree.anc_of_edge hv hpr hedge ha
    have hdp := hdp.resolve_left hne
    obtain ⟨pblk, hpb, _⟩ := hedge
    have hold : PureHolds env s := by
      refine hp pblk hpb d j dblk s hdb hsj hpure hdr ?_
      by_cases hdeq : d = p
      · subst hdeq
        rw [hpb] at hdb; cases hdb
        exact Or.inr ⟨rfl, (List.getElem?_eq_some_iff.mp hsj).1⟩
      · exact Or.inl ⟨hdeq, hdp⟩
    obtain ⟨vals, _, hlen, rfl⟩ := enterOpt_spec he₁
    have hkeys := enter_keys hlen
    have hdmem := List.mem_of_find?_eq_some hdb
    have hdid : dblk.id = d := by simpa using List.find?_some hdb
    obtain ⟨e, _⟩ : ∃ e, f.blocks.head? = some e := by
      cases h : f.blocks.head? with
      | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
      | some e => exact ⟨e, rfl⟩
    rename_i he
    have hroot := (DomTree.valid_entry hv he).2
    have hbroot : T.Anc e.id b := hid ▸ DomTree.valid_root hv he hmem (hid ▸ hr)
    -- a phi of `b` is no result and no operand of `s`
    have hphi : ∀ w, w ∈ blk.phis.map (·.dst) → (w, Def.phi b) ∈ defList f := fun w hw' => by
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hw'
      exact hid ▸ phi_def hmem hφ
    refine pureHolds_keep hold _ (fun x hx hk => ?_) (fun w hw' hk => ?_)
    · rw [hkeys] at hk
      cases hU.fn (hdid ▸ stmt_def hdmem hsj hx) (hphi _ hk)
    · rw [hkeys] at hk
      have hpw := hphi w hk
      rcases stmt_operand hwf hs hdb hdr hsj hw' with hpar | ⟨blk', hb', hph | ⟨j', _, s', hs', hv'⟩⟩ |
        ⟨d', hne', ha', hdef⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpar
        cases hU.fn (param_def hq) hpw
      · rw [hdb] at hb'; cases hb'
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
        exact hne (Def.phi.inj (hU.fn (hdid ▸ phi_def hdmem hφ) hpw))
      · rw [hdb] at hb'; cases hb'
        obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
        cases hU.fn (hdid ▸ stmt_def hdmem hs' hdd) hpw
      · have := phi_of_definedIn hU hdef hpw
        subst this
        exact hne (DomTree.anc_antisymm hroot hbroot ha ha')

/-- A statement keeps L2, and adds itself if pure. -/
theorem pureInv_stmt (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {b k : Nat} {blk : Block} (hb : f.block? b = some blk) (hr : (T.reach.find? b).isSome = true)
    {s : Stmt} (hsk : blk.body[k]? = some s) {env : Env} (hpi : PureInv f T b k env)
    {vals : List Val} (hvals : s.inst.pure = true → pureVals env s.inst = some vals)
    (hl : s.dsts.length = vals.length) :
    PureInv f T b (k + 1) ((s.dsts.zip vals).foldl bindStep env) := by
  have hU := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  obtain ⟨e, he⟩ : ∃ e, f.blocks.head? = some e := by
    cases h : f.blocks.head? with
    | none => rw [List.head?_eq_none_iff] at h; rw [h] at hmem; cases hmem
    | some e => exact ⟨e, rfl⟩
  have hroot := (DomTree.valid_entry hv he).2
  have hbroot : T.Anc e.id b := hid ▸ DomTree.valid_root hv he hmem (hid ▸ hr)
  have hkeys : ((s.dsts.zip vals).map (·.1.1)) = s.dsts.map (·.1) := by
    have h1 : (s.dsts.zip vals).map Prod.fst = s.dsts := List.map_fst_zip (by omega)
    calc (s.dsts.zip vals).map (·.1.1) = ((s.dsts.zip vals).map Prod.fst).map (·.1) := by
          rw [List.map_map]; rfl
      _ = s.dsts.map (·.1) := by rw [h1]
  -- a key the statement binds is defined by it
  have hkey : ∀ w, w ∈ (s.dsts.zip vals).map (·.1.1) → (w, Def.stmt b k) ∈ defList f := by
    intro w hw
    rw [hkeys] at hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact hid ▸ stmt_def hmem hsk hx
  intro d j dblk s' hdb hsj hpure hdr hbef
  have hdmem := List.mem_of_find?_eq_some hdb
  have hdid : dblk.id = d := by simpa using List.find?_some hdb
  by_cases hnew : d = b ∧ j = k
  · obtain ⟨rfl, rfl⟩ := hnew
    rw [hb] at hdb; cases hdb
    rw [hsk] at hsj; cases hsj
    have hvs := hvals hpure
    refine ⟨vals, ?_, hl, fun x hx => fold_get_mem _ _ ?_ x hx⟩
    · rw [pureVals_congr _ fun o hop => ?_, hvs]
      cases o with
      | var w =>
        refine fold_get_not _ _ _ fun hw => ?_
        have hwd := hkey w hw
        rcases stmt_operand hwf hs hb hr hsk hop with hpar | ⟨blk', hb', hph | ⟨j', hj', s', hs', hv'⟩⟩ |
          ⟨d', hne', _, hdef⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpar
          cases hU.fn (param_def hq) hwd
        · rw [hb] at hb'; cases hb'
          obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
          cases hU.fn (hid ▸ phi_def hmem hφ) hwd
        · rw [hb] at hb'; cases hb'
          obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
          have := hU.fn (hid ▸ stmt_def hmem hs' hdd) hwd
          simp only [Def.stmt.injEq] at this
          omega
        · rcases definedIn_def hdef with h | ⟨j'', h⟩
          · cases hU.fn h hwd
          · exact hne' (Def.stmt.inj (hU.fn h hwd)).1
      | imm => rfl
    · rw [hkeys]; exact hU.dsts hmem hsk
  · have hbef' : Before T d j b k := by
      rcases hbef with h | ⟨rfl, hj⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by omega⟩
    refine pureHolds_keep (hpi d j dblk s' hdb hsj hpure hdr hbef') _ (fun x hx hk => ?_)
      fun w hw hk => ?_
    · have := hU.fn (hdid ▸ stmt_def hdmem hsj hx) (hkey _ hk)
      simp only [Def.stmt.injEq] at this
      exact hnew this
    · have hwd := hkey w hk
      rcases stmt_operand hwf hs hdb hdr hsj hw with hpar | ⟨blk', hb', hph | ⟨j', hj', s'', hs'', hv'⟩⟩ |
        ⟨d', hne', ha', hdef⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpar
        cases hU.fn (param_def hq) hwd
      · rw [hdb] at hb'; cases hb'
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hph
        cases hU.fn (hdid ▸ phi_def hdmem hφ) hwd
      · rw [hdb] at hb'; cases hb'
        obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hv'
        have := hU.fn (hdid ▸ stmt_def hdmem hs'' hdd) hwd
        simp only [Def.stmt.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        rcases hbef' with ⟨hne, _⟩ | ⟨_, hj⟩
        · exact hne rfl
        · omega
      · rcases definedIn_def hdef with h | ⟨j'', h⟩
        · cases hU.fn h hwd
        · have := (Def.stmt.inj (hU.fn h hwd)).1
          subst this
          rcases hbef' with ⟨hne, ha⟩ | ⟨rfl, _⟩
          · exact hne (DomTree.anc_antisymm hroot hbroot ha ha')
          · exact hne' rfl

/-- What one statement returns: integers, and its pure instruction's values. -/
theorem returns_runStmtO_pure {o : Oracle} (hoi : o.IntRet) (c : Ctx) {env : Env} (h : EnvInt env)
    {s : Stmt} (hs : s.inst.machine = true) :
    Returns (fun vals => IntVals vals ∧ (s.inst.pure = true → pureVals env s.inst = some vals))
      (runStmtO o c env s) := by
  refine Returns.and (returns_runStmtO hoi c h hs) ?_
  by_cases hp : s.inst.pure = true
  · have hrun : runStmtO o c env s = runInst c env s.inst := by
      unfold runStmtO
      split
      · next heq => rw [heq] at hp; simp [Inst.pure] at hp
      · rfl
    rw [hrun, runInst_pure c env _ hp]
    exact Returns.lift fun vals hv _ => hv
  · intro _ _ _ _ _ h; exact absurd h hp

/-- The block's first `k` statements keep the definedness invariant and L2. -/
theorem pureInv_take (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {o : Oracle} (hoi : o.IntRet) (c : Ctx) {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (hr : (T.reach.find? b).isSome = true) {env₁ : Env}
    (h₀ : PointInv f T b 0 env₁ ∧ PureInv f T b 0 env₁) :
    ∀ k, k ≤ blk.body.length → Returns (fun env => PointInv f T b k env ∧ PureInv f T b k env)
      (runBodyO o c env₁ (blk.body.take k))
  | 0, _ => by simp only [List.take_zero, runBodyO]; exact Returns.pure h₀
  | k + 1, hk => by
    have hlt : k < blk.body.length := by omega
    have hsk : blk.body[k]? = some blk.body[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hsk, Option.toList_some, runBodyO_append]
    refine Returns.bind (pureInv_take hwf hv hs hoi c hb hr h₀ k (by omega)) fun env ⟨hpi, hpu⟩ => ?_
    have hm := Func.machine_block (Func.wf_machine hwf) hb _ (List.mem_of_getElem? hsk)
    simp only [runBodyO]
    refine Returns.bind (returns_runStmtO_pure hoi c hpi.1.int hm) fun vals ⟨hiv, hpv⟩ =>
      Returns.bind (returns_bind env _ vals) fun env₂ ⟨hl, he⟩ => Returns.pure ?_
    subst he
    exact ⟨point_succ' hwf hb hsk hpi hiv hl, pureInv_stmt hwf hv hs hb hr hsk hpu hpv hl⟩

/-- A block goes to a block state where L2 holds at its end. -/
theorem pureInv_step (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {o : Oracle} (hoi : o.IntRet) (c : Ctx) {s : BState} (hi : BlockInv f T s)
    (hp : BlockPure f T s) :
    Returns (fun n => match n with
      | .goto env _ => ∀ blk, f.block? s.2.2 = some blk → PureInv f T s.2.2 blk.body.length env
      | .done _ => True) (stepBlock o c f s.1 s.2.1 s.2.2) := by
  obtain ⟨env, prev, b⟩ := s
  unfold stepBlock
  cases hb : f.block? b with
  | none => exact Returns.stuck _
  | some blk =>
    dsimp only
    refine Returns.bind (Returns.and (point_zero hwf hv hi hb) (pureInv_enter hwf hv hs hi hp hb))
      fun env₁ h₀ => ?_
    have hbody := pureInv_take hwf hv hs hoi c hb hi.2.2.1 h₀ blk.body.length le_rfl
    rw [List.take_length] at hbody
    refine Returns.bind hbody fun env₂ ⟨hpi, hpu⟩ => ?_
    refine Returns.mono (returns_runTerm hpi.1.int blk.term) fun n hn => ?_
    cases n with
    | goto env' d =>
      obtain ⟨rfl, _⟩ := hn
      intro blk' hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      exact hpu
    | done _ => trivial

/-- L2 on the run from the entry: at every point of every block state the run reaches, every pure
    statement of a reachable block before the point holds. -/
theorem l2 (hwf : f.wf sig syms = true) (hv : T.valid f = true) (hs : ssa f T = true)
    {o : Oracle} (hoi : o.IntRet) (c : Ctx) {e : Block} (he : f.blocks.head? = some e)
    {args : List Val} (hargs : IntVals args) {I : ExecutionEnv} {w w₀ : World} {env₀ : Env}
    (h₀ : (bind {} f.params args).exec I w = some (.ok (env₀, w₀)))
    {s : BState} (hr : Reaches o c f (env₀, none, e.id) s) {blk : Block}
    (hb : f.block? s.2.2 = some blk) {k : Nat} (hk : k ≤ blk.body.length) :
    Returns (PureInv f T s.2.2 k)
      (enter s.1 s.2.1 blk >>= fun env₁ => runBodyO o c env₁ (blk.body.take k)) := by
  have hinv : BlockInv f T s ∧ BlockPure f T s := by
    clear hb hk
    induction hr with
    | start => exact ⟨entry_inv hwf hv he hargs I w env₀ w₀ h₀, trivial⟩
    | step _ hx ih =>
      exact ⟨stepBlock_inv hwf hv hoi c ih.1 _ _ _ _ hx,
        pureInv_step hwf hv hs hoi c ih.1 ih.2 _ _ _ _ hx⟩
  refine Returns.bind (Returns.and (point_zero hwf hv hinv.1 hb)
    (pureInv_enter hwf hv hs hinv.1 hinv.2 hb)) fun env₁ h₀' => ?_
  exact Returns.mono (pureInv_take hwf hv hs hoi c hb hinv.1.2.2.1 h₀' k hk) fun _ h => h.2

end Fe.Sonatina.Steps
