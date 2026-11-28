import Fe.Sonatina.Stage3.Place.Inv
import Fe.Sonatina.Stage3.Place.Rules

/-!
# The machine side of a template, and the frame relation across a statement

A source statement other than a call is lowered to machine statements that call nothing
(`Place/Lower.lean`, `stmt`); the simulation runs them by `runPlain`, the machine IR's run of
call-free statements (`runInst` and `bind`, as `runBodyG` runs them under the guard that protects
nothing).  This file gives:

- `mval_eval`: an operand with a word evaluates to it; `runPlain_cons_bin` and the like: the run
  of one statement of the shape `take1` matches;
- `envRel_step`: the frame relation after a statement, from the one before, the statement's
  results related, and the machine values it defines not those of other live values
  (`clobberOk`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- The machine run of call-free statements. -/
def runPlain (c : Ctx) : Env → List Stmt → FeM Env
  | env, [] => pure env
  | env, s :: rest => do
    let vals ← runInst c env s.inst
    let env ← Fe.Sonatina.bind env s.dsts vals
    runPlain c env rest

theorem runPlain_append (c : Ctx) (env : Env) (ms ms' : List Stmt) :
    runPlain c env (ms ++ ms') = (runPlain c env ms >>= fun env => runPlain c env ms') := by
  induction ms generalizing env with
  | nil => simp [runPlain]
  | cons s rest ih => simp only [List.cons_append, runPlain, bind_assoc, ih]

/-- An operand with a word evaluates to it, as an `i256`. -/
theorem mval_eval {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalOperand env o = pure (.int 256 m) := by
  cases o with
  | var r =>
    simp only [mval] at h
    split at h
    · next v hv => cases h; simp [evalOperand, hv]
    · cases h
  | imm bits v =>
    simp only [mval] at h
    split at h
    · next hb => cases h; subst hb; rfl
    · cases h

theorem mval_evalInt {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalInt env o = pure (256, m) := by
  simp [evalInt, mval_eval h]

theorem mval_evalWord {env : Env} {o : Operand} {m : Nat} (h : mval env o = some m) :
    evalWord env o = pure (Ethereum.UInt256.ofNat m) := by
  simp [evalWord, mval_evalInt h]

/-- Binding one word result. -/
theorem bind_one (env : Env) (r : Nat) (v : Nat) :
    Fe.Sonatina.bind env [(r, .int 256)] [.int 256 v] = pure (env.insert r (.int 256 (v % W))) := by
  simp [Fe.Sonatina.bind, Val.as, Ty.bits, W]

/-- The run of a binary operation on two words. -/
theorem runPlain_bin (c : Ctx) {env : Env} {op : BinOp} {a b : Operand} {x y r : Nat}
    (ha : mval env a = some x) (hb : mval env b = some y) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .bin op a b⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (op.eval 256 x y % W))) rest := by
  simp [runPlain, runInst, evalPair, mval_evalInt ha, mval_evalInt hb, bind_one]

/-- The run of a comparison of two words. -/
theorem runPlain_cmp (c : Ctx) {env : Env} {op : CmpOp} {a b : Operand} {x y r : Nat}
    (ha : mval env a = some x) (hb : mval env b = some y) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .cmp op a b⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (if op.eval 256 x y then 1 else 0))) rest := by
  simp only [runPlain, runInst, evalPair, mval_evalInt ha, mval_evalInt hb, pure_bind, beq_self_eq_true,
    if_true, Fe.Sonatina.bind, Fe.Sonatina.bool]
  split <;> simp [Val.as, Ty.bits]

/-- The run of `is_zero` of a word. -/
theorem runPlain_isZero (c : Ctx) {env : Env} {a : Operand} {x r : Nat}
    (ha : mval env a = some x) (rest : List Stmt) :
    runPlain c env (⟨[(r, .int 256)], .isZero a⟩ :: rest) =
      runPlain c (env.insert r (.int 256 (if x = 0 then 1 else 0))) rest := by
  simp only [runPlain, runInst, mval_evalInt ha, pure_bind, Fe.Sonatina.bind, Fe.Sonatina.bool]
  split <;> simp_all [Val.as, Ty.bits]

/-! ## The frame relation across a statement -/

/-- The machine value of each live value of `L` other than `own`'s is kept by an update of the
    machine environment that changes only `ds`, when no machine value in `ds` is one of theirs. -/
theorem mval_keep {vm : VM} {envM envM' : Env} {ds : List Nat}
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {y : Nat}
    (hy : ∀ m ∈ ds, vm.find? y ≠ some (.var m)) :
    (vm.find? y).bind (mval envM') = (vm.find? y).bind (mval envM) := by
  cases h : vm.find? y with
  | none => rfl
  | some o =>
    cases o with
    | var r =>
      have hr : r ∉ ds := fun hm => hy r hm h
      simp only [Option.bind_some, mval, hkeep r hr]
    | imm bits v => rfl

theorem foldl_insert_other {x : Nat} :
    ∀ (l : List ((Nat × Ty) × H.Val)) (env : HEnv), (∀ p ∈ l, p.1.1 ≠ x) →
      (l.foldl (fun env (d, v) => env.insert d.1 v) env)[x]? = env[x]?
  | [], _, _ => rfl
  | p :: l, env, h => by
    rw [List.foldl_cons, foldl_insert_other l _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rw [Std.TreeMap.getElem?_insert]
    have := h p (List.mem_cons_self ..)
    simp [compare_eq_iff_eq, this]

/-- A binding leaves the values it does not bind. -/
theorem bindVals_other {env env' : HEnv} {dsts : List (Nat × Ty)} {vals : List H.Val}
    (h : bindVals env dsts vals = some env') {x : Nat} (hx : x ∉ dsts.map (·.1)) :
    env'[x]? = env[x]? := by
  unfold bindVals at h
  split at h
  · cases h
    apply foldl_insert_other
    intro p hp
    have := (List.of_mem_zip hp).1
    exact fun he => hx (List.mem_map.mpr ⟨p.1, this, he⟩)
  · cases h

theorem bindVals_one {env env' : HEnv} {x : Nat} {t : Ty} {v : H.Val}
    (h : bindVals env [(x, t)] [v] = some env') : v.fits t = true ∧ env' = env.insert x v := by
  unfold bindVals at h
  split at h
  · next hc => cases h; simp at hc; exact ⟨hc, rfl⟩
  · cases h

/-- The frame relation after a statement: the values live after it that it does not define are
    live before it and keep their values on both sides (the machine values the statement defines
    are none of theirs, `clobberOk`); those it defines are related by `hnew`. -/
theorem envRel_step {z : Bool} {F : Frame} {g : Ghost} {hst hst' : H.State} {envH envH' : HEnv}
    {envM envM' : Env} {L L' : List Nat} {dsts : List (Nat × Ty)} {vals : List H.Val}
    {ds : List Nat}
    (hE : EnvRel z F g hst envH envM L)
    (hL : ∀ y ∈ L', y ∉ dsts.map (·.1) → y ∈ L)
    (hb : bindVals envH dsts vals = some envH')
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?)
    (hcl : ∀ y ∈ L', y ∉ dsts.map (·.1) → ∀ m ∈ ds, F.vm.find? y ≠ some (.var m))
    (hold : ∀ v, ValOk hst v → ValOk hst' v)
    (horig : ∀ os v, OrigOk g hst F.R F.fpf os v → OrigOk g hst' F.R F.fpf os v)
    (hnew : ∀ x ∈ dsts.map (·.1), x ∈ L' → ∃ v m, envH'[x]? = some v ∧
      (∃ t, F.decls.find? x = some t ∧ v.fits t = true) ∧ (F.vm.find? x).bind (mval envM') = some m ∧
      VRel g z (F.D x) v m ∧ ValOk hst' v ∧ OrigOk g hst' F.R F.fpf (origOf F.O (.var x)) v) :
    EnvRel z F g hst' envH' envM' L' := by
  intro x hx
  by_cases hd : x ∈ dsts.map (·.1)
  · exact hnew x hd hx
  · obtain ⟨v, m, h1, h2, h3, h4, h5, h6⟩ := hE x (hL x hx hd)
    refine ⟨v, m, ?_, h2, ?_, h4, hold v h5, horig _ v h6⟩
    · rw [bindVals_other hb hd]; exact h1
    · rw [mval_keep hkeep (hcl x hx hd)]; exact h3

theorem take1_some {inst : Inst} {ms rest : List Stmt} {r : Nat} (h : take1 inst ms = some (r, rest)) :
    ms = ⟨[(r, .int 256)], inst⟩ :: rest := by
  unfold take1 at h
  split at h
  · next r' i rest' =>
    split at h
    · next he => cases h; rw [beq_iff_eq.mp he]
    · cases h
  · cases h

theorem stmt_bin {c : FCtx} {vm vm' : VM} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {ds : List Nat} {op : BinOp} {a b : Operand} {x : Nat} {tx : Ty}
    (hi : s.inst = .base (.bin op a b)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ ta tb a' b' r, c.tyOf a = some ta ∧ c.tyOf b = some tb ∧ mop vm a = some a' ∧
      mop vm b = some b' ∧
      (sameW ta tb && !op.generic && (ta.bits == 256 || ta.bits == 1 && op.okI1) &&
        sameW tx ta) = true ∧
      ms = ⟨[(r, .int 256)], .bin op a' b'⟩ :: ms' ∧ vm' = vm ∧ vm.find? x = some (.var r) ∧
      mb' = mb ∧ ds = [r] := by
  simp only [stmt, hi, hd, bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, ite_true] at h
  obtain ⟨ta, hta, tb, htb, a', ha', b', hb', h⟩ := h
  split at h
  · next hok =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨r, rest⟩, ht, h⟩ := h
    have hms := take1_some ht
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨vm2, hv, h⟩ := h
    split at hv
    · next hf =>
      cases hv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨ta, tb, a', b', r, hta, htb, ha', hb', hok, hms, rfl, beq_iff_eq.mp hf, rfl, rfl⟩
    · cases hv
  · simp at h

/-! ## Operands -/

/-- Whether an operand is a derived value of the frame (S8). -/
def Frame.dOp (F : Frame) : Operand → Bool
  | .var y => F.D y
  | .imm .. => false

/-- A source operand live (or an immediate of its width) at a point where the frame relation
    holds: its H value, of its type, and its machine operand's word, related. -/
theorem opnd_rel {z : Bool} {F : Frame} {g : Ghost} {hst : H.State} {envH : HEnv} {envM : Env}
    {L : List Nat} {c : FCtx} {vm : VM} {a a' : Operand} {ta : Ty}
    (hE : EnvRel z F g hst envH envM L) (hdecl : F.decls = c.decls) (hvm : F.vm = vm)
    (hlive : ∀ y, a = .var y → y ∈ L) (ht : c.tyOf a = some ta) (hm : mop vm a = some a') :
    ∃ v m, evalOp envH a = some v ∧ v.fits ta = true ∧ mval envM a' = some m ∧
      VRel g z (F.dOp a) v m ∧ ValOk hst v ∧ OrigOk g hst F.R F.fpf (origOf F.O a) v := by
  cases a with
  | var y =>
    obtain ⟨v, m, h1, ⟨t, ht', hf⟩, h3, h4, h5, h6⟩ := hE y (hlive y rfl)
    simp only [FCtx.tyOf] at ht
    rw [hdecl, ht] at ht'
    cases ht'
    simp only [mop] at hm
    rw [hvm, hm] at h3
    exact ⟨v, m, h1, hf, h3, h4, h5, h6⟩
  | imm bits n =>
    simp only [FCtx.tyOf] at ht
    split at ht
    · next hw =>
      cases ht
      simp only [mop, Option.some.injEq] at hm
      subst hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      refine ⟨.int bits n, n, rfl, ?_, by simp [mval], rfl, trivial, trivial⟩
      simp [H.Val.fits, hw.2]
    · cases ht

theorem OrigOk.mono {g : Ghost} {hst : H.State} {R : NatMap Range} {fpf : List Range}
    {os os' : List Nat} {v : H.Val} (h : OrigOk g hst R fpf os v) (hs : ∀ o ∈ os, o ∈ os') :
    OrigOk g hst R fpf os' v := by
  cases v with
  | int => trivial
  | ptr b o =>
    rcases h with h | ⟨hl, ⟨s, hs1, hs2⟩ | ⟨h0, hd⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hl, Or.inl ⟨s, hs s.succ hs1, hs2⟩⟩
    · exact Or.inr ⟨hl, Or.inr ⟨hs 0 h0, hd⟩⟩

/-! ## Binary operations -/

theorem binVal_some {st : H.State} {op : BinOp} {x y : H.Val} (hg : op.generic = false)
    (hb : x.bits = y.bits) : ∃ v, binVal st op x y = some v := by
  unfold binVal
  rw [hg, hb]
  simp only [Bool.false_or, bne_self_eq_false, Bool.false_eq_true, if_false]
  match x, y with
  | .int _ _, .int _ _ => exact ⟨_, rfl⟩
  | .ptr _ _, .int _ _ => exact ⟨_, rfl⟩
  | .int _ _, .ptr _ _ => exact ⟨_, rfl⟩
  | .ptr _ _, .ptr _ _ => exact ⟨_, rfl⟩

theorem ptrBin_some {op : BinOp} {b o k : Nat} {f : Bool} {v : H.Val}
    (h : ptrBin op b o k f = some v) :
    ∃ o', v = .ptr b o' ∧ (o' < W ∨ o' = o) ∧
      ((op = .add ∨ op = .or ∨ op = .xor ∨ op = .and) ∨ (op = .sub ∧ f = true)) := by
  cases op <;> simp only [ptrBin, Option.some.injEq, reduceCtorEq] at h
  · exact ⟨_, h.symm, Or.inl (Nat.mod_lt _ (by positivity)), Or.inl (Or.inl rfl)⟩
  · split at h
    · next hf => cases h; exact ⟨_, rfl, Or.inl (Nat.mod_lt _ (by positivity)), Or.inr ⟨rfl, hf⟩⟩
    · cases h
  all_goals (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals (subst h; exact ⟨_, rfl, Or.inr rfl, by simp⟩)

/-- A pointer `binVal` gives keeps an operand's block, through one of the origin-keeping
    operations (`sub` only with the pointer first), at an offset below `2 ^ 256` if the
    operands' are. -/
theorem binVal_ptr {st : H.State} {op : BinOp} {x y : H.Val} {b o : Nat}
    (h : binVal st op x y = some (.ptr b o)) (hx : ValOk st x) (hy : ValOk st y) :
    o < W ∧ (((∃ o', x = .ptr b o') ∧ (op = .add ∨ op = .sub ∨ op = .or ∨ op = .xor ∨ op = .and)) ∨
      ((∃ o', y = .ptr b o') ∧ (op = .add ∨ op = .or ∨ op = .xor ∨ op = .and))) := by
  unfold binVal at h
  split at h
  · cases h
  match x, y, h with
  | .int _ _, .int _ _, h => cases h
  | .ptr b' o', .int _ k, h =>
    dsimp only at h
    cases hp : ptrBin op b' o' k true with
    | none => rw [hp] at h; cases h
    | some v =>
      rw [hp] at h
      simp only [Option.getD_some, Option.some.injEq] at h
      subst h
      obtain ⟨o2, he, hlt, hop⟩ := ptrBin_some hp
      cases he
      refine ⟨hlt.elim id (fun e => e ▸ hx.2), Or.inl ⟨⟨o', rfl⟩, ?_⟩⟩
      rcases hop with h | ⟨h, _⟩
      · rcases h with h | h | h | h <;> simp [h]
      · simp [h]
  | .int _ k, .ptr b' o', h =>
    dsimp only at h
    cases hp : ptrBin op b' o' k false with
    | none => rw [hp] at h; cases h
    | some v =>
      rw [hp] at h
      simp only [Option.getD_some, Option.some.injEq] at h
      subst h
      obtain ⟨o2, he, hlt, hop⟩ := ptrBin_some hp
      cases he
      refine ⟨hlt.elim id (fun e => e ▸ hy.2), Or.inr ⟨⟨o', rfl⟩, ?_⟩⟩
      rcases hop with h | ⟨_, h⟩
      · exact h
      · cases h
  | .ptr _ _, .ptr _ _, h => cases h

theorem wrap_lt (bits : Nat) (n : Int) : wrap bits n < 2 ^ bits := by
  unfold wrap
  have hp : ((2 : Int) ^ bits) = ((2 ^ bits : Nat) : Int) := by push_cast; rfl
  rw [hp]
  have hp' : (0 : Int) < ((2 ^ bits : Nat) : Int) := by positivity
  rw [Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hp'))]
  exact Int.emod_lt_of_pos _ hp'

theorem toNat_lt' (u : Ethereum.UInt256) : u.toNat < W := u.val.isLt

/-- An operation on words gives a word. -/
theorem eval_lt (op : BinOp) {x y : Nat} (hx : x < W) (hy : y < W) : op.eval 256 x y < W := by
  cases op <;> simp only [BinOp.eval]
  all_goals first
    | exact wrap_lt _ _
    | exact toNat_lt' _
    | (split <;> (try split) <;> first
        | exact wrap_lt _ _
        | exact Nat.two_pow_pos 256
        | exact Nat.sub_lt (Nat.two_pow_pos 256) Nat.one_pos
        | exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
        | exact lt_of_le_of_lt (Nat.mod_le _ _) hx
        | (rw [Nat.shiftRight_eq_div_pow]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hy))
    | exact Nat.and_lt_two_pow _ hy
    | exact Nat.or_lt_two_pow hx hy
    | exact Nat.xor_lt_two_pow hx hy

theorem fits_iff {v : H.Val} {t : Ty} (ht : Ty.value t = true) :
    v.fits t = true ↔ match v with
      | .int bits n => bits = t.bits ∧ n < 2 ^ t.bits
      | .ptr _ o => t.bits = 256 ∧ o < W := by
  cases v <;> cases t <;> simp_all [H.Val.fits, Ty.value, Ty.bits, W]

theorem fits_sameW {v : H.Val} {t u : Ty} (h : sameW t u = true) (hv : v.fits u = true) :
    v.fits t = true := by
  simp only [sameW, Bool.and_eq_true, beq_iff_eq] at h
  rw [fits_iff h.1.2] at hv
  rw [fits_iff h.1.1, h.2]
  exact hv

/-- `binVal`'s result has its operands' type, at a word or (an operation of `okI1`) at `i1`. -/
theorem binVal_fits {st : H.State} {op : BinOp} {x y v : H.Val} {t : Ty}
    (h : binVal st op x y = some v) (hx : x.fits t = true) (hy : y.fits t = true)
    (ht : Ty.value t = true) (hb : t.bits = 256 ∨ (t.bits = 1 ∧ op.okI1 = true))
    (hox : ValOk st x) (hoy : ValOk st y) : v.fits t = true := by
  rw [fits_iff ht]
  cases v with
  | ptr b o =>
    obtain ⟨hlt, hc⟩ := binVal_ptr h hox hoy
    rcases hc with ⟨⟨o', rfl⟩, _⟩ | ⟨⟨o', rfl⟩, _⟩
    · exact ⟨(fits_ptr hx).2, hlt⟩
    · exact ⟨(fits_ptr hy).2, hlt⟩
  | int bits n =>
    unfold binVal at h
    split at h
    · cases h
    match x, y, h with
    | .int b1 a1, .int _ a2, h =>
      simp only [Option.some.injEq, H.Val.int.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h1'⟩ := fits_int hx
      obtain ⟨h2, _⟩ := fits_int hy
      refine ⟨h1', ?_⟩
      rw [h1']
      rcases hb with hb | ⟨hb, hok⟩
      · rw [hb] at h1 h2 ⊢; exact eval_lt op h1 h2
      · rw [hb] at h1 h2 ⊢
        cases op <;> simp [BinOp.okI1] at hok <;> simp only [BinOp.eval]
        · exact Nat.and_lt_two_pow _ h2
        · exact Nat.or_lt_two_pow h1 h2
        · exact Nat.xor_lt_two_pow h1 h2
    | .ptr b' o', .int _ k, h =>
      dsimp only at h
      have ht256 := (fits_ptr hx).2
      cases hp : ptrBin op b' o' k true with
      | none =>
        rw [hp] at h
        simp only [Option.getD_none, Option.some.injEq, H.Val.int.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hk : k < W := by have := (fits_int hy).1; rwa [ht256] at this
        refine ⟨ht256.symm, ?_⟩
        rw [ht256]
        exact eval_lt op (Nat.mod_lt _ (by positivity)) hk
      | some v' =>
        rw [hp] at h
        obtain ⟨_, he, _⟩ := ptrBin_some hp
        simp only [Option.getD_some, Option.some.injEq] at h
        rw [h] at he; cases he
    | .int _ k, .ptr b' o', h =>
      dsimp only at h
      have ht256 := (fits_ptr hy).2
      cases hp : ptrBin op b' o' k false with
      | none =>
        rw [hp] at h
        simp only [Option.getD_none, Option.some.injEq, H.Val.int.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hk : k < W := by have := (fits_int hx).1; rwa [ht256] at this
        refine ⟨ht256.symm, ?_⟩
        rw [ht256]
        exact eval_lt op hk (Nat.mod_lt _ (by positivity))
      | some v' =>
        rw [hp] at h
        obtain ⟨_, he, _⟩ := ptrBin_some hp
        simp only [Option.getD_some, Option.some.injEq] at h
        rw [h] at he; cases he
    | .ptr _ _, .ptr _ _, h =>
      simp only [Option.some.injEq, H.Val.int.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ht256 := (fits_ptr hx).2
      refine ⟨ht256.symm, ?_⟩
      rw [ht256]
      exact eval_lt op (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))

theorem mem_sortedInsert {x y : Nat} : ∀ {l : List Nat}, y ∈ sortedInsert x l ↔ y = x ∨ y ∈ l
  | [] => by simp [sortedInsert]
  | z :: zs => by
    unfold sortedInsert
    split
    · simp
    · split
      · next h => simp only [beq_iff_eq] at h; subst h; simp
      · rw [List.mem_cons, List.mem_cons, mem_sortedInsert]; tauto

theorem mem_nset {y : Nat} : ∀ {l : List Nat}, y ∈ nset l ↔ y ∈ l
  | [] => by simp [nset]
  | x :: xs => by
    show y ∈ sortedInsert x (nset xs) ↔ _
    rw [mem_sortedInsert, mem_nset, List.mem_cons]


/-! ## The step of a source statement

What the simulation needs of each source statement `s` other than a call (`TemplOk`): the
machine's run of the statements of its template, with calls by any oracle, ends in a result
that H's step at `s` matches (`StepOk`): H halts in an outcome that excuses the result, or both
go on, related by `Inv` and `EnvRel` at the point after `s`, the ghost extended (`GhostLe`). -/

/-- H's outcome `o` excuses the machine's result `r`: H's run is undefined or out of heap
    there, or the machine ends as H does. -/
def Excuses {α : Type} (o : Outcome) (r : Except (Exit World) α) : Prop :=
  o = .ub ∨ o = .exhausted ∨ ∃ e, r = .error e ∧ Matches o (.error e)

/-- The ghost `g'` of state `hst'` extends the ghost `g` of `hst`: old blocks keep their
    machine bases, sizes and address words, heap blocks stay heap blocks, and a live block whose
    range misses every range of `fp` (the running function's footprint) stays live. -/
structure GhostLe (fp : List Range) (g g' : Ghost) (hst hst' : H.State) : Prop where
  size : hst.blocks.size ≤ hst'.blocks.size
  j : ∀ b, b < hst.blocks.size → g'.j b = g.j b
  bsize : ∀ b, b < hst.blocks.size → hst'.bsize b = hst.bsize b
  addr : ∀ b, b < hst.blocks.size → hst'.addrOf b = hst.addrOf b
  heap : ∀ b, g.heap b → g'.heap b
  live : ∀ b, g.live b → (∀ r ∈ fp, Disj r (g.rg hst b)) → g'.live b

theorem GhostLe.refl (fp : List Range) (g : Ghost) (hst : H.State) : GhostLe fp g g hst hst :=
  ⟨le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ h _ => h⟩

theorem GhostLe.rg {fp : List Range} {g g' : Ghost} {hst hst' : H.State}
    (h : GhostLe fp g g' hst hst') {b : Nat} (hb : b < hst.blocks.size) :
    g'.rg hst' b = g.rg hst b := by
  simp only [Ghost.rg, h.j b hb, h.bsize b hb]

theorem GhostLe.trans {fp : List Range} {g g' g'' : Ghost} {hst hst' hst'' : H.State}
    (h₁ : GhostLe fp g g' hst hst') (h₂ : GhostLe fp g' g'' hst' hst'')
    (hlt : ∀ b, g.live b → b < hst.blocks.size) : GhostLe fp g g'' hst hst'' where
  size := le_trans h₁.size h₂.size
  j b hb := by rw [h₂.j b (lt_of_lt_of_le hb h₁.size), h₁.j b hb]
  bsize b hb := by rw [h₂.bsize b (lt_of_lt_of_le hb h₁.size), h₁.bsize b hb]
  addr b hb := by rw [h₂.addr b (lt_of_lt_of_le hb h₁.size), h₁.addr b hb]
  heap b hb := h₂.heap b (h₁.heap b hb)
  live b hb hd := h₂.live b (h₁.live b hb hd) (by rw [h₁.rg (hlt b hb)]; exact hd)

/-- What H does at statement `s`, against the machine's result `r` of its template: it halts in
    an outcome that excuses `r`, or the machine goes on and H steps to a state related to the
    machine's at the point after `s`, whose live values are `L'`. -/
def StepOk (P : HSection) (I : Fe.EVM.Env) (S : SecFacts) (F : Frame) (g : Ghost) (hst : H.State)
    (envH : HEnv) (s : HStmt) (L' : List Nat) (r : Except (Exit World) (Env × World)) : Prop :=
  (∃ o, (∀ rest, ExecBody P I envH (s :: rest) hst (.halt o)) ∧ Excuses o r) ∨
  ∃ envM' w', r = .ok (envM', w') ∧ ∃ envH' hst' g', Inv S hst' w' g' ∧
    EnvRel S.z F g' hst' envH' envM' L' ∧ GhostLe F.fpf g g' hst hst' ∧
    ∀ rest o, ExecBody P I envH' rest hst' o → ExecBody P I envH (s :: rest) hst o

/-- The machine statements `pre` of `s`'s template, run from `envM` and `w` with calls by any
    oracle, end in a result H's step at `s` matches. -/
def TemplOk (P : HSection) (I : Fe.EVM.Env) (cM : Ctx) (S : SecFacts) (F : Frame) (g : Ghost)
    (hst : H.State) (w : World) (envH : HEnv) (envM : Env) (s : HStmt) (L' : List Nat)
    (pre : List Stmt) : Prop :=
  ∀ (O : Oracle) r, (runBodyO O cM envM pre).exec I w = some r → StepOk P I S F g hst envH s L' r

/-- The facts the simulation has at source statement `s` of a function walked under `c`: the
    values live before it (`L`) and after it (`L'`), the machine values its template defines
    (`ds`), and what the checks give about it: its results are declared, its operands live, the
    machine values it defines none of another live value's (`clobberOk`), origins (S3) and, in
    address-0 mode, derived values (S8) of the function's place `k`. -/
structure At (S : SecFacts) (F : Frame) (c : FCtx) (Dr : Derived) (k : Nat) (s : HStmt)
    (callee? : Option Nat) (L L' ds : List Nat) : Prop where
  decls : F.decls = c.decls
  dsts : ∀ d ∈ s.dsts, F.decls.find? d.1 = some d.2
  uses : ∀ y, Operand.var y ∈ s.inst.args → y ∈ L
  keep : ∀ y ∈ L', y ∉ s.defs → y ∈ L
  clob : ∀ y, (y ∈ L ∨ y ∈ L') → y ∉ s.defs → ∀ m ∈ ds, F.vm.find? y ≠ some (.var m)
  nodup : (s.dsts.map (·.1)).Nodup
  self : ∀ y, Operand.var y ∈ s.inst.args → y ∉ s.defs
  orig : ∀ x t, s.dsts = [(x, t)] → ∀ o ∈ stmtOrig c.frec F.O s, o ∈ origOf F.O (.var x)
  D : F.D = Dr.has k
  obs : S.z = true → ∀ i a, s.inst.args[i]? = some a → Dr.op k a = true → i ∈ nonObserving Dr k s
  der : S.z = true → stmtDerived Dr k s callee? = true → ∀ x ∈ s.defs, Dr.has k x = true

theorem At.dOp {S : SecFacts} {F : Frame} {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt}
    {callee? : Option Nat} {L L' ds : List Nat} (hA : At S F c Dr k s callee? L L' ds) (a : Operand) :
    F.dOp a = Dr.op k a := by
  cases a <;> simp [Frame.dOp, Derived.op, hA.D]

/-- Call-free statements run with calls by any oracle as `runPlain` runs them. -/
theorem runBodyO_plain (O : Oracle) (c : Ctx) (env : Env) (ms : List Stmt)
    (h : ∀ st ∈ ms, ∀ g a, st.inst ≠ .call g a) : runBodyO O c env ms = runPlain c env ms := by
  induction ms generalizing env with
  | nil => rfl
  | cons st rest ih =>
    rcases st with ⟨dsts, inst⟩
    have h0 : ∀ g a, inst ≠ .call g a := h _ (List.mem_cons_self ..)
    simp only [runBodyO, runPlain, runStmtO]
    cases inst
    case call g a => exact absurd rfl (h0 g a)
    all_goals
      congr 1; funext vals; congr 1; funext env'
      exact ih env' fun st hs => h st (List.mem_cons_of_mem _ hs)

/-- A statement H steps without changing its state, to one value related to the machine value
    its template binds: the step goes on, related at the next point. -/
theorem stepOk_pure1 {P : HSection} {I : Fe.EVM.Env} {S : SecFacts} {F : Frame} {g : Ghost}
    {hst : H.State} {w : World} {envH : HEnv} {envM envM' : Env} {L L' : List Nat} {c : FCtx}
    {Dr : Derived} {k : Nat} {s : HStmt} {callee? : Option Nat} {ds : List Nat}
    (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds) {x : Nat} {tx : Ty} (hd : s.dsts = [(x, tx)])
    {v : H.Val} (hstep : stepInst P.ctx I envH hst s.inst = .ok [v] hst) (hfit : v.fits tx = true)
    (hkeep : ∀ r, r ∉ ds → envM'[r]? = envM[r]?) {m : Nat}
    (hm : (F.vm.find? x).bind (mval envM') = some m) (hv : VRel g S.z (F.D x) v m)
    (hok : ValOk hst v) (horig : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v) :
    StepOk P I S F g hst envH s L' (.ok (envM', w)) := by
  have hb : bindVals envH s.dsts [v] = some (envH.insert x v) := by
    simp [bindVals, hd, hfit]
  have hdefs : s.defs = [x] := by simp [HStmt.defs, hd]
  refine Or.inr ⟨envM', w, rfl, envH.insert x v, hst, g, hI, ?_, GhostLe.refl _ _ _,
    fun rest o hr => ExecBody.step hstep hb hr⟩
  refine envRel_step hE (fun y hy hn => hA.keep y hy (by rw [hdefs]; rwa [hd] at hn)) hb hkeep
    (fun y hy hn => hA.clob y (Or.inr hy) (by rw [hdefs]; rwa [hd] at hn)) (fun _ h => h) (fun _ _ h => h) ?_
  have hdt : F.decls.find? x = some tx := hA.dsts (x, tx) (by simp [hd])
  intro y hy _
  simp only [hd, List.map_cons, List.map_nil, List.mem_singleton] at hy
  subst hy
  exact ⟨v, m, by simp, ⟨tx, hdt, hfit⟩, hm, hv, hok, horig⟩

/-! ## Binary operations -/

theorem ptrBin_off {op : BinOp} {b o k b' o' : Nat} (A : Nat)
    (h : ptrBin op b o k true = some (.ptr b' o')) :
    b' = b ∧ (A + o') % W = op.eval 256 ((A + o) % W) k := by
  cases op <;> simp only [ptrBin, reduceCtorEq, Option.some.injEq, H.Val.ptr.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, wrap_add _ _ _⟩
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, wrap_sub _ _ _⟩
    · cases h
  all_goals
    split at h
    · next hk =>
      simp only [Option.some.injEq, H.Val.ptr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      refine ⟨rfl, ?_⟩
      simp only [BinOp.eval]
      first | rw [Nat.or_zero] | rw [Nat.xor_zero]
            | rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
    · cases h

theorem ptrBin_off2 {op : BinOp} {b o k b' o' : Nat} (A : Nat)
    (h : ptrBin op b o k false = some (.ptr b' o')) :
    b' = b ∧ (A + o') % W = op.eval 256 k ((A + o) % W) := by
  cases op <;> simp only [ptrBin, reduceCtorEq, Option.some.injEq, H.Val.ptr.injEq,
    Bool.false_eq_true, if_false] at h
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    show (A + (o + k) % W) % W = wrap 256 (((k + (A + o) % W : Nat)) : Int)
    rw [wrap_nat]; simp only [W]; omega
  all_goals
    split at h
    · next hk =>
      simp only [Option.some.injEq, H.Val.ptr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      refine ⟨rfl, ?_⟩
      simp only [BinOp.eval]
      first | rw [Nat.zero_or] | rw [Nat.zero_xor]
            | rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
    · cases h

theorem ptrBin_add_some (b o k : Nat) (f : Bool) : (ptrBin .add b o k f).isSome := by
  simp [ptrBin]

theorem ptrBin_sub_some (b o k : Nat) : (ptrBin .sub b o k true).isSome := by
  simp [ptrBin]

/-- A related machine word is a word. -/
theorem vrel_lt {g : Ghost} {z dx : Bool} {v : H.Val} {m : Nat} {t : Ty} (hv : VRel g z dx v m)
    (hf : v.fits t = true) (ht : Ty.value t = true) : m < W := by
  cases v with
  | int bits n =>
    have : n = m := hv
    subst this
    exact lt_of_lt_of_le (fits_int hf).1 (Nat.pow_le_pow_right (by norm_num) (value_bits ht).2)
  | ptr b o => rw [← hv.1]; exact Nat.mod_lt _ (by positivity)

/-- A binary operation (`lower_structural`): H's step gives the value `binVal` does, of the
    result's type, with no change of state; the machine's statement binds its machine value to
    a word related to it.  Outside address-0 mode every operand's word in H is its machine word;
    in it, rule S8 allows a derived (possibly inexact) pointer only as an operand of `add` with
    an integer, or the first of `sub`, which keep its block and add to its offset. -/
theorem inst_bin {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {F : Frame}
    {g : Ghost} {hst : H.State} {w : World} {envH : HEnv} {envM : Env} {L L' : List Nat}
    {c : FCtx} {Dr : Derived} {k : Nat} {s : HStmt} {mb mb' : Nat} {ms ms' : List Stmt}
    {callee? : Option Nat} {vm' : VM} {ds : List Nat} {op : BinOp} {a b : Operand} {x : Nat}
    {tx : Ty} (hI : Inv S hst w g) (hE : EnvRel S.z F g hst envH envM L)
    (hA : At S F c Dr k s callee? L L' ds)
    (hi : s.inst = .base (.bin op a b)) (hd : s.dsts = [(x, tx)])
    (h : stmt c true F.vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧ TemplOk P I cM S F g hst w envH envM s L' pre := by
  obtain ⟨ta, tb, a', b', r, hta, htb, ha', hb', hok, hms, rfl, hx, rfl, rfl⟩ := stmt_bin hi hd h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hsw, hgen⟩, hbits⟩, hsx⟩ := hok
  have hargs : s.inst.args = [a, b] := by simp [hi, HInst.args, HInst.skel, Inst.args]
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) hta ha'
  obtain ⟨vb, mb, hvb, hfb, hmb, hrb, hob, hgb⟩ := opnd_rel hE hA.decls rfl
    (fun y hy => hA.uses y (by rw [hargs, ← hy]; simp)) htb hb'
  have hval : Ty.value ta = true := by simp only [sameW, Bool.and_eq_true] at hsw; exact hsw.1.1
  have hfb' : vb.fits ta = true := fits_sameW hsw hfb
  have hbw : ∀ v : H.Val, v.fits ta = true → v.bits = ta.bits := by
    intro v hv
    rw [fits_iff hval] at hv
    cases v with
    | int bits n => exact hv.1
    | ptr _ _ => exact hv.1.symm
  obtain ⟨v, hv⟩ := binVal_some (st := hst) hgen ((hbw va hfa).trans (hbw vb hfb').symm)
  have hfv : v.fits ta = true := binVal_fits hv hfa hfb' hval hbits hoa hob
  have hla : ma < W := vrel_lt hra hfa hval
  have hlb : mb < W := vrel_lt hrb hfb' hval
  -- Rule S8, in address-0 mode: where a derived operand may be, and that the result is derived.
  have hobs : S.z = true → (F.dOp a = true → (op = .add ∧ F.dOp b = false) ∨
      (op = .sub ∧ F.dOp b = false)) ∧ (F.dOp b = true → op = .add ∧ F.dOp a = false) := by
    intro hz
    rw [hA.dOp a, hA.dOp b]
    have h0 := hA.obs hz 0 a (by rw [hargs]; rfl)
    have h1 := hA.obs hz 1 b (by rw [hargs]; rfl)
    simp only [nonObserving, hi] at h0 h1
    constructor
    · intro hda
      have := h0 hda
      cases op <;> simp_all
    · intro hdb
      have := h1 hdb
      cases op <;> simp_all
  have hder : S.z = true → (F.dOp a = true ∨ F.dOp b = true) → F.D x = true := by
    intro hz hab
    have hs : stmtDerived Dr k s callee? = true := by
      obtain ⟨h1, h2⟩ := hobs hz
      rw [hA.dOp a, hA.dOp b] at h1 h2 hab
      simp only [stmtDerived, hi]
      rcases hab with hab | hab
      · rcases h1 hab with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [hab]
      · obtain ⟨rfl, _⟩ := h2 hab; simp [hab]
    rw [hA.D]
    exact hA.der hz hs x (by simp [HStmt.defs, hd])
  -- The value is related to the machine's word.
  have hw : ∀ y : H.Val, ∀ dy my, VRel g S.z dy y my → ValOk hst y → S.z = false →
      hst.word y = my := fun y dy my hy ho hz => vrel_word hI hy ho (Or.inl hz)
  have hrel : VRel g S.z (F.D x) v (op.eval 256 ma mb % W) := by
    have hev : ∀ n, n < W → op.eval 256 ma mb = n → n = op.eval 256 ma mb % W := fun n hn he => by
      rw [he, Nat.mod_eq_of_lt hn]
    unfold binVal at hv
    rw [if_neg (by rw [hgen]; simp [(hbw va hfa).trans (hbw vb hfb').symm])] at hv
    match va, vb, hv, hra, hrb, hoa, hob with
    | .int bits na, .int _ nb, hv, hra, hrb, _, _ =>
      simp only [Option.some.injEq] at hv
      subst hv
      have e1 : na = ma := hra
      have e2 : nb = mb := hrb
      subst e1 e2
      have hbt : bits = ta.bits := hbw _ hfa
      show op.eval bits na nb = _
      have : op.eval bits na nb = op.eval 256 na nb := by
        rcases hbits with h256 | ⟨h1, hi1⟩
        · rw [hbt, h256]
        · rw [hbt, h1]; exact BinOp.okI1_eval hi1 1 256 _ _
      rw [this, Nat.mod_eq_of_lt (eval_lt op hla hlb)]
    | .ptr ba oa, .int _ kb, hv, hra, hrb, hoa, _ =>
      have e2 : kb = mb := hrb
      subst e2
      dsimp only at hv
      cases hp : ptrBin op ba oa kb true with
      | some v' =>
        rw [hp] at hv
        simp only [Option.getD_some, Option.some.injEq] at hv
        subst hv
        obtain ⟨o', rfl, _⟩ := ptrBin_some hp
        obtain ⟨-, he⟩ := ptrBin_off (g.j ba) hp
        exact ⟨by rw [he, hra.1, Nat.mod_eq_of_lt (eval_lt op hla hlb)],
          fun hz => hder hz (Or.inl (hra.2 hz))⟩
      | none =>
        rw [hp] at hv
        simp only [Option.getD_none, Option.some.injEq] at hv
        subst hv
        cases hz : S.z
        · show op.eval 256 (hst.word (.ptr ba oa)) kb = _
          rw [hw _ _ _ hra hoa hz, Nat.mod_eq_of_lt (eval_lt op hla hlb)]
        · exfalso
          rcases (hobs hz).1 (hra.2 hz) with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [ptrBin] at hp
    | .int _ ka, .ptr bb ob, hv, hra, hrb, _, hob =>
      have e1 : ka = ma := hra
      subst e1
      dsimp only at hv
      cases hp : ptrBin op bb ob ka false with
      | some v' =>
        rw [hp] at hv
        simp only [Option.getD_some, Option.some.injEq] at hv
        subst hv
        obtain ⟨o', rfl, _⟩ := ptrBin_some hp
        obtain ⟨-, he⟩ := ptrBin_off2 (g.j bb) hp
        exact ⟨by rw [he, hrb.1, Nat.mod_eq_of_lt (eval_lt op hla hlb)],
          fun hz => hder hz (Or.inr (hrb.2 hz))⟩
      | none =>
        rw [hp] at hv
        simp only [Option.getD_none, Option.some.injEq] at hv
        subst hv
        cases hz : S.z
        · show op.eval 256 ka (hst.word (.ptr bb ob)) = _
          rw [hw _ _ _ hrb hob hz, Nat.mod_eq_of_lt (eval_lt op hla hlb)]
        · exfalso
          obtain ⟨rfl, _⟩ := (hobs hz).2 (hrb.2 hz)
          simp [ptrBin] at hp
    | .ptr ba oa, .ptr bb ob, hv, hra, hrb, hoa, hob =>
      simp only [Option.some.injEq] at hv
      subst hv
      cases hz : S.z
      · show op.eval 256 (hst.word (.ptr ba oa)) (hst.word (.ptr bb ob)) = _
        rw [hw _ _ _ hra hoa hz, hw _ _ _ hrb hob hz, Nat.mod_eq_of_lt (eval_lt op hla hlb)]
      · exfalso
        rcases (hobs hz).1 (hra.2 hz) with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hrb.2 hz] at h <;> cases h
  have hok : ValOk hst v := by
    cases v with
    | int => trivial
    | ptr bv ov =>
      obtain ⟨holt, hc⟩ := binVal_ptr hv hoa hob
      rcases hc with ⟨⟨o', rfl⟩, _⟩ | ⟨⟨o', rfl⟩, _⟩
      · exact ⟨hoa.1, holt⟩
      · exact ⟨hob.1, holt⟩
  have horig : OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v := by
    cases v with
    | int => trivial
    | ptr bv ov =>
      obtain ⟨_, hc⟩ := binVal_ptr hv hoa hob
      have hsub := hA.orig x tx hd
      simp only [stmtOrig, hi] at hsub
      rcases hc with ⟨⟨o', rfl⟩, hop⟩ | ⟨⟨o', rfl⟩, hop⟩
      · refine OrigOk.mono (os := origOf F.O a) hga fun o ho => hsub o ?_
        rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp [mem_nset, ho]
      · refine OrigOk.mono (os := origOf F.O b) hgb fun o ho => hsub o ?_
        rcases hop with rfl | rfl | rfl | rfl <;> simp [mem_nset, ho]
  refine ⟨[_], hms, rfl, fun O res hres => ?_⟩
  rw [runBodyO_plain O cM envM _ (by simp), runPlain_bin cM hma hmb] at hres
  simp only [runPlain, Fe.M.exec_pure, Option.some.injEq] at hres
  subst hres
  refine stepOk_pure1 hI hE hA hd (by simp [stepInst, hi, hva, hvb, hv]) (fits_sameW hsx hfv)
    (fun r' hr' => ?_) (by rw [hx]; simp [mval]) hrel hok horig
  have hne : r ≠ r' := fun e => hr' (by simp [e])
  rw [Std.TreeMap.getElem?_insert]
  simp [compare_eq_iff_eq, hne]

end Fe.Sonatina.Stage3.Place
