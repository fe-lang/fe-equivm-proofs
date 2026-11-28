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

/-- A binary operation (`lower_structural`), outside address-0 mode: H's step gives the value
    `binVal` does, of the result's type, with no change of state; the machine's statement binds
    its machine value to the word of it; the value is related, valid, and rule S3 holds of it
    by the origins certificate (`horig`). -/
theorem inst_bin {S : SecFacts} {F : Frame} {g : Ghost} {hst : H.State} {w : World}
    {envH : HEnv} {envM : Env} {L : List Nat} {c : FCtx} {vm vm' : VM} {s : HStmt}
    {mb mb' : Nat} {ms ms' : List Stmt} {callee? : Option Nat} {ds : List Nat} {op : BinOp}
    {a b : Operand} {x : Nat} {tx : Ty} (P : HSection) (I : Fe.EVM.Env) (cM : Ctx)
    (fr : FuncRec) (hI : Inv S hst w g) (hz : S.z = false)
    (hE : EnvRel S.z F g hst envH envM L) (hdecl : F.decls = c.decls) (hvm : F.vm = vm)
    (hi : s.inst = .base (.bin op a b)) (hd : s.dsts = [(x, tx)])
    (hlive : ∀ y, (a = .var y ∨ b = .var y) → y ∈ L)
    (horig : ∀ o ∈ stmtOrig fr F.O s, o ∈ origOf F.O (.var x))
    (h : stmt c true vm s mb ms callee? = some (vm', mb', ms', ds)) :
    ∃ v r st1, ms = st1 :: ms' ∧ ds = [r] ∧ vm' = vm ∧ mb' = mb ∧ vm.find? x = some (.var r) ∧
      (∀ rest, runPlain cM envM (st1 :: rest) =
        runPlain cM (envM.insert r (.int 256 (hst.word v))) rest) ∧
      stepInst P.ctx I envH hst s.inst = .ok [v] hst ∧ v.fits tx = true ∧
      VRel g S.z (F.D x) v (hst.word v) ∧ ValOk hst v ∧
      OrigOk g hst F.R F.fpf (origOf F.O (.var x)) v := by
  obtain ⟨ta, tb, a', b', r, hta, htb, ha', hb', hok, hms, rfl, hx, rfl, rfl⟩ := stmt_bin hi hd h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hsw, hgen⟩, hbits⟩, hsx⟩ := hok
  obtain ⟨va, ma, hva, hfa, hma, hra, hoa, hga⟩ :=
    opnd_rel hE hdecl hvm (fun y hy => hlive y (Or.inl hy)) hta ha'
  obtain ⟨vb, mb, hvb, hfb, hmb, hrb, hob, hgb⟩ :=
    opnd_rel hE hdecl hvm (fun y hy => hlive y (Or.inr hy)) htb hb'
  have hval : Ty.value ta = true := by simp only [sameW, Bool.and_eq_true] at hsw; exact hsw.1.1
  have hfb' : vb.fits ta = true := fits_sameW hsw hfb
  -- The operands' widths are the type's.
  have hbw : ∀ v : H.Val, v.fits ta = true → v.bits = ta.bits := by
    intro v hv
    rw [fits_iff hval] at hv
    cases v with
    | int bits n => exact hv.1
    | ptr _ _ => exact hv.1.symm
  obtain ⟨v, hv⟩ := binVal_some (st := hst) hgen ((hbw va hfa).trans (hbw vb hfb').symm)
  have hwa := vrel_word hI hra hoa (Or.inl hz)
  have hwb := vrel_word hI hrb hob (Or.inl hz)
  have hfv : v.fits ta = true := binVal_fits hv hfa hfb' hval hbits hoa hob
  have hword : hst.word v = op.eval 256 ma mb := by
    rw [binVal_word hv, hbw va hfa, hwa, hwb]
    rcases hbits with h256 | ⟨h1, hi1⟩
    · rw [h256]
    · rw [h1]; exact BinOp.okI1_eval hi1 1 256 _ _
  have hlt : ∀ u : H.Val, u.fits ta = true → hst.word u < W := fun u hu =>
    word_lt hst u hu (value_bits hval).2
  have hok : ValOk hst v := by
    cases v with
    | int => trivial
    | ptr bv ov =>
      obtain ⟨holt, hc⟩ := binVal_ptr hv hoa hob
      rcases hc with ⟨⟨o', rfl⟩, _⟩ | ⟨⟨o', rfl⟩, _⟩
      · exact ⟨hoa.1, holt⟩
      · exact ⟨hob.1, holt⟩
  refine ⟨v, r, _, hms, rfl, rfl, rfl, hx, fun rest => ?_, ?_, fits_sameW hsx hfv, ?_, hok, ?_⟩
  · rw [runPlain_bin cM hma hmb, ← hword, Nat.mod_eq_of_lt (hlt v hfv)]
  · simp [stepInst, hi, hva, hvb, hv]
  · cases v with
    | int bits n => rfl
    | ptr bv ov =>
      refine ⟨?_, fun h => by rw [hz] at h; cases h⟩
      have hj : g.j bv ≠ 0 := fun h0 => by rw [hI.zero bv hok.1 h0] at hz; cases hz
      rw [word_ptr, hI.exact bv hok.1 hj]
  · cases v with
    | int => trivial
    | ptr bv ov =>
      obtain ⟨_, hc⟩ := binVal_ptr hv hoa hob
      have hsub : ∀ o ∈ stmtOrig fr F.O s, o ∈ origOf F.O (.var x) := horig
      simp only [stmtOrig, hi] at hsub
      rcases hc with ⟨⟨o', rfl⟩, hop⟩ | ⟨⟨o', rfl⟩, hop⟩
      · refine OrigOk.mono (os := origOf F.O a) hga fun o ho => hsub o ?_
        rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp [mem_nset, ho]
      · refine OrigOk.mono (os := origOf F.O b) hgb fun o ho => hsub o ?_
        rcases hop with rfl | rfl | rfl | rfl <;> simp [mem_nset, ho]

end Fe.Sonatina.Stage3.Place
