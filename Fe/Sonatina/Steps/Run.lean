import Fe.Sonatina.Steps.EdgeSplit

/-!
# Lemmas about runs

What the step kinds' simulations share:

- operand maps (`Inst.mapOps`, `Term.mapOps`, `Stmt.mapOps`) and `inc`, a phi's operand from a
  block, with the congruences `runInst_mapOps`, `runStmtO_mapOps`, `runTerm_mapOps`;
- `Fol`: an output computation against the input's remaining run, which may step alone;
- `enterOpt`, `enter` as an option (`enter_eq`), `enterOpt_spec`, `enter_val`, `enter_total`;
- bindings (`fold_get_not`, `fold_get_mem`, `fold_get_cases`, `EnvSub.fold`);
- unique definitions (`UniqueDefs`, from `ssa`), and the tree's antisymmetry
  (`DomTree.anc_antisymm`);
- `phi_has_pred` (a phi has an operand from each predecessor), `blockInv_of_point`,
  `point_succ'`, `runFrom_enter`, `jump_step`.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-! ## Operand maps -/

def _root_.Fe.Sonatina.Inst.mapOps (g : Operand → Operand) : Inst → Inst
  | .bin op a b => .bin op (g a) (g b)
  | .cmp op a b => .cmp op (g a) (g b)
  | .isZero a => .isZero (g a)
  | .not a => .not (g a)
  | .neg a => .neg (g a)
  | .clz a => .clz (g a)
  | .ctz a => .ctz (g a)
  | .ovf op a b => .ovf op (g a) (g b)
  | .sat op a b ty => .sat op (g a) (g b) ty
  | .cast op a ty => .cast op (g a) ty
  | .select c a b => .select (g c) (g a) (g b)
  | .evm op args => .evm op (args.map g)
  | .mload a ty => .mload (g a) ty
  | .mstore a v ty => .mstore (g a) (g v) ty
  | .memzero d l => .memzero (g d) (g l)
  | .malloc s => .malloc (g s)
  | .alloca ty => .alloca ty
  | .symAddr s => .symAddr s
  | .symSize s => .symSize s
  | .funcPtr f => .funcPtr f
  | .blackBox a => .blackBox (g a)
  | .insertValue a i v => .insertValue (g a) (g i) (g v)
  | .extractValue a i => .extractValue (g a) (g i)
  | .keccakWords ws => .keccakWords (ws.map g)
  | .call f args => .call f (args.map g)

def _root_.Fe.Sonatina.Stmt.mapOps (g : Operand → Operand) (s : Stmt) : Stmt :=
  ⟨s.dsts, s.inst.mapOps g⟩

def _root_.Fe.Sonatina.Term.mapOps (g : Operand → Operand) : Term → Term
  | .br c nz z => .br (g c) nz z
  | .brTable s d cs => .brTable (g s) d (cs.map fun c => (g c.1, c.2))
  | .ret vs => .ret (vs.map g)
  | .evmReturn a l => .evmReturn (g a) (g l)
  | .evmRevert a l => .evmRevert (g a) (g l)
  | .evmSelfDestruct a => .evmSelfDestruct (g a)
  | t => t

/-- A phi's first operand from block `p`, the one `enter` takes. -/
def inc (φ : Phi) (p : Nat) : Option Operand := (φ.incoming.find? (·.2 == p)).map (·.1)

/-! ## Following the input's run -/

/-- The output's computation `x'` against the input's remaining run `y`: from related worlds,
    `x'` diverges, or exits as `y` does, or returns `a` where `y` goes on as `y₁` with
    `Q a y₁`. -/
def Fol {α : Type} (Q : α → FeM (List Val) → Prop) (x' : FeM α) (y : FeM (List Val)) : Prop :=
  ∀ I w' w, WRel w' w → match x'.exec I w' with
    | none => True
    | some (.error e') => ∃ e, y.exec I w = some (.error e) ∧ ExitRel e' e
    | some (.ok (a, w₁')) => ∃ y₁ w₁, y.exec I w = y₁.exec I w₁ ∧ Q a y₁ ∧ WRel w₁' w₁

namespace Fol

variable {α β : Type}

theorem bind {Q : α → FeM (List Val) → Prop} {Q' : β → FeM (List Val) → Prop} {x' : FeM α}
    {k' : α → FeM β} {y : FeM (List Val)} (hx : Fol Q x' y)
    (hk : ∀ a y₁, Q a y₁ → Fol Q' (k' a) y₁) : Fol Q' (x' >>= k') y := by
  intro I w' w hw
  have h := hx I w' w hw
  rw [Fe.M.exec_bind]
  revert h
  rcases x'.exec I w' with _ | (e' | ⟨a, w₁'⟩)
  · intro _; trivial
  · exact id
  · rintro ⟨y₁, w₁, hy, hQ, hw₁⟩
    have h₂ := hk a y₁ hQ I w₁' w₁ hw₁
    revert h₂
    dsimp only
    rcases (k' a).exec I w₁' with _ | (e'' | ⟨b, w₂'⟩)
    · intro _; trivial
    · rintro ⟨e, he, hr⟩; exact ⟨e, hy.trans he, hr⟩
    · rintro ⟨y₂, w₂, hy₂, hQ', hw₂⟩; exact ⟨y₂, w₂, hy.trans hy₂, hQ', hw₂⟩

theorem approx {S : α → α → Prop} {Q : α → FeM (List Val) → Prop} {x' x : FeM α}
    {k : α → FeM (List Val)} (hx : Approx S x' x) (hk : ∀ a' a, S a' a → Q a' (k a)) :
    Fol Q x' (x >>= k) := by
  intro I w' w hw
  have h := hx I w' w hw
  rw [Fe.M.exec_bind]
  revert h
  rcases x'.exec I w' with _ | (e' | ⟨a', w₁'⟩) <;> rcases x.exec I w with _ | (e | ⟨a, w₁⟩) <;>
    simp only [ResRel, imp_self, IsEmpty.forall_iff]
  · intro h; exact ⟨e, rfl, h⟩
  · intro h; exact ⟨k a, w₁, rfl, hk a' a h.1, h.2⟩

theorem total {P : β → Prop} {Q : α → FeM (List Val) → Prop} {x' : FeM α} {x : FeM β}
    {k : β → FeM (List Val)} (hx : Total P x) (hk : ∀ b, P b → Fol Q x' (k b)) :
    Fol Q x' (x >>= k) := by
  intro I w' w hw
  obtain ⟨b, hb, hP⟩ := hx I w
  have e : (x >>= k).exec I w = (k b).exec I w := by rw [Fe.M.exec_bind, hb]
  have := hk b hP I w' w hw
  rw [e]; exact this

theorem congr {Q : α → FeM (List Val) → Prop} {x' : FeM α} {y y₂ : FeM (List Val)}
    (h : ∀ I w, y.exec I w = y₂.exec I w) (hy : Fol Q x' y₂) : Fol Q x' y := by
  intro I w' w hw
  have := hy I w' w hw
  rw [h]; exact this

theorem pure {Q : α → FeM (List Val) → Prop} {a : α} {y : FeM (List Val)} (h : Q a y) :
    Fol Q (Pure.pure a) y := by
  intro I w' w hw
  simp only [Fe.M.exec_pure]
  exact ⟨y, w, rfl, h, hw⟩

theorem stuck {Q : α → FeM (List Val) → Prop} {y : FeM (List Val)} : Fol Q Fe.Sonatina.stuck y := by
  intro I w' w _
  simp only [Fe.Sonatina.stuck, Fe.M.exec_diverge]

theorem mono {Q Q' : α → FeM (List Val) → Prop} {x' : FeM α} {y : FeM (List Val)}
    (h : Fol Q x' y) (hQ : ∀ a y₁, Q a y₁ → Q' a y₁) : Fol Q' x' y := by
  intro I w' w hw
  have := h I w' w hw
  revert this
  rcases x'.exec I w' with _ | (e' | ⟨a, w₁'⟩)
  · exact id
  · exact id
  · rintro ⟨y₁, w₁, hy, hq, hw₁⟩; exact ⟨y₁, w₁, hy, hQ _ _ hq, hw₁⟩

/-- What the output's computation returns also satisfies what it is known to return. -/
theorem strengthen {P : α → Prop} {Q : α → FeM (List Val) → Prop} {x' : FeM α}
    {y : FeM (List Val)} (h : Fol Q x' y) (hP : Returns P x') :
    Fol (fun a y₁ => Q a y₁ ∧ P a) x' y := by
  intro I w' w hw
  have := h I w' w hw
  have hP' : ∀ a w₁', x'.exec I w' = some (.ok (a, w₁')) → P a := fun a w₁' => hP I w' a w₁'
  revert this hP'
  rcases x'.exec I w' with _ | (e' | ⟨a, w₁'⟩)
  · exact fun h _ => h
  · exact fun h _ => h
  · rintro ⟨y₁, w₁, hy, hq, hw₁⟩ hP'; exact ⟨y₁, w₁, hy, ⟨hq, hP' a w₁' rfl⟩, hw₁⟩

end Fol

/-! ## Entering a block as an option -/

/-- `enter` as a pure computation: the phis' operands from `prev`, bound at once. -/
def enterOpt (env : Env) (prev : Option Nat) (b : Block) : Option Env :=
  (b.phis.mapM fun phi => prev >>= inc phi >>= opVal env) >>= fun vals =>
    if (b.phis.map fun phi => (phi.dst, phi.ty)).length == vals.length then
      some (((b.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)
    else none

theorem mapM_lift {α β : Type} (g : α → Option β) :
    ∀ l : List α, l.mapM (fun a => lift (g a)) = lift (l.mapM g)
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, mapM_lift g l]
    cases g a with
    | none => simp only [lift, stuck, Option.bind_eq_bind, Option.bind_none]; rfl
    | some b =>
      simp only [lift, pure_bind]
      cases l.mapM g <;> simp only [stuck, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, pure_bind] <;> rfl

theorem mapM_eq_lift {α β : Type} {F : α → FeM β} {g : α → Option β}
    (hF : ∀ a, F a = lift (g a)) (l : List α) : l.mapM F = lift (l.mapM g) := by
  rw [← mapM_lift]; congr 1; funext a; exact hF a

theorem enter_eq (env : Env) (prev : Option Nat) (b : Block) :
    enter env prev b = lift (enterOpt env prev b) := by
  unfold enter enterOpt
  rw [mapM_eq_lift (g := fun phi => prev >>= inc phi >>= opVal env) ?hF, lift_bind]
  case hF =>
    intro phi
    cases prev with
    | none => rfl
    | some p =>
      simp only [inc, Option.bind_eq_bind, Option.bind_some]
      cases phi.incoming.find? (·.2 == p) with
      | none => rfl
      | some x => rcases x with ⟨o, q⟩; simp only [Option.map_some, Option.bind_some, evalOperand_eq]
  cases b.phis.mapM fun phi => prev >>= inc phi >>= opVal env with
  | none => rfl
  | some vals =>
    simp only [Option.bind_eq_bind, Option.bind_some, Fe.Sonatina.bind]
    split
    · rw [foldl_bindStep (fun e x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl)]; rfl
    · rfl

theorem mapM_option_forall₂ {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM g = some vs → List.Forall₂ (fun a b => g a = some b) l vs
  | [], vs, h => by simp at h; subst h; exact .nil
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h
    rcases ha : g a with _ | b
    · rw [ha] at h; simp at h
    rcases hl : l.mapM g with _ | bs
    · rw [ha, hl] at h; simp at h
    rw [ha, hl] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .cons ha (mapM_option_forall₂ hl)

theorem mapM_option_of_forall {α β : Type} {g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (g a).isSome = true) → ∃ vs, l.mapM g = some vs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    obtain ⟨bs, hbs⟩ := mapM_option_of_forall (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl⟩

/-! ## Bindings -/

theorem fold_get_not : ∀ (l : List ((Nat × Ty) × Val)) (env : Env) (k : Nat),
    k ∉ l.map (·.1.1) → (l.foldl bindStep env)[k]? = env[k]?
  | [], _, _, _ => rfl
  | x :: l, env, k, h => by
    rw [List.foldl_cons, fold_get_not l _ k (fun hm => h (List.mem_cons_of_mem _ hm))]
    unfold bindStep; rw [env_insert_get]
    have : x.1.1 ≠ k := fun e => h (e ▸ List.mem_cons_self ..)
    simp [this]

theorem fold_get_mem : ∀ (l : List ((Nat × Ty) × Val)) (env : Env), (l.map (·.1.1)).Nodup →
    ∀ x ∈ l, (l.foldl bindStep env)[x.1.1]? = some (x.2.as x.1.2)
  | [], _, _, _, hx => nomatch hx
  | y :: l, env, hn, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [fold_get_not l _ _ hn.1]; unfold bindStep; rw [env_insert_get]; simp
    · exact fold_get_mem l _ hn.2 x hx

theorem fold_get_cases : ∀ (l : List ((Nat × Ty) × Val)) (env : Env) (k : Nat) (v : Val),
    (l.foldl bindStep env)[k]? = some v →
      (∃ x ∈ l, x.1.1 = k ∧ v = x.2.as x.1.2) ∨ (env[k]? = some v ∧ k ∉ l.map (·.1.1))
  | [], _, _, _, h => Or.inr ⟨h, fun hm => nomatch hm⟩
  | x :: l, env, k, v, h => by
    rw [List.foldl_cons] at h
    rcases fold_get_cases l _ k v h with ⟨y, hy, hk, hv⟩ | ⟨he, hk⟩
    · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hk, hv⟩
    · unfold bindStep at he; rw [env_insert_get] at he
      split at he
      · next hx => simp only [Option.some.injEq] at he
                   exact Or.inl ⟨x, List.mem_cons_self .., hx, he.symm⟩
      · next hx =>
        refine Or.inr ⟨he, fun hm => ?_⟩
        rcases List.mem_cons.mp hm with e | hm
        · exact hx e.symm
        · exact hk hm

theorem EnvSub.fold {env' env : Env} (h : EnvSub env' env) :
    ∀ l : List ((Nat × Ty) × Val), EnvSub (l.foldl bindStep env') (l.foldl bindStep env)
  | [] => h
  | x :: l => by
    rw [List.foldl_cons, List.foldl_cons]
    refine EnvSub.fold (fun k v hv => ?_) l
    unfold bindStep at hv ⊢; rw [env_insert_get] at hv ⊢
    by_cases hx : x.1.1 = k <;> simp only [hx, ↓reduceIte] at hv ⊢
    · exact hv
    · exact h k v hv

/-- A word value is its own `i256`. -/
theorem as_word {v : Val} {n : Nat} (hv : v = .int 256 n) (hn : n < 2 ^ 256) :
    v.as (.int 256) = v := by
  subst hv; simp only [Val.as, Ty.bits]; rw [Nat.mod_eq_of_lt hn]

/-! ## Unique definitions -/

theorem nodup_fst_fun {α β : Type} : ∀ {l : List (α × β)}, (l.map (·.1)).Nodup →
    ∀ {a : α} {b₁ b₂ : β}, (a, b₁) ∈ l → (a, b₂) ∈ l → b₁ = b₂
  | [], _, _, _, _, h, _ => nomatch h
  | x :: l, hn, a, b₁, b₂, h₁, h₂ => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h₁ with e₁ | h₁ <;> rcases List.mem_cons.mp h₂ with e₂ | h₂
    · rw [← e₁] at e₂; exact (Prod.mk.inj e₂).2.symm
    · exact absurd (e₁ ▸ List.mem_map_of_mem (f := (·.1)) h₂) hn.1
    · exact absurd (e₂ ▸ List.mem_map_of_mem (f := (·.1)) h₁) hn.1
    · exact nodup_fst_fun hn.2 h₁ h₂

/-- The definitions of `f` are unique: what `ssa` checks first. -/
def UniqueDefs (f : Func) : Prop := ((defList f).map (·.1)).Nodup

theorem UniqueDefs.of_ssa {f : Func} {T : DomTree} (h : ssa f T = true) : UniqueDefs f := by
  unfold ssa at h
  simp only [Bool.and_eq_true] at h
  exact distinct_nodup h.1

theorem UniqueDefs.fn {f : Func} (h : UniqueDefs f) {v : Nat} {d₁ d₂ : Def}
    (h₁ : (v, d₁) ∈ defList f) (h₂ : (v, d₂) ∈ defList f) : d₁ = d₂ := nodup_fst_fun h h₁ h₂

theorem phi_def {f : Func} {b : Block} (hb : b ∈ f.blocks) {φ : Phi} (hφ : φ ∈ b.phis) :
    (φ.dst, Def.phi b.id) ∈ defList f := by
  simp only [defList, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨b, hb, Or.inl ⟨φ, hφ, rfl⟩⟩

theorem stmt_def {f : Func} {b : Block} (hb : b ∈ f.blocks) {k : Nat} {s : Stmt}
    (hs : b.body[k]? = some s) {d : Nat × Ty} (hd : d ∈ s.dsts) :
    (d.1, Def.stmt b.id k) ∈ defList f := by
  simp only [defList, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨b, hb, Or.inr ⟨(s, k), List.mem_zipIdx_iff_getElem?.mpr hs, d, hd, rfl⟩⟩

theorem param_def {f : Func} {p : Nat × Ty} (hp : p ∈ f.params) : (p.1, Def.param) ∈ defList f := by
  simp only [defList, List.mem_append, List.mem_map]
  exact Or.inl ⟨p, hp, rfl⟩

theorem definedIn_def {f : Func} {d v : Nat} (h : DefinedIn f d v) :
    (v, Def.phi d) ∈ defList f ∨ ∃ j, (v, Def.stmt d j) ∈ defList f := by
  obtain ⟨blk, hb, hv⟩ := h
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = d := by simpa using List.find?_some hb
  rcases hv with hphi | ⟨s, hs, hvs⟩
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hphi
    exact Or.inl (hid ▸ phi_def hmem hφ)
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    obtain ⟨dd, hdd, rfl⟩ := List.mem_map.mp hvs
    exact Or.inr ⟨j, hid ▸ stmt_def hmem hj hdd⟩

theorem sublist_flatMap {α β : Type} {g : α → List β} {a : α} {l : List α} (h : a ∈ l) :
    (g a).Sublist (l.flatMap g) := by
  rw [List.flatMap]; exact List.sublist_flatten_of_mem (List.mem_map_of_mem h)

/-- The phis of a block bind distinct values. -/
theorem UniqueDefs.phis {f : Func} (h : UniqueDefs f) {b : Block} (hb : b ∈ f.blocks) :
    (b.phis.map (·.dst)).Nodup := by
  refine List.Nodup.sublist ?_ h
  have e : b.phis.map (·.dst) =
      (b.phis.map fun phi => (phi.dst, Def.phi b.id)).map (·.1) := by simp
  rw [e]
  refine List.Sublist.map _ ?_
  unfold defList
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact (List.sublist_append_left _ _).trans (sublist_flatMap (g := fun b : Block =>
    b.phis.map (fun phi => (phi.dst, Def.phi b.id)) ++
      b.body.zipIdx.flatMap fun sk => sk.1.dsts.map fun d => (d.1, Def.stmt b.id sk.2)) hb)

/-- The results of a statement are distinct. -/
theorem UniqueDefs.dsts {f : Func} (h : UniqueDefs f) {b : Block} (hb : b ∈ f.blocks) {k : Nat}
    {s : Stmt} (hs : b.body[k]? = some s) : (s.dsts.map (·.1)).Nodup := by
  refine List.Nodup.sublist ?_ h
  have e : s.dsts.map (·.1) = (s.dsts.map fun d => (d.1, Def.stmt b.id k)).map (·.1) := by simp
  rw [e]
  refine List.Sublist.map _ ?_
  unfold defList
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  refine List.Sublist.trans ?_ (sublist_flatMap (g := fun b : Block =>
    b.phis.map (fun phi => (phi.dst, Def.phi b.id)) ++
      b.body.zipIdx.flatMap fun sk => sk.1.dsts.map fun d => (d.1, Def.stmt b.id sk.2)) hb)
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact sublist_flatMap (g := fun sk : Stmt × Nat => sk.1.dsts.map fun d => (d.1, Def.stmt b.id sk.2))
    (List.mem_zipIdx_iff_getElem?.mpr hs : (s, k) ∈ b.body.zipIdx)

/-! ## The tree is antisymmetric -/

/-- Climb `n` steps of the tree from `b`. -/
def DomTree.climb (T : DomTree) : Nat → Nat → Option Nat
  | 0, b => some b
  | n + 1, b => (T.idom.find? b).bind (T.climb n)

theorem DomTree.Anc.climb {T : DomTree} {d b : Nat} (h : T.Anc d b) : ∃ n, T.climb n b = some d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step hp _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [DomTree.climb, hp, Option.bind_some, hn]⟩

theorem DomTree.climb_add (T : DomTree) : ∀ m n b, T.climb (m + n) b = (T.climb m b).bind (T.climb n)
  | 0, n, b => by simp [DomTree.climb]
  | m + 1, n, b => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [DomTree.climb]
    cases T.idom.find? b with
    | none => rfl
    | some p => simp only [Option.bind_some]; exact DomTree.climb_add T m n p

theorem DomTree.climb_mul {T : DomTree} {p b : Nat} (h : T.climb p b = some b) :
    ∀ i, T.climb (p * i) b = some b
  | 0 => by simp [DomTree.climb]
  | i + 1 => by
    rw [Nat.mul_succ, DomTree.climb_add, DomTree.climb_mul h i, Option.bind_some, h]

theorem DomTree.climb_none {T : DomTree} {m b e : Nat} (h : T.climb m b = some e)
    (he : T.idom.find? e = none) : ∀ r, T.climb (m + 1 + r) b = none := by
  intro r
  rw [DomTree.climb_add, DomTree.climb_add, h]
  simp [DomTree.climb, he]

/-- Ancestry in a tree whose root, an ancestor of the block, has no immediate dominator is
    antisymmetric. -/
theorem DomTree.anc_antisymm {T : DomTree} {e a b : Nat} (hroot : T.idom.find? e = none)
    (hb : T.Anc e b) (h₁ : T.Anc a b) (h₂ : T.Anc b a) : a = b := by
  obtain ⟨k, hk⟩ := h₁.climb
  obtain ⟨j, hj⟩ := h₂.climb
  obtain ⟨m, hm⟩ := hb.climb
  have hc : T.climb (k + j) b = some b := by rw [DomTree.climb_add, hk, Option.bind_some, hj]
  by_cases hp : k + j = 0
  · have : k = 0 := by omega
    subst this
    simp only [DomTree.climb, Option.some.injEq] at hk
    exact hk.symm
  · have hlt : m + 1 ≤ (k + j) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have := DomTree.climb_mul hc (m + 1)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hlt
    rw [hr, DomTree.climb_none hm hroot r] at this
    cases this

/-! ## Operands rewritten to equal values -/

theorem mapM_map_eq {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {g : α → α} {F : α → m β} :
    ∀ {l : List α}, (∀ a ∈ l, F (g a) = F a) → (l.map g).mapM F = l.mapM F
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_map_eq fun x hx => h x (List.mem_cons_of_mem _ hx)]

section congr

variable {env : Env} {g : Operand → Operand}

theorem ev_congr {o : Operand} (h : opVal env (g o) = opVal env o) :
    evalOperand env (g o) = evalOperand env o ∧ evalInt env (g o) = evalInt env o ∧
      evalWord env (g o) = evalWord env o := by
  have hi : evalInt env (g o) = evalInt env o := by
    rw [evalInt_eq, evalInt_eq]; unfold intVal; rw [h]
  exact ⟨by rw [evalOperand_eq, evalOperand_eq, h], hi, by unfold evalWord; rw [hi]⟩

theorem runInst_mapOps (c : Ctx) (i : Inst) (h : ∀ o ∈ i.args, opVal env (g o) = opVal env o) :
    runInst c env (i.mapOps g) = runInst c env i := by
  have E := fun o ho => ev_congr (env := env) (g := g) (o := o) (h o ho)
  cases i
  case evm op args =>
    simp only [Inst.mapOps, runInst]
    rw [mapM_map_eq (l := args) fun o ho => (E o ho).2.2]
  case keccakWords ws =>
    simp only [Inst.mapOps, runInst]
    rw [mapM_map_eq (l := ws) fun o ho => (E o ho).2.2]
  case call => rfl
  case select c a b =>
    simp only [Inst.args, List.forall_mem_cons, List.forall_mem_nil, and_true] at E
    simp only [Inst.mapOps, runInst, E.1.2.1]
    congr 1; funext x; rcases x with ⟨_, n⟩
    cases hc : (n != 0) <;> simp only [Bool.false_eq_true, ↓reduceIte, E.2.1.1, E.2.2.1]
  all_goals simp only [Inst.args, List.forall_mem_cons, List.forall_mem_nil, and_true,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true] at E
  all_goals simp only [Inst.mapOps, runInst, evalPair, E]

theorem runStmtO_mapOps (o : Oracle) (c : Ctx) (s : Stmt)
    (h : ∀ a ∈ s.inst.args, opVal env (g a) = opVal env a) :
    runStmtO o c env (s.mapOps g) = runStmtO o c env s := by
  rcases s with ⟨dsts, inst⟩
  cases inst
  case call callee args =>
    simp only [runStmtO, Stmt.mapOps, Inst.mapOps]
    rw [mapM_map_eq (l := args) fun a ha => (ev_congr (h a ha)).1]
  all_goals exact runInst_mapOps c _ h

theorem _root_.Fe.Sonatina.Term.args_mapOps (g : Operand → Operand) (t : Term) :
    (t.mapOps g).args = t.args.map g := by
  cases t <;> simp [Term.mapOps, Term.args]

theorem runTerm_mapOps (t : Term) (h : ∀ o ∈ t.args, opVal env (g o) = opVal env o) :
    runTerm env (t.mapOps g) = runTerm env t := by
  have E := fun o ho => ev_congr (env := env) (g := g) (o := o) (h o ho)
  cases t
  case brTable s d cs =>
    simp only [Term.args, List.forall_mem_cons] at E
    simp only [Term.mapOps, runTerm, E.1.2.1]
    rw [mapM_map_eq (g := fun c => (g c.1, c.2)) fun cse hc => ?_]
    rcases cse with ⟨o, dest⟩
    dsimp only
    rw [(E.2 o (List.mem_map_of_mem (f := (·.1)) hc)).2.1]
  case ret vs =>
    simp only [Term.mapOps, runTerm]
    rw [mapM_map_eq (l := vs) fun o ho => (E o ho).1]
  all_goals simp only [Term.args, List.forall_mem_cons, List.forall_mem_nil, and_true,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true] at E
  all_goals simp only [Term.mapOps, runTerm, E]

end congr

/-- A statement run in an environment that binds less approximates it in the larger one. -/
theorem Approx.runStmtO_sub {o : Oracle} (ho : Oracle.Mono o) {c : Ctx} {env' env : Env}
    (h : EnvSub env' env) (he : EnvInt env) (s : Stmt) (hs : s.inst.machine = true) :
    Approx Eq (runStmtO o c env' s) (runStmtO o c env s) := by
  unfold runStmtO
  split
  · next callee args heq =>
    rw [heq] at hs
    exact Approx.bind (Approx.strengthen (Approx.mapM' (Approx.evalOperand h) _)
      (returns_evalOperands he _)) fun a a₀ ⟨e, hv⟩ => by
        cases e; exact ho _ _ hv
  · exact Approx.runInst h rfl _ hs

/-! ## Phis have an operand from each predecessor -/

theorem predFold_keep {id : Nat} : ∀ (l : List Nat) (m : NatMap (List Nat)) {t x : Nat},
    x ∈ (m.find? t).getD [] →
      x ∈ ((l.foldl (fun m s => m.insert s (id :: (m.find? s).getD [])) m).find? t).getD []
  | [], _, _, _, h => h
  | s :: l, m, t, x, h => by
    rw [List.foldl_cons]
    refine predFold_keep l _ ?_
    rw [NatMap.find?_insert]
    split
    · next e => subst e; exact List.mem_cons_of_mem _ h
    · exact h

theorem predFold_mem {id : Nat} : ∀ (l : List Nat) (m : NatMap (List Nat)) {t : Nat}, t ∈ l →
    id ∈ ((l.foldl (fun m s => m.insert s (id :: (m.find? s).getD [])) m).find? t).getD []
  | s :: l, m, t, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact predFold_keep l _ (by rw [NatMap.find?_insert, if_pos rfl]; exact List.mem_cons_self ..)
    · exact predFold_mem l _ h

theorem predMap_keep : ∀ (bs : List Block) (m : NatMap (List Nat)) {t x : Nat},
    x ∈ (m.find? t).getD [] → x ∈ ((bs.foldl (fun m b => b.term.succs.foldl
      (fun m s => m.insert s (b.id :: (m.find? s).getD [])) m) m).find? t).getD []
  | [], _, _, _, h => h
  | b :: bs, m, t, x, h => by
    rw [List.foldl_cons]; exact predMap_keep bs _ (predFold_keep _ _ h)

theorem predMap_mem : ∀ (bs : List Block) (m : NatMap (List Nat)) {qb : Block} {t : Nat},
    qb ∈ bs → t ∈ qb.term.succs → qb.id ∈ ((bs.foldl (fun m b => b.term.succs.foldl
      (fun m s => m.insert s (b.id :: (m.find? s).getD [])) m) m).find? t).getD []
  | b :: bs, m, qb, t, hq, ht => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact predMap_keep bs _ (predFold_mem _ _ ht)
    · exact predMap_mem bs _ hq ht

/-- Entering a block of a well-formed function from a predecessor, each phi has an operand. -/
theorem phi_has_pred {sig : Sigs} {syms : List String} {f : Func} (hwf : f.wf sig syms = true)
    {q b : Nat} {qb blk : Block} (hqb : f.block? q = some qb) (hb : b ∈ qb.term.succs)
    (hblk : f.block? b = some blk) : ∀ φ ∈ blk.phis, (inc φ q).isSome = true := by
  intro φ hφ
  have hqm := List.mem_of_find?_eq_some hqb
  have hqid : qb.id = q := by simpa using List.find?_some hqb
  have hbm := List.mem_of_find?_eq_some hblk
  have hbid : blk.id = b := by simpa using List.find?_some hblk
  unfold Func.wf at hwf
  simp only [Bool.and_eq_true] at hwf
  have hc := hwf.1.2
  unfold Func.cfgOk at hc
  split at hc
  · cases hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  have hφc := (hc.2 blk hbm).2 φ hφ
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hφc
  have hp : q ∈ ((predMap f).find? blk.id).getD [] := by
    rw [hbid, ← hqid]; exact predMap_mem _ _ hqm hb
  obtain ⟨⟨o, q'⟩, hm, hq'⟩ := List.mem_map.mp (hφc.2 q hp)
  simp only at hq'
  subst hq'
  unfold inc
  rw [Option.isSome_map]
  exact List.find?_isSome.mpr ⟨(o, q'), hm, by simp⟩

/-- From the point at the end of a reachable block, the block state of one of its successors. -/
theorem blockInv_of_point {f : Func} {T : DomTree} (hv : T.valid f = true) {env : Env}
    {b : Nat} {blk : Block} (hb : f.block? b = some blk) (hr : (T.reach.find? b).isSome = true)
    (hpi : PointInv f T b blk.body.length env) {d : Nat} (hd : d ∈ blk.term.succs) :
    BlockInv f T (env, some b, d) := by
  obtain ⟨hw, hdom⟩ := hpi
  have hedge : Edge f b d := ⟨blk, hb, hd⟩
  refine ⟨hw, fun p hp => hdom p.1 (Or.inl (List.mem_map_of_mem hp)),
    (DomTree.valid_edge hv hr hedge).1, hr, hedge, fun d' v ha hdef => ?_⟩
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

/-- A value's definition, from a definition of it as a phi or statement of block `d`. -/
theorem phi_of_definedIn {f : Func} (hu : UniqueDefs f) {d B v : Nat} (h : DefinedIn f d v)
    (hB : (v, Def.phi B) ∈ defList f) : d = B := by
  rcases definedIn_def h with h | ⟨j, h⟩
  · exact Def.phi.inj (hu.fn h hB)
  · cases hu.fn h hB

/-- A phi operand of block `b`'s phi from reachable `q` that is a phi `u` of block `Bu`: `Bu` is
    an ancestor-or-self of `q`. -/
theorem phiUse_anc {sig : Sigs} {syms : List String} {f : Func} (hwf : f.wf sig syms = true)
    {T : DomTree} (hs : ssa f T = true) {b : Nat} {blk : Block} (hb : f.block? b = some blk)
    (hr : (T.reach.find? b).isSome = true) {q : Nat} (hq : (T.reach.find? q).isSome = true)
    {φ : Phi} (hφ : φ ∈ blk.phis) {u : Nat} (hm : (Operand.var u, q) ∈ φ.incoming) {Bu : Nat}
    (hBu : (u, Def.phi Bu) ∈ defList f) : T.Anc Bu q := by
  have hu := UniqueDefs.of_ssa hs
  have hmem := List.mem_of_find?_eq_some hb
  have hid : blk.id = b := by simpa using List.find?_some hb
  have huse := (ssa_block hs hmem (hid ▸ hr)).1 φ hφ _ hm hq
  rcases phiUseOk_sound (Func.wf_ids hwf) huse with hp | ⟨d, ha, hdef⟩
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
    cases hu.fn (param_def hp') hBu
  · exact phi_of_definedIn hu hdef hBu ▸ ha

theorem forall₂_zip_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {vs : List β}, List.Forall₂ R l vs → ∀ {a : α}, a ∈ l →
      ∃ b, (a, b) ∈ l.zip vs ∧ R a b
  | _, _, .nil, _, h => nomatch h
  | x :: _, y :: _, .cons hr hl, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hR⟩ := forall₂_zip_of_mem hl h
      exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

theorem inc_mem {φ : Phi} {q : Nat} {o : Operand} (h : inc φ q = some o) : (o, q) ∈ φ.incoming := by
  unfold inc at h
  obtain ⟨⟨o', q'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hq : q' = q := by simpa using List.find?_some hf
  subst hq
  exact List.mem_of_find?_eq_some hf

/-- The keys `enter` binds: the phis' values. -/
theorem enter_keys {phis : List Phi} {vals : List Val}
    (h : (phis.map fun phi => (phi.dst, phi.ty)).length = vals.length) :
    ((phis.map fun phi => (phi.dst, phi.ty)).zip vals).map (·.1.1) = phis.map (·.dst) := by
  have : ((phis.map fun phi => (phi.dst, phi.ty)).zip vals).map (·.1) =
      phis.map fun phi => (phi.dst, phi.ty) := List.map_fst_zip (by omega)
  calc ((phis.map fun phi => (phi.dst, phi.ty)).zip vals).map (·.1.1)
      = (((phis.map fun phi => (phi.dst, phi.ty)).zip vals).map (·.1)).map (·.1) := by
        rw [List.map_map]; rfl
    _ = phis.map (·.dst) := by rw [this, List.map_map]; rfl

/-- What `enter` binds a phi to: its operand from `q`, as its type. -/
theorem enter_val {env : Env} {q : Nat} {phis : List Phi} {vals : List Val}
    (hF2 : List.Forall₂ (fun phi v => (some q >>= inc phi >>= opVal env) = some v) phis vals)
    (hlen : (phis.map fun phi => (phi.dst, phi.ty)).length = vals.length)
    (hnd : (phis.map (·.dst)).Nodup) {φ : Phi} (hφ : φ ∈ phis) :
    ∃ o v, inc φ q = some o ∧ opVal env o = some v ∧
      (((phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env)[φ.dst]? =
        some (v.as φ.ty) := by
  obtain ⟨v, hz, hR⟩ := forall₂_zip_of_mem hF2 hφ
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hR
  obtain ⟨o, ho, hv⟩ := hR
  refine ⟨o, v, ho, hv, ?_⟩
  have hm : ((φ.dst, φ.ty), v) ∈ (phis.map fun phi => (phi.dst, phi.ty)).zip vals := by
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨(φ, v), hz, rfl⟩
  have := fold_get_mem _ env (by rw [enter_keys hlen]; exact hnd) _ hm
  exact this

/-- `enterOpt`'s result: the fold of the phis' values. -/
theorem enterOpt_spec {env : Env} {prev : Option Nat} {blk : Block} {e₁ : Env}
    (h : enterOpt env prev blk = some e₁) :
    ∃ vals, List.Forall₂ (fun phi v => (prev >>= inc phi >>= opVal env) = some v) blk.phis vals ∧
      (blk.phis.map fun phi => (phi.dst, phi.ty)).length = vals.length ∧
      e₁ = ((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env := by
  unfold enterOpt at h
  rcases hv : blk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env) with _ | vals
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq] at h
    exact ⟨vals, mapM_option_forall₂ hv, by simpa using hl, h.symm⟩
  · cases h

theorem wf_imm_word {o : Operand} (h : o.wf = true) {env : Env} {v : Val} (hv : opVal env o = some v)
    (hnv : ∀ u, o ≠ .var u) : ∃ n, n < 2 ^ 256 ∧ v = .int 256 n := by
  cases o with
  | var u => exact absurd rfl (hnv u)
  | imm bits n =>
    simp only [Operand.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [opVal, Option.some.injEq] at hv
    obtain ⟨rfl, hn⟩ := h
    exact ⟨n, hn, hv.symm⟩

/-- A world, for runs that do not depend on one. -/
def someWorld : World := { accounts := default, logs := default }

theorem returns_lift_some {α : Type} {P : α → Prop} {a : α} (h : Returns P (Steps.lift (some a))) :
    P a :=
  h default someWorld a someWorld (by simp only [Steps.lift, Fe.M.exec_pure])

/-- The output's environment binds only values of the output. -/
def DomSub (f' : Func) (env : Env) : Prop :=
  ∀ k, (env[k]?).isSome = true → ((defsOf f').find? k).isSome = true

theorem defsOf_isSome {f : Func} {k : Nat} {d : Def} (h : (k, d) ∈ defList f) :
    ((defsOf f).find? k).isSome = true := by
  rw [defsOf, NatMap.find?_ofList, List.lookup_isSome_iff]
  exact ⟨(k, d), h, by simp⟩

/-- The rest of the input's run after entering block `b`, `cb`. -/
def inRun (o : Oracle) (c : Ctx) (f : Func) (b : Nat) (cb : Block) (e : Env) : FeM (List Val) :=
  runBodyO o c e cb.body >>= fun e => runTerm e cb.term >>= fun
    | .goto e d => runFrom o c f (e, some b, d)
    | .done v => pure v

theorem bind_rel (e' e : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    Approx (fun a' a => dsts.length = vals.length ∧ a' = (dsts.zip vals).foldl bindStep e' ∧
        a = (dsts.zip vals).foldl bindStep e)
      (Fe.Sonatina.bind e' dsts vals) (Fe.Sonatina.bind e dsts vals) := by
  unfold Fe.Sonatina.bind
  by_cases hl : (dsts.length == vals.length) = true
  · simp only [hl, ↓reduceIte]
    exact Approx.pure ⟨by simpa using hl,
      foldl_bindStep (fun _ x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl) _ _,
      foldl_bindStep (fun _ x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl) _ _⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte]
    exact Approx.stuck _

theorem Approx.pure_left {α : Type} {S : α → α → Prop} {a' : α} {x : FeM α}
    (h : Approx S (Pure.pure a') x) : Approx (fun b' b => S b' b ∧ b' = a') (Pure.pure a') x := by
  intro I w' w hw
  have := h I w' w hw
  revert this
  rw [Fe.M.exec_pure]
  rcases x.exec I w with _ | (_ | ⟨a, w₁⟩)
  · exact id
  · exact id
  · exact fun h => ⟨⟨h.1, rfl⟩, h.2⟩

section run

variable {f : Func}

theorem runFrom_enter (o : Oracle) (c : Ctx) {b : Nat} {cb : Block} (hb : f.block? b = some cb)
    (env : Env) (prev : Option Nat) :
    runFrom o c f (env, prev, b) = enter env prev cb >>= inRun o c f b cb := by
  unfold runFrom inRun
  rw [runBlocksO]
  simp only [stepBlock, hb, bind_assoc]
  rfl

/-- Entering a block the input reaches from a predecessor: its phis all have values. -/
theorem enter_total {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true) {T : DomTree}
    (hs : ssa f T = true) {env : Env} {q b : Nat} (hi : BlockInv f T (env, some q, b))
    {blk : Block} (hb : f.block? b = some blk) : ∃ e₁, enterOpt env (some q) blk = some e₁ := by
  have hdef := phis_defined hwf hs hi hb
  obtain ⟨_, _, _, _, ⟨qb, hqb, hsucc⟩, _⟩ := hi
  obtain ⟨vals, hv⟩ := mapM_option_of_forall (g := fun phi => some q >>= inc phi >>= opVal env)
    (l := blk.phis) fun φ hφ => by
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (phi_has_pred hwf hqb hsucc hb φ hφ)
      obtain ⟨n, hn⟩ := hdef φ hφ (o, q) (inc_mem ho) rfl
      simp only [Option.bind_eq_bind, Option.bind_some, ho]
      unfold intVal at hn
      revert hn
      cases opVal env o <;> simp
  have hlen := (mapM_option_forall₂ hv).length_eq
  refine ⟨((blk.phis.map fun phi => (phi.dst, phi.ty)).zip vals).foldl bindStep env, ?_⟩
  unfold enterOpt
  rw [hv]
  simp only [Option.bind_eq_bind, Option.bind_some, List.length_map, hlen, beq_self_eq_true,
    ↓reduceIte]

/-- The input's step through a block with no statements that jumps. -/
theorem jump_step (o : Oracle) (c : Ctx) {env : Env} {r t t₂ : Nat} {tb : Block}
    (htb : f.block? t = some tb) (hbody : tb.body = []) (hterm : tb.term = .jump t₂) {e₂ : Env}
    (he : enterOpt env (some r) tb = some e₂) (I : ExecutionEnv) (w : World) :
    (runFrom o c f (env, some r, t)).exec I w = (runFrom o c f (e₂, some t, t₂)).exec I w := by
  apply runFrom_goto
  show (stepBlock o c f env (some r) t).exec I w = _
  simp only [stepBlock, htb, enter_eq, he, lift, pure_bind, hbody, runBodyO, hterm, runTerm,
    Fe.M.exec_pure]

/-- A phi operand's value is a word. -/
theorem phi_val_word {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true) {blk : Block}
    (hb : blk ∈ f.blocks) {φ : Phi} (hφ : φ ∈ blk.phis) {o : Operand} {q : Nat}
    (ho : (o, q) ∈ φ.incoming) {env : Env} (hw : EnvW env) {v : Val} (hv : opVal env o = some v) :
    v.as (.int 256) = v := by
  by_cases hvar : ∃ u, o = .var u
  · obtain ⟨u, rfl⟩ := hvar
    obtain ⟨n, hn, e⟩ := hw u v hv
    exact as_word e hn
  · obtain ⟨n, hn, e⟩ := wf_imm_word ((Func.wf_operands hwf hb).1 φ hφ _ ho) hv
      fun u h => hvar ⟨u, h⟩
    exact as_word e hn

theorem point_succ' {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true) {T : DomTree}
    {b k : Nat} {blk : Block} (hb : f.block? b = some blk) {s : Stmt} (hs : blk.body[k]? = some s)
    {env : Env} (hpi : PointInv f T b k env) {vals : List Val} (hv : IntVals vals)
    (hl : s.dsts.length = vals.length) :
    PointInv f T b (k + 1) ((s.dsts.zip vals).foldl bindStep env) := by
  obtain ⟨hw, hdom⟩ := hpi
  have hmem := List.mem_of_find?_eq_some hb
  have hsm : s ∈ blk.body := List.mem_of_getElem? hs
  have htys := ((Func.wf_words hwf).2 blk hmem).2 s hsm
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

theorem entry_phis {sig : Sigs} {syms : List String} (hwf : f.wf sig syms = true) {e : Block}
    (he : f.blocks.head? = some e) : e.phis = [] := by
  unfold Func.wf at hwf
  simp only [Bool.and_eq_true] at hwf
  have hc := hwf.1.2
  unfold Func.cfgOk at hc
  rw [he] at hc
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
  exact hc.1.1

end run

end Fe.Sonatina.Steps
