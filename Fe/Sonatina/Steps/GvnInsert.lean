import Fe.Sonatina.Steps.LowerSwitchesSound
import Fe.Sonatina.Steps.GvnRewrite

/-!
# Inserting unused phis

`insPhis f news` prepends `news[i]` to the phis of `f`'s `i`-th block.  When the new phis' results
are no value `f` mentions (`insOk`), the function with them approximates `f`: block for block, its
environment agrees with `f`'s on every value `f` mentions (`LSCtx.Agree` over `funcVars f`); it
binds the new phis besides, or is stuck where one's operand is unbound.  The well-formedness of
the result follows from `f`'s and `insOk`'s checks.
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum Fe Fe.EVM Fe.Sonatina.Steps

variable {sig : Sigs} {syms : List String}

/-- A block with phis prepended. -/
abbrev withPhis (bn : Block × List Phi) : Block := { bn.1 with phis := bn.2 ++ bn.1.phis }

theorem find_ins {b : Nat} : ∀ (l : List Block) (ns : List (List Phi)), ns.length = l.length →
    (l.find? (·.id == b) = none ∧ ((l.zip ns).map withPhis).find? (·.id == b) = none) ∨
    ∃ bk nw, l.find? (·.id == b) = some bk ∧ nw ∈ ns ∧
      ((l.zip ns).map withPhis).find? (·.id == b) = some (withPhis (bk, nw))
  | [], [], _ => Or.inl ⟨rfl, rfl⟩
  | x :: l, n :: ns, hl => by
    simp only [List.zip_cons_cons, List.map_cons]
    by_cases hx : (x.id == b) = true
    · right
      have hw : ((withPhis (x, n)).id == b) = true := by simpa [withPhis] using hx
      refine ⟨x, n, by simp only [List.find?_cons, hx], List.mem_cons_self .., ?_⟩
      simp only [List.find?_cons, hw]
    · have hx' : (x.id == b) = false := by simpa using hx
      simp only [List.find?_cons, hx']
      rcases find_ins l ns (by simpa using hl) with h | ⟨bk, nw, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨bk, nw, h1, List.mem_cons_of_mem _ h2, h3⟩
  | [], _ :: _, hl | _ :: _, [], hl => by simp at hl

theorem insPhis_block {f : Func} {news : List (List Phi)} (hl : news.length = f.blocks.length)
    (b : Nat) : ((insPhis f news).block? b = none ∧ f.block? b = none) ∨
    ∃ bk nw, f.block? b = some bk ∧ nw ∈ news ∧
      (insPhis f news).block? b = some { bk with phis := nw ++ bk.phis } := by
  rcases find_ins f.blocks news hl (b := b) with ⟨h1, h2⟩ | ⟨bk, nw, h1, h2, h3⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨bk, nw, h1, h2, h3⟩

/-- What `insOk` checks. -/
theorem insOk_spec {f : Func} {news : List (List Phi)} (h : insOk f news = true) :
    news.length = f.blocks.length ∧ (∀ nw ∈ news, ∀ φ ∈ nw, φ.dst ∉ funcVars f ∧
      ∀ p ∈ φ.incoming, p.1.wf = true) ∧ (insPhis f news).cfgOk = true ∧
      (insPhis f news).wordTyped = true := by
  simp only [insOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hl, hn⟩, hc⟩, hw⟩ := h
  refine ⟨hl, fun nw hnw φ hφ => ⟨fun hm => ?_, (hn nw hnw φ hφ).2⟩, hc, hw⟩
  have := (hn nw hnw φ hφ).1
  rw [NatMap.find?_ofList, Option.isNone_iff_eq_none, List.lookup_eq_none_iff] at this
  have h' := this ⟨φ.dst, ()⟩ (List.mem_map_of_mem hm)
  simp at h'

/-! ## Well formed -/

theorem insPhis_wf {f : Func} {news : List (List Phi)} (hwf : f.wf sig syms = true)
    (h : insOk f news = true) : (insPhis f news).wf sig syms = true := by
  obtain ⟨hl, hn, hc, hw⟩ := insOk_spec h
  have hwf' := hwf
  unfold Func.wf at hwf' ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at hwf' ⊢
  obtain ⟨⟨⟨hm, _⟩, _⟩, hb⟩ := hwf'
  have hmem : ∀ b₁ ∈ (insPhis f news).blocks, ∃ bk ∈ f.blocks, ∃ nw ∈ news,
      b₁ = { bk with phis := nw ++ bk.phis } := by
    intro b₁ hb₁
    simp only [insPhis, List.mem_map] at hb₁
    obtain ⟨⟨bk, nw⟩, hz, rfl⟩ := hb₁
    exact ⟨bk, (List.of_mem_zip hz).1, nw, (List.of_mem_zip hz).2, rfl⟩
  refine ⟨⟨⟨?_, hw⟩, hc⟩, fun b₁ hb₁ => ?_⟩
  · unfold Func.machine at hm ⊢
    rw [List.all_eq_true] at hm ⊢
    intro b₁ hb₁
    obtain ⟨bk, hbk, nw, _, rfl⟩ := hmem b₁ hb₁
    exact hm bk hbk
  · obtain ⟨bk, hbk, nw, hnw, rfl⟩ := hmem b₁ hb₁
    obtain ⟨⟨hph, hbody⟩, hterm⟩ := hb bk hbk
    refine ⟨⟨fun φ hφ => ?_, hbody⟩, by simpa [insPhis] using hterm⟩
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact (hn nw hnw φ hφ).2
    · exact hph φ hφ

/-! ## The simulation -/

theorem agree_fold_fresh {X : LSCtx} {env' env : Env} (h : X.Agree env' env) :
    ∀ l : List ((Nat × Ty) × Val), (∀ x ∈ l, X.fresh x.1.1 = true) → X.Agree (l.foldl bindStep env') env
  | [], _ => h
  | x :: l, hl => by
    rw [List.foldl_cons]
    exact agree_fold_fresh (LSCtx.Agree.insert_fresh h (hl x (List.mem_cons_self ..)) _) l
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- Entering a block with phis prepended, whose results are fresh, from an agreeing environment. -/
theorem approx_enter_ins {X : LSCtx} {bk : Block} {nw : List Phi}
    (hfresh : ∀ φ ∈ nw, X.fresh φ.dst = true) (hin : ∀ φ ∈ bk.phis, ∀ p ∈ φ.incoming, X.inV p.1)
    {env' env : Env} (ha : X.Agree env' env) (prev : Option Nat) :
    Approx X.Agree (enter env' prev { bk with phis := nw ++ bk.phis }) (enter env prev bk) := by
  rw [enter_eq, enter_eq]
  refine Approx.lift fun e₁' he₁' => ?_
  unfold enterOpt at he₁' ⊢
  simp only [List.mapM_append] at he₁'
  rcases hn : nw.mapM (fun phi => prev >>= inc phi >>= opVal env') with _ | vn
  · rw [hn] at he₁'; simp at he₁'
  have hold : bk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env') =
      bk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env) := by
    apply mapM_congr'
    intro φ hφ
    cases prev with
    | none => rfl
    | some q =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rcases hi : inc φ q with _ | o
      · rfl
      · simp only [Option.bind_some]
        exact ha.opVal (hin φ hφ _ (inc_mem hi))
  rw [hn, hold] at he₁'
  rcases ho : bk.phis.mapM (fun phi => prev >>= inc phi >>= opVal env) with _ | vo
  · rw [ho] at he₁'; simp at he₁'
  rw [ho] at he₁'
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at he₁'
  have hln := (mapM_option_forall₂ hn).length_eq
  have hlo := (mapM_option_forall₂ ho).length_eq
  simp only [List.map_append, List.length_append, List.length_map, hln, hlo, beq_self_eq_true,
    ↓reduceIte, Option.some.injEq] at he₁'
  subst he₁'
  refine ⟨((bk.phis.map fun phi => (phi.dst, phi.ty)).zip vo).foldl bindStep env, by simp [hlo], ?_⟩
  rw [List.zip_append (by simp [hln]), List.foldl_append]
  refine LSCtx.Agree.fold (agree_fold_fresh ha _ fun x hx => ?_) _
  obtain ⟨φ, hφ, hxe⟩ := List.mem_map.mp (List.of_mem_zip hx).1
  rw [← hxe]
  exact hfresh φ hφ

theorem insPhis_head {f : Func} {news : List (List Phi)} (hl : news.length = f.blocks.length)
    {e : Block} (he : f.blocks.head? = some e) :
    ∃ e₁, (insPhis f news).blocks.head? = some e₁ ∧ e₁.id = e.id := by
  unfold insPhis
  cases hb : f.blocks with
  | nil => rw [hb] at he; cases he
  | cons x l =>
    rw [hb] at he hl
    cases hn : news with
    | nil => rw [hn] at hl; simp at hl
    | cons n ns =>
      simp only [List.head?_cons, Option.some.injEq] at he
      subst he
      exact ⟨_, rfl, rfl⟩

/-- The function with unused phis inserted approximates the function. -/
theorem insPhis_sound {f : Func} {news : List (List Phi)} (hwf : f.wf sig syms = true)
    (h : insOk f news = true) {o : Oracle} (ho : Oracle.Mono o) (hoi : o.IntRet) (c : Ctx) :
    FuncRef o c (some (insPhis f news)) (some f) := by
  obtain ⟨hl, hn, _, _⟩ := insOk_spec h
  have hm := Func.wf_machine hwf
  let X := LSCtx.of f (insPhis f news)
  have hfresh : ∀ nw ∈ news, ∀ φ ∈ nw, X.fresh φ.dst = true := by
    intro nw hnw φ hφ
    show ((NatMap.ofList ((funcVars f).map (·, ()))).find? φ.dst).isNone = true
    rw [NatMap.find?_ofList, Option.isNone_iff_eq_none, List.lookup_eq_none_iff]
    intro p hp
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
    simp only [bne_iff_ne, ne_eq]
    intro hpe
    exact (hn nw hnw φ hφ).1 (hpe ▸ hu)
  let R : BState → BState → Prop := fun s' s => s'.2 = s.2 ∧ X.Agree s'.1 s.1 ∧ EnvInt s.1
  have sim : Sim o c (insPhis f news) f R := Sim.of_steps fun s' s hR => by
    left
    obtain ⟨env', prev, b⟩ := s'
    obtain ⟨env, prev₀, b₀⟩ := s
    obtain ⟨he, ha, hint⟩ := hR
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    dsimp only
    unfold stepBlock
    rcases insPhis_block hl b with ⟨h1, h2⟩ | ⟨bk, nw, h1, hnw, h2⟩
    · rw [h1]; exact Approx.stuck _
    rw [h1, h2]
    dsimp only
    have hbm := List.mem_of_find?_eq_some h1
    refine Approx.bind (Approx.strengthen (approx_enter_ins (hfresh nw hnw)
      (fun φ hφ p hp u hu => LSCtx.of_V (vars_phi hbm hφ hp hu)) ha prev)
      (returns_enter_int hint prev bk)) fun e₁' e₁ ⟨ha₁, hi₁⟩ => ?_
    refine Approx.bind (Approx.strengthen (LSCtx.approx_runBodyO ho hoi c bk.body e₁' e₁ ha₁ hi₁
      fun st hst => ⟨Func.machine_of_mem hm hbm st hst, fun a ha' u hu =>
        LSCtx.of_V (vars_stmt hbm hst ha' hu)⟩)
      (returns_runBodyO hoi c e₁ bk.body hi₁ (Func.machine_of_mem hm hbm))) fun e₂' e₂ ⟨ha₂, hi₂⟩ => ?_
    refine Approx.mono (Approx.strengthen (approx_runTerm_agree (fun a ha' => ha₂.opVal
      fun u hu => LSCtx.of_V (vars_term hbm ha' hu)) hi₂) (returns_runTerm hi₂ bk.term))
      fun n' n ⟨hn', hnint⟩ => ?_
    rcases n' with ⟨ea, d'⟩ | v' <;> rcases n with ⟨eb, d⟩ | v <;> simp only at hn'
    · obtain ⟨h1, h2, h3, _⟩ := hn'
      rw [h1, h2, h3]
      exact ⟨rfl, ha₂, hi₂⟩
    · exact hn'
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he : f.blocks.head? with
  | none =>
    cases he₁ : (insPhis f news).blocks.head? with
    | none => exact Approx.stuck _
    | some e₁ =>
      exfalso
      unfold insPhis at he₁
      cases hb : f.blocks with
      | nil => rw [hb] at he₁; simp at he₁
      | cons x l => rw [hb] at he; cases he
  | some e =>
    obtain ⟨e₁, he₁, hid⟩ := insPhis_head hl he
    rw [he₁]
    dsimp only
    rw [show (insPhis f news).params = f.params from rfl, hid]
    refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _) (returns_bind_int EnvInt.empty hargs))
      fun env env₀ ⟨e₂, hi⟩ => ?_
    cases e₂
    exact Sim.approx sim (env, none, e.id) (env, none, e.id) ⟨rfl, fun _ _ => rfl, hi⟩

end Fe.Sonatina.Steps.Schemas
