import Fe.Sonatina.Steps.Oracle

/-!
# Simulation of a function by its output

The schema every step kind's proof uses (design §5.3): a relation `R` on block states of the
output `f'` and the input `f`, both run with calls by one oracle, such that from related states
one block of `f'` diverges, or ends as the input's run does, or reaches a state related to one
the input's run reaches after any number of blocks (`Sim`).  Then the output's run from related
states approximates the input's (`Sim.approx`), by fixpoint induction over the output's run: the
output may take steps the input does not (an edge split's new block), and the input steps the
output does not (a merged chain, a tunnel), with no bound on either.

`Sim.of_steps` builds a simulation from blocks that step together (`lock`) or output blocks that
only jump (`stutter`).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Lean.Order

/-- A block state: the environment, the block entered from, the block. -/
abbrev BState := Env × Option Nat × Nat

/-- The run of `f` from a block state. -/
def runFrom (o : Oracle) (c : Ctx) (f : Func) (s : BState) : FeM (List Val) :=
  runBlocksO o c f s.1 s.2.1 s.2.2

/-- What one output block's result `r` must be against the input's run from `s` at `w`. -/
def SimStep (o : Oracle) (c : Ctx) (f : Func) (R : BState → BState → Prop) (id' : Nat)
    (s : BState) (I : ExecutionEnv) (w : World) :
    Option (Except (Exit World) (Next × World)) → Prop
  | none => True
  | some (.error e') => ∃ e, (runFrom o c f s).exec I w = some (.error e) ∧ ExitRel e' e
  | some (.ok (.done v, w₁')) =>
    ∃ w₁, (runFrom o c f s).exec I w = some (.ok (v, w₁)) ∧ WRel w₁' w₁
  | some (.ok (.goto env d, w₁')) =>
    ∃ t w₁, (runFrom o c f s).exec I w = (runFrom o c f t).exec I w₁ ∧ R (env, some id', d) t ∧
      WRel w₁' w₁

/-- `R` is a simulation of `f` by `f'`. -/
def Sim (o : Oracle) (c : Ctx) (f' f : Func) (R : BState → BState → Prop) : Prop :=
  ∀ s' s, R s' s → ∀ I w' w, WRel w' w →
    SimStep o c f R s'.2.2 s I w ((stepBlock o c f' s'.1 s'.2.1 s'.2.2).exec I w')

/-- The output's run from related states approximates the input's. -/
theorem Sim.approx {o : Oracle} {c : Ctx} {f' f : Func} {R : BState → BState → Prop}
    (h : Sim o c f' f R) : ∀ s' s, R s' s → Approx Eq (runFrom o c f' s') (runFrom o c f s) := by
  suffices H : ∀ env prev id s, R (env, prev, id) s →
      Approx Eq (runBlocksO o c f' env prev id) (runFrom o c f s) by
    intro s' s hR; exact H s'.1 s'.2.1 s'.2.2 s hR
  refine runBlocksO.fixpoint_induct o c f'
    (fun G => ∀ env prev id s, R (env, prev, id) s → Approx Eq (G env prev id) (runFrom o c f s))
    ?_ ?_
  · exact Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
        ∀ prev id s, R (env, prev, id) s → Approx Eq (G prev id) (runFrom o c f s))
      fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
        ∀ id s, R (env, prev, id) s → Approx Eq (G id) (runFrom o c f s))
      fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
        ∀ s, R (env, prev, id) s → Approx Eq x (runFrom o c f s))
      fun id => admissible_approx_forall _ _ _
  · intro G hG env prev id s hR I w' w hw
    have hs := h (env, prev, id) s hR I w' w hw
    simp only [Fe.M.exec_bind]
    revert hs
    rcases (stepBlock o c f' env prev id).exec I w' with _ | (e' | ⟨n, w₁'⟩)
    · intro _; trivial
    · rintro ⟨e, he, hx⟩; simp only [he, ResRel]; exact hx
    · cases n with
      | done v =>
        rintro ⟨w₁, hv, hx⟩
        simp only [Fe.M.exec_pure, hv, ResRel]
        exact ⟨trivial, hx⟩
      | goto env' d =>
        rintro ⟨t, w₁, ht, hRt, hx⟩
        rw [ht]
        exact hG env' (some id) d t hRt I w₁' w₁ hx

/-- The input's run from a state whose block goes on. -/
theorem runFrom_goto {o : Oracle} {c : Ctx} {f : Func} {s : BState} {I : ExecutionEnv}
    {w w₁ : World} {env : Env} {d : Nat}
    (h : (stepBlock o c f s.1 s.2.1 s.2.2).exec I w = some (.ok (.goto env d, w₁))) :
    (runFrom o c f s).exec I w = (runFrom o c f (env, some s.2.2, d)).exec I w₁ := by
  unfold runFrom
  rw [runBlocksO, Fe.M.exec_bind, h]

theorem runFrom_done {o : Oracle} {c : Ctx} {f : Func} {s : BState} {I : ExecutionEnv}
    {w w₁ : World} {v : List Val}
    (h : (stepBlock o c f s.1 s.2.1 s.2.2).exec I w = some (.ok (.done v, w₁))) :
    (runFrom o c f s).exec I w = some (.ok (v, w₁)) := by
  unfold runFrom
  rw [runBlocksO, Fe.M.exec_bind, h]
  rfl

theorem runFrom_error {o : Oracle} {c : Ctx} {f : Func} {s : BState} {I : ExecutionEnv}
    {w : World} {e : Exit World}
    (h : (stepBlock o c f s.1 s.2.1 s.2.2).exec I w = some (.error e)) :
    (runFrom o c f s).exec I w = some (.error e) := by
  unfold runFrom
  rw [runBlocksO, Fe.M.exec_bind, h]

/-- How two blocks' results correspond when both step: the same exit or values, or the states
    they go to related by `R`, from blocks `id'` and `id`. -/
def NextRel (R : BState → BState → Prop) (id' id : Nat) : Next → Next → Prop
  | .goto env' d', .goto env d => R (env', some id', d') (env, some id, d)
  | .done v', .done v => v' = v
  | _, _ => False

/-- A simulation from blocks that step together, or output blocks that only jump without
    changing anything (the input does not move). -/
theorem Sim.of_steps {o : Oracle} {c : Ctx} {f' f : Func} {R : BState → BState → Prop}
    (h : ∀ s' s, R s' s →
      Approx (NextRel R s'.2.2 s.2.2) (stepBlock o c f' s'.1 s'.2.1 s'.2.2)
        (stepBlock o c f s.1 s.2.1 s.2.2) ∨
      ∃ d, (∀ I w, (stepBlock o c f' s'.1 s'.2.1 s'.2.2).exec I w =
        some (.ok (.goto s'.1 d, w))) ∧ R (s'.1, some s'.2.2, d) s) :
    Sim o c f' f R := by
  intro s' s hR I w' w hw
  rcases h s' s hR with hl | ⟨d, hd, hRd⟩
  · have hx := hl I w' w hw
    revert hx
    rcases (stepBlock o c f' s'.1 s'.2.1 s'.2.2).exec I w' with _ | (e' | ⟨n', w₁'⟩)
    · intro _; trivial
    · rcases hin : (stepBlock o c f s.1 s.2.1 s.2.2).exec I w with _ | (e | ⟨n, w₁⟩) <;>
        intro hx <;> simp only [ResRel] at hx
      exact ⟨e, runFrom_error hin, hx⟩
    · rcases hin : (stepBlock o c f s.1 s.2.1 s.2.2).exec I w with _ | (e | ⟨n, w₁⟩) <;>
        intro hx <;> simp only [ResRel] at hx
      cases n' <;> cases n <;> simp only [NextRel, false_and] at hx
      all_goals first
        | exact ⟨_, w₁, runFrom_goto hin, hx.1, hx.2⟩
        | exact ⟨w₁, hx.1 ▸ runFrom_done hin, hx.2⟩
  · rw [hd]
    exact ⟨s, w, rfl, hRd, hw⟩

end Fe.Sonatina.Steps
