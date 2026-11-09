/-!
# Fe model core

The monad that exported Fe functions are written in.  It depends on Lean's standard library
only: the environment and the world are parameters, and each target supplies its own.
-/

namespace Fe

/-- Why a run stopped without a result. -/
inductive Fail where
  /-- A revert with its return data: an explicit revert, or a failed `assert!` with a message. -/
  | revert (data : ByteArray)
  /-- A trap with its panic code: checked arithmetic, a failed index check, an `assert!` without
      a message. -/
  | panic (code : Nat)
  /-- A state change attempted where none is allowed. -/
  | static

/-- The model monad over an environment `ρ` and a world `σ`.  A run that does not terminate is
    `none`, the bottom of `Option`, so recursive definitions can use `partial_fixpoint`. -/
abbrev M (ρ σ : Type) := ReaderT ρ (StateT σ (ExceptT Fail Option))

namespace M

variable {ρ σ α β : Type}

/-- Run a computation: `none` if it diverges, otherwise its failure, or its result and the final
    world. -/
def exec (m : M ρ σ α) (env : ρ) (world : σ) : Option (Except Fail (α × σ)) :=
  ((m.run env).run world).run

def fail (f : Fail) : M ρ σ α := throw f

def revert (data : ByteArray) : M ρ σ α := fail (.revert data)

def panic (code : Nat) : M ρ σ α := fail (.panic code)

@[simp] theorem exec_pure (a : α) (env : ρ) (w : σ) :
    (pure a : M ρ σ α).exec env w = some (.ok (a, w)) := rfl

@[simp] theorem exec_fail (f : Fail) (env : ρ) (w : σ) :
    (fail f : M ρ σ α).exec env w = some (.error f) := rfl

@[simp] theorem exec_revert (data : ByteArray) (env : ρ) (w : σ) :
    (revert data : M ρ σ α).exec env w = some (.error (.revert data)) := rfl

@[simp] theorem exec_panic (code : Nat) (env : ρ) (w : σ) :
    (panic code : M ρ σ α).exec env w = some (.error (.panic code)) := rfl

@[simp] theorem exec_read (env : ρ) (w : σ) :
    (read : M ρ σ ρ).exec env w = some (.ok (env, w)) := rfl

@[simp] theorem exec_get (env : ρ) (w : σ) :
    (get : M ρ σ σ).exec env w = some (.ok (w, w)) := rfl

@[simp] theorem exec_set (env : ρ) (w w' : σ) :
    (set w' : M ρ σ PUnit).exec env w = some (.ok (⟨⟩, w')) := rfl

@[simp] theorem exec_modify (f : σ → σ) (env : ρ) (w : σ) :
    (modify f : M ρ σ PUnit).exec env w = some (.ok (⟨⟩, f w)) := rfl

/-- A bind runs its first part, and continues only from a result. -/
@[simp] theorem exec_bind (m : M ρ σ α) (k : α → M ρ σ β) (env : ρ) (w : σ) :
    (m >>= k).exec env w =
      match m.exec env w with
      | none => none
      | some (.error f) => some (.error f)
      | some (.ok (a, w')) => (k a).exec env w' := by
  simp only [exec, bind, ReaderT.bind, ReaderT.run, StateT.bind, StateT.run, ExceptT.bind,
    ExceptT.run, ExceptT.mk, Option.bind]
  cases h : m env w with
  | none => rfl
  | some r => cases r with
    | error f => rfl
    | ok p => rfl

/-- Running a conditional runs the branch taken. -/
theorem exec_ite (c : Prop) [Decidable c] (a b : M ρ σ α) (env : ρ) (w : σ) :
    (if c then a else b).exec env w = if c then a.exec env w else b.exec env w := by
  split <;> rfl

/-- A map runs its computation and applies the function to a result. -/
@[simp] theorem exec_map (f : α → β) (m : M ρ σ α) (env : ρ) (w : σ) :
    (f <$> m).exec env w =
      match m.exec env w with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (a, w')) => some (.ok (f a, w')) := by
  rw [map_eq_pure_bind, exec_bind]
  rfl

end M

end Fe
