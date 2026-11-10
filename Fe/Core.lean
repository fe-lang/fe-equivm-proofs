/-!
# Fe model core

The monad that exported Fe functions are written in.  It depends on Lean's standard library
only: the environment and the world are parameters, and each target supplies its own.
-/

namespace Fe

/-- How a run ends other than by returning to its caller. -/
inductive Exit (σ : Type) where
  /-- A revert with its return data: an explicit revert, or a failed `assert!` with a message. -/
  | revert (data : ByteArray)
  /-- A trap with its panic code: checked arithmetic, a failed index check, an `assert!` without
      a message. -/
  | panic (code : Nat)
  /-- A state change attempted where none is allowed. -/
  | static
  /-- An invalid instruction: `panic()` and `todo()`, which trap. -/
  | trap
  /-- The whole run ends successfully from inside a callee, with return data and the world as
      it then is. -/
  | stop (data : ByteArray) (world : σ)

/-- Whether an exit is a failure that discards the run's changes: a revert or a panic. -/
@[simp] def Exit.reverts {σ : Type} : Exit σ → Bool
  | .revert _ | .panic _ => true
  | .static | .trap | .stop _ _ => false

/-- The model monad over an environment `ρ` and a world `σ`.  A run that does not terminate is
    `none`, the bottom of `Option`, so recursive definitions can use `partial_fixpoint`. -/
abbrev M (ρ σ : Type) := ReaderT ρ (StateT σ (ExceptT (Exit σ) Option))

namespace M

variable {ρ σ α β : Type}

/-- Run a computation: `none` if it diverges, otherwise how it exited, or its result and the
    final world. -/
def exec (m : M ρ σ α) (env : ρ) (world : σ) : Option (Except (Exit σ) (α × σ)) :=
  ((m.run env).run world).run

def fail (f : Exit σ) : M ρ σ α := throw f

/-- A run that does not terminate. -/
def diverge : M ρ σ α := fun _ _ => (none : Option (Except (Exit σ) (α × σ)))

/-- End the whole run successfully with `data`. -/
def stop (data : ByteArray) : M ρ σ α := do fail (.stop data (← get))

def revert (data : ByteArray) : M ρ σ α := fail (.revert data)

def panic (code : Nat) : M ρ σ α := fail (.panic code)

@[simp] theorem exec_pure (a : α) (env : ρ) (w : σ) :
    (pure a : M ρ σ α).exec env w = some (.ok (a, w)) := rfl

@[simp] theorem exec_fail (f : Exit σ) (env : ρ) (w : σ) :
    (fail f : M ρ σ α).exec env w = some (.error f) := rfl

@[simp] theorem exec_revert (data : ByteArray) (env : ρ) (w : σ) :
    (revert data : M ρ σ α).exec env w = some (.error (.revert data)) := rfl

@[simp] theorem exec_panic (code : Nat) (env : ρ) (w : σ) :
    (panic code : M ρ σ α).exec env w = some (.error (.panic code)) := rfl

/-- What follows a branch follows each side of it. -/
theorem ite_bind (c : Prop) [Decidable c] (x y : M ρ σ α) (f : α → M ρ σ β) :
    (if c then x else y) >>= f = if c then x >>= f else y >>= f := by
  split <;> rfl

@[simp] theorem exec_diverge (env : ρ) (w : σ) :
    (diverge : M ρ σ α).exec env w = none := rfl

@[simp] theorem exec_stop (data : ByteArray) (env : ρ) (w : σ) :
    (stop data : M ρ σ α).exec env w = some (.error (.stop data w)) := rfl

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

/-! ## Runs that never stop from inside -/

/-- The computation never ends the run from inside: it returns, fails or diverges.  A model
    written without `stop` has this property, and a proof that inspects its outcomes needs it. -/
def NoStop (m : M ρ σ α) : Prop :=
  ∀ env w data w', m.exec env w ≠ some (.error (.stop data w'))

theorem NoStop.pure (a : α) : NoStop (pure a : M ρ σ α) := by
  intro env w data w' h; simp at h

theorem NoStop.revert (data : ByteArray) : NoStop (revert data : M ρ σ α) := by
  intro env w data' w' h; simp at h

theorem NoStop.panic (code : Nat) : NoStop (panic code : M ρ σ α) := by
  intro env w data w' h; simp at h

theorem NoStop.fail_static : NoStop (fail .static : M ρ σ α) := by
  intro env w data w' h; simp at h

theorem NoStop.read : NoStop (read : M ρ σ ρ) := by
  intro env w data w' h; simp at h

theorem NoStop.get : NoStop (get : M ρ σ σ) := by
  intro env w data w' h; simp at h

theorem NoStop.modify (f : σ → σ) : NoStop (modify f : M ρ σ PUnit) := by
  intro env w data w' h; simp at h

theorem NoStop.bind {m : M ρ σ α} {k : α → M ρ σ β} (hm : NoStop m) (hk : ∀ a, NoStop (k a)) :
    NoStop (m >>= k) := by
  intro env w data w' h
  rw [exec_bind] at h
  cases hr : m.exec env w with
  | none => rw [hr] at h; cases h
  | some r =>
    cases r with
    | error f => rw [hr] at h; injection h with h; injection h with h; exact hm env w data w' (by rw [hr, h])
    | ok p => rw [hr] at h; exact hk p.1 env p.2 data w' h

theorem NoStop.ite (c : Prop) [Decidable c] {a b : M ρ σ α} (ha : NoStop a) (hb : NoStop b) :
    NoStop (if c then a else b) := by
  split <;> assumption

end M

end Fe
