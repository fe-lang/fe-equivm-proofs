import Fe.Sonatina.Steps.SchemasWord

/-!
# The constant evaluator

`evalConst op ws` is the value of the pure operation `op` on the words `ws`, or `none` if the
arity is wrong or a word is not below `2 ^ 256`.  It is structural (no well-founded
recursion), so `decide` evaluates it in the kernel; `evm_exp` takes 256 square-and-multiply
steps.  Design §4.13 "F".

`evalConst_sound`: an instruction of the machine IR whose operands evaluate to the words gives
the value `evalConst` computes.  `clz` is the exception: its value holds on Osaka only, and it
traps before (`runInst_clz`); a checker must not fold `clz` for an earlier fork (review H-2).
-/

namespace Fe.Sonatina.Steps.Schemas

/-- A pure operation of the machine IR, of any arity. -/
inductive Op where
  | op1 (o : Op1)
  | op2 (o : Op2)
  | op3 (o : Op3)
  deriving DecidableEq, Repr, Inhabited

def evalConst : Op → List Nat → Option Nat
  | .op1 o, [x] => if x < W then some (o.eval x) else none
  | .op2 o, [x, y] => if x < W ∧ y < W then some (o.eval x y) else none
  | .op3 o, [x, y, z] => if x < W ∧ y < W ∧ z < W then some (o.eval x y z) else none
  | _, _ => none

def PureInst.op : PureInst → Op
  | .op1 o _ => .op1 o
  | .op2 o _ _ => .op2 o
  | .op3 o _ _ _ => .op3 o

theorem evalConst_lt {op : Op} {ws : List Nat} {r : Nat} (h : evalConst op ws = some r) :
    r < W := by
  unfold evalConst at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h
  · exact Op1.eval_lt _ ‹_›
  · exact Op2.eval_lt _ ‹_ ∧ _›.1 ‹_ ∧ _›.2
  · exact Op3.eval_lt _ ‹_ ∧ _ ∧ _›.2.2

theorem ArgsAre.lt {env : Env} {os : List Operand} {xs : List Nat} (h : ArgsAre env os xs) :
    ∀ x ∈ xs, x < W := by
  induction h with
  | nil => intro x hx; cases hx
  | cons hd _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hd.2
    · exact ih x hx

/-- On the words its operands evaluate to, a pure instruction's `evalConst` is `evalOn`. -/
theorem evalConst_of_args {env : Env} {p : PureInst} {xs : List Nat}
    (h : ArgsAre env p.args xs) : evalConst p.op xs = some (p.evalOn xs) := by
  have hlt := h.lt
  rcases p with ⟨o, a⟩ | ⟨o, a, b⟩ | ⟨o, a, b, d⟩ <;>
    simp only [PureInst.args, ArgsAre] at h
  · rcases h with _ | ⟨_, _ | _⟩
    simp [evalConst, PureInst.op, PureInst.evalOn, hlt]
  · rcases h with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
    simp [evalConst, PureInst.op, PureInst.evalOn, hlt]
  · rcases h with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
    simp [evalConst, PureInst.op, PureInst.evalOn, hlt]

/-- Soundness of the constant evaluator: an instruction of the machine IR other than `clz`,
    whose operands evaluate to the `i256` words `xs`, gives the word `evalConst` computes, at the
    width of `PureInst.bits` (`Val.as_word` makes it the `i256` value). -/
theorem evalConst_sound {c : Ctx} {env : Env} {i : Inst} {p : PureInst} (hp : pureInst? i = some p)
    (hclz : ∀ a, p ≠ .op1 .clz a) {xs : List Nat} (hargs : ArgsAre env p.args xs) {r : Nat}
    (h : evalConst p.op xs = some r) : runInst c env i = pure [.int p.bits r] := by
  rw [evalConst_of_args hargs, Option.some.injEq] at h
  subst h
  rw [← pureInst?_toInst hp]
  exact runInst_pure hclz hargs

/-- `clz` folds to `evalConst`'s value on Osaka only. -/
theorem evalConst_clz {c : Ctx} {env : Env} {a : Operand} {x r : Nat}
    (ha : evalOperand env a = pure (.int 256 x)) (h : evalConst (.op1 .clz) [x] = some r)
    (I : Fe.EVM.Env) (w : Fe.EVM.World) :
    (runInst c env (.clz a)).exec I w =
      if I.header.fork = .Osaka then some (.ok ([.int 256 r], w)) else some (.error .trap) := by
  simp only [evalConst] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact runInst_clz ha I w
  · cases h

end Fe.Sonatina.Steps.Schemas
