import Fe.Sonatina.Stage3.Place.Fns

/-!
# What H's runs of a function keep, for its terminal fixed buffers

Rule S6 (`s6Site`) speaks of two sets of values of function `f`: the integer operands
(`intOperands`), whose values are integers in every run of H, and, per terminal fixed buffer at
site `t`, the must-origin set `M_t` (`mustIter`), whose values point into the buffer in every run
that has made it.  Both are facts of reachable states, not of every state the invariant `Inv`
and the frame relation `EnvRel` admit: a value that `EnvRel` relates may be a pointer though
its statement only makes integers, and a value of `M_t` may be live, and bound, at the site (in a
block no run reaches; session 6, `place/s6/t/fix-cex*.lean`).  `FixInv` states them of H's
environment at a point of `f`, so that the simulation carries them (`FnOk.qEntry/qStep/qEdge`)
to the site (`FixK`):

- every bound integer operand is an integer;
- per site: if its result is bound, the point is after the site (in the reach set of the site's
  block, or after a statement that defines it in its block), and while its result is not bound,
  no value of `M_t` is.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- Every bound integer operand of `f` is an integer. -/
def IntEnv (f : HFunc) (envH : HEnv) : Prop :=
  ∀ y ∈ intOperands f, ∀ v, envH[y]? = some v → ∀ b o, v ≠ .ptr b o

/-- Statement `it` of block `bt` of `fn` is a terminal fixed buffer with result `t`. -/
def FixSite (fn : Fn) (bt : HBlock) (it t : Nat) : Prop :=
  bt ∈ fn.f.blocks ∧ ∃ st a tx, bt.body[it]? = some st ∧ st.inst = .base (.malloc a) ∧
    st.dsts = [(t, tx)] ∧ fn.c.frec.isFixed t = true

/-- The blocks after the site in block `bt`, as `s6Site` computes them. -/
def fixR (f : HFunc) (bt : HBlock) : List Nat :=
  reachIter f (f.blocks.length + 1) (nset bt.term.succs)

/-- The must-origin set of the site with result `t`, as `s6Site` computes it. -/
def fixM (f : HFunc) (t : Nat) : List Nat :=
  mustIter f (intOperands f) (f.blocks.length + 1) [t]

/-- The point before statement `i` of block `b` is after the site with result `t` in block
    `bt`: `b` is in the site's reach set, or a statement before `i` in `b` defines `t`. -/
def AfterFix (f : HFunc) (bt : HBlock) (t : Nat) (b : HBlock) (i : Nat) : Prop :=
  b.id ∈ fixR f bt ∨ ∃ j < i, ∃ s, b.body[j]? = some s ∧ t ∈ s.defs

/-- The invariant of H's environments at the point before statement `i` of block `b` of `fn`. -/
def FixInv (fn : Fn) (b : HBlock) (i : Nat) (envH : HEnv) : Prop :=
  IntEnv fn.f envH ∧ ∀ bt it t, FixSite fn bt it t →
    ((envH[t]?).isSome → AfterFix fn.f bt t b i) ∧
    (envH[t]? = none → ∀ y ∈ fixM fn.f t, envH[y]? = none)

end Fe.Sonatina.Stage3.Place
