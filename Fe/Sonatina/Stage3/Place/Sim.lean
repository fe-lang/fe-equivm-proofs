import Fe.Sonatina.Stage3.Place.Inst
import Fe.Sonatina.Stage3.Place.Index
import Fe.Sonatina.Steps.Defined

/-!
# The simulation of S14 (PLAN §5)

Every run of the lowered machine module's function that ends is matched by a run of H's: the
call contract `CallP` (`CallP_runFunc`).  The proof fixes, per function, what the checks give
about it as obligations (`FnOk`): each statement's template (`StmtObl`: a plain one or a call
`TemplOkC`, a diamond `DiaK`, a terminal fixed buffer `FixK`), each terminator (`TermObl`),
each block entry (`PhiObl`) and the function entry (`EntryObl`).  The pattern lemmas
(`Inst*.lean`) and the static facts of `check` discharge them (`Sound.lean`).

The machine side runs on the oracle layer (`Steps/Oracle.lean`): a function's blocks by
`runBlocksO` under a fixed oracle `O` that satisfies the call contract, so that a block's
statements run structurally (`runBodyO`) and each template's statements are a prefix of them;
calls by the step-indexed oracle `runFuncN` (`Index.lean`), the call contract by induction on
the index.

**Blocks** (`blocks_sim`), by `runBlocksO.fixpoint_induct`: the motive speaks of every entry
into a machine block the run may make, whatever its kind, so that no uniqueness of the kind is
needed: a region start (`QR`: the start block of a source block's region, entered from the block
a source predecessor's region ends in), and a diamond's arm or join (`QD`: inside the template
of a source statement whose machine statements branch, the dynamic `evm_mload_bytes` and the
heap base clamp).  It also says that the approximant is below the fixpoint (`Def`), which the
terminal fixed buffer's suffix needs.  Inside a block the walk (`walk_sim`) is induction on the
source statements, one template at a time.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Lean.Order

/-! ## The walk, position by position -/

/-- The callee place of statement `s` among the places `cs` left, and the places left after it
    (as `walk` takes them). -/
def calleeOf (s : HStmt) (cs : List Nat) : Option Nat × List Nat :=
  if s.inst matches .base (.call ..) then (cs.head?, cs.tail) else (none, cs)

/-- The checking walk's machine block, statements and callee places before statement `i` of
    the statements `l`. -/
def walkTo (c : FCtx) (vm : VM) : List HStmt → Nat → List Stmt → List Nat → Nat →
    Option (Nat × List Stmt × List Nat)
  | _, mb, ms, cs, 0 => some (mb, ms, cs)
  | [], _, _, _, _ + 1 => none
  | s :: rest, mb, ms, cs, i + 1 =>
    match stmt c true vm s mb ms (calleeOf s cs).1 with
    | some (_, mb', ms', _) => walkTo c vm rest mb' ms' (calleeOf s cs).2 i
    | none => none

theorem walkTo_succ {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} {i : Nat} {mb₁ : Nat} {ms₁ : List Stmt} {cs₁ : List Nat} {s : HStmt}
    {x : Nat × List Stmt × List Nat},
    walkTo c vm l mb ms cs i = some (mb₁, ms₁, cs₁) → l[i]? = some s →
    walkTo c vm l mb ms cs (i + 1) = some x →
    ∃ vm' mb₂ ms₂ ds, stmt c true vm s mb₁ ms₁ (calleeOf s cs₁).1 = some (vm', mb₂, ms₂, ds) ∧
      x = (mb₂, ms₂, (calleeOf s cs₁).2)
  | [], _, _, _, _, _, _, _, _, _, _, hs, _ => by simp at hs
  | t :: rest, mb, ms, cs, 0, mb₁, ms₁, cs₁, s, x, h₁, hs, h₂ => by
    simp only [walkTo, Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    simp only [walkTo] at h₂
    split at h₂
    · next vm' mb₂ ms₂ ds heq =>
      simp only [walkTo, Option.some.injEq] at h₂
      exact ⟨vm', mb₂, ms₂, ds, heq, h₂.symm⟩
    · cases h₂
  | t :: rest, mb, ms, cs, i + 1, mb₁, ms₁, cs₁, s, x, h₁, hs, h₂ => by
    simp only [walkTo] at h₁ h₂
    split at h₁
    · next heq =>
      rw [heq] at h₂
      exact walkTo_succ h₁ (by simpa using hs) h₂
    · cases h₁

theorem walkTo_le {c : FCtx} {vm : VM} : ∀ {l : List HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} {i j : Nat}, i ≤ j → (walkTo c vm l mb ms cs j).isSome →
    (walkTo c vm l mb ms cs i).isSome
  | _, _, _, _, 0, _, _, _ => by simp [walkTo]
  | [], _, _, _, _ + 1, 0, hij, _ => absurd hij (by omega)
  | [], _, _, _, _ + 1, _ + 1, _, h => by simp [walkTo] at h
  | _ :: _, _, _, _, _ + 1, 0, hij, _ => absurd hij (by omega)
  | s :: rest, mb, ms, cs, i + 1, j + 1, hij, h => by
    simp only [walkTo] at h ⊢
    split
    · next heq =>
      rw [heq] at h
      exact walkTo_le (by omega) h
    · next heq => rw [heq] at h; exact h

/-! ## Machine computations that only bind -/

/-- `x` ends only by returning, in the world it started from. -/
def Quiet {α : Type} (x : FeM α) : Prop := ∀ I w r, x.exec I w = some r → ∃ a, r = .ok (a, w)

theorem Quiet.world {α : Type} {x : FeM α} (hx : Quiet x) {I : Fe.EVM.Env} {w w' : World} {a : α}
    (h : x.exec I w = some (.ok (a, w'))) : w = w' := by
  obtain ⟨b, hb⟩ := hx I w _ h
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
  exact hb.2.symm

theorem Quiet.pure {α : Type} (a : α) : Quiet (Pure.pure a : FeM α) := fun _ _ _ h => by
  simp only [Fe.M.exec_pure, Option.some.injEq] at h; exact ⟨a, h.symm⟩

theorem Quiet.stuck {α : Type} : Quiet (stuck : FeM α) := fun _ _ _ h => by cases h

theorem Quiet.bind {α β : Type} {x : FeM α} {k : α → FeM β} (hx : Quiet x)
    (hk : ∀ a, Quiet (k a)) : Quiet (x >>= k) := by
  intro I w r h
  simp only [Fe.M.exec_bind] at h
  cases hx0 : x.exec I w with
  | none => rw [hx0] at h; cases h
  | some r0 =>
    rw [hx0] at h
    obtain ⟨a, rfl⟩ := hx I w r0 hx0
    exact hk a I w r h

theorem Quiet.evalOperand (env : Env) (o : Operand) : Quiet (evalOperand env o) := by
  unfold Fe.Sonatina.evalOperand
  split
  · split
    · exact Quiet.pure _
    · exact Quiet.stuck
  · exact Quiet.pure _

theorem Quiet.mapM {α β : Type} {f : α → FeM β} (hf : ∀ a, Quiet (f a)) :
    ∀ l : List α, Quiet (l.mapM f)
  | [] => by simp only [List.mapM_nil]; exact Quiet.pure _
  | a :: l => by
    simp only [List.mapM_cons]
    exact Quiet.bind (hf a) fun b => Quiet.bind (Quiet.mapM hf l) fun bs => Quiet.pure _

theorem Quiet.bindEnv (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) :
    Quiet (Fe.Sonatina.bind env dsts vals) := by
  unfold Fe.Sonatina.bind
  split
  · exact Quiet.pure _
  · exact Quiet.stuck

theorem Quiet.enter (env : Env) (prev : Option Nat) (b : Block) :
    Quiet (Fe.Sonatina.enter env prev b) := by
  unfold Fe.Sonatina.enter
  refine Quiet.bind (Quiet.mapM (fun phi => ?_) _) fun vals => Quiet.bindEnv _ _ _
  split
  · split
    · exact Quiet.evalOperand _ _
    · exact Quiet.stuck
  · exact Quiet.stuck

theorem enter_nil {b : Block} (h : b.phis = []) (env : Env) (prev : Option Nat) :
    Fe.Sonatina.enter env prev b = pure env := by
  simp only [Fe.Sonatina.enter, h, List.mapM_nil, pure_bind, List.map_nil, Fe.Sonatina.bind,
    List.length_nil, beq_self_eq_true, ite_true, List.zip_nil_left, List.foldl_nil]

/-! ## How H ends against the machine -/

theorem Excuses.of_ok {α β : Type} {o : Outcome} {a : α} (h : Excuses o (.ok a : Except (Exit World) α))
    (r : Except (Exit World) β) : Excuses o r := by
  rcases h with h | h | ⟨e, he, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · cases he

theorem Excuses.of_error {α β : Type} {o : Outcome} {e : Exit World}
    (h : Excuses o (.error e : Except (Exit World) α)) : Excuses o (.error e : Except (Exit World) β) := by
  rcases h with h | h | ⟨e', he, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · simp only [Except.error.injEq] at he
    subst he
    exact Or.inr (Or.inr ⟨e, rfl, hm⟩)

/-- A run of `x >>= k` that ends, where `x` ends in an exit: it ends so. -/
theorem exec_bind_error {α β : Type} {x : FeM α} {k : α → FeM β} {I : Fe.EVM.Env} {w : World}
    {e : Exit World} (hx : x.exec I w = some (.error e)) : (x >>= k).exec I w = some (.error e) := by
  simp only [Fe.M.exec_bind, hx]

theorem exec_bind_ok {α β : Type} {x : FeM α} {k : α → FeM β} {I : Fe.EVM.Env} {w w' : World}
    {a : α} (hx : x.exec I w = some (.ok (a, w'))) : (x >>= k).exec I w = (k a).exec I w' := by
  simp only [Fe.M.exec_bind, hx]

/-- A run of `x >>= k` that ends: `x` ends, in an exit that is the whole run's, or in a value
    from which `k` ends as the whole run does. -/
theorem exec_bind_some {α β : Type} {x : FeM α} {k : α → FeM β} {I : Fe.EVM.Env} {w : World}
    {r : Except (Exit World) (β × World)} (h : (x >>= k).exec I w = some r) :
    (∃ e, x.exec I w = some (.error e) ∧ r = .error e) ∨
    ∃ a w', x.exec I w = some (.ok (a, w')) ∧ (k a).exec I w' = some r := by
  simp only [Fe.M.exec_bind] at h
  cases hx : x.exec I w with
  | none => rw [hx] at h; cases h
  | some r0 =>
    rw [hx] at h
    rcases r0 with e | ⟨a, w'⟩
    · simp only [Option.some.injEq] at h; exact Or.inl ⟨e, rfl, h.symm⟩
    · exact Or.inr ⟨a, w', rfl, h⟩

/-! ## The section and its functions -/

/-- What the simulation fixes about one source function: the function and its place, its
    translation context (`c.mf` is the machine function), its frame, its liveness certificate
    with the live sets of its points, the block each source block's region ends in, and each
    block's callee places (by block id). -/
structure Fn where
  f : HFunc
  k : Nat
  c : FCtx
  F : Frame
  L : Live
  pts : NatMap (List (List Nat))
  tb : NatMap Nat
  cs : Nat → List Nat

/-- The machine block where the region of source block `b` starts. -/
def Fn.start (fn : Fn) (b : HBlock) : Option (Nat × Block) := do
  let mb ← fn.c.bm.find? b.id
  let mblk ← fn.c.mf.block? mb
  some (mb, mblk)

/-- The walk's state before statement `i` of block `b`. -/
def Fn.pos (fn : Fn) (b : HBlock) (i : Nat) : Option (Nat × List Stmt × List Nat) := do
  let (mb, mblk) ← fn.start b
  walkTo fn.c fn.F.vm b.body mb mblk.body (fn.cs b.id) i

/-- The values live before statement `i` of block `b` (and, at the body's length, before its
    terminator). -/
def Fn.live (fn : Fn) (b : HBlock) (i : Nat) : List Nat := ptsAt fn.pts b.id i

section defs

variable (P : HSection) (I : Fe.EVM.Env) (cM : Ctx) (S : SecFacts) (Dr : Derived)

/-- The function's results are derived (rule S8). -/
def Fn.dret (fn : Fn) : Bool := Dr.rets.contains fn.k

/-- Returned values, against the machine's: each machine value is the word of a related H value
    of the result type, an integer or a pointer into a heap block (rule S3: no value with
    origins is returned). -/
def RetRel (g : Ghost) (hst : H.State) (dret : Bool) (rets : List Ty) (valsH : List H.Val)
    (vals : List Val) : Prop :=
  List.Forall₂ (fun (v : H.Val) (mv : Val) => ∃ m, mv = Val.int 256 m ∧ VRel g S.z dret v m ∧
    ValOk hst v ∧ ∀ b o, v = .ptr b o → g.heap b) valsH vals ∧
  List.Forall₂ (fun (v : H.Val) (t : Ty) => v.fits t = true) valsH rets

/-- How a run of a function ends against the machine's result `r` of it, from ghost `g` and
    state `hst` at its start: H halts in an outcome that excuses `r`, or both return, related,
    the ghost extended. -/
def FRel (fn : Fn) (g : Ghost) (hst : H.State) (fo : FOut)
    (r : Except (Exit World) (List Val × World)) : Prop :=
  (∃ o, fo = .halt o ∧ Excuses o r) ∨
  ∃ vals w' valsH hst' g', r = .ok (vals, w') ∧ fo = .ret valsH hst' ∧ Inv S hst' w' g' ∧
    GhostLe fn.F.fpf g g' hst hst' ∧ RetRel S g' hst' (fn.dret Dr) fn.f.rets valsH vals

/-- What H's terminator of block `b` does from `env`, `st`, as an `ExecBlocks` rule needs. -/
def TermRun (f : HFunc) (b : HBlock) (env : HEnv) (st : H.State) (fo : FOut) : Prop :=
  (∃ d, stepTerm I env st b.term = .goto d ∧ ExecBlocks P I f env (some b.id) d st fo) ∨
  (∃ vals, stepTerm I env st b.term = .ret vals ∧ fo = .ret vals st) ∨
  (∃ o, stepTerm I env st b.term = .halt o ∧ fo = .halt o)

/-- H's run of the statements `rest` of block `b` and on, against the machine's result `r` of
    the function's run, for a function run that started at ghost `g₀` and state `hst₀`. -/
def Tail (fn : Fn) (g₀ : Ghost) (hst₀ : H.State) (b : HBlock) (rest : List HStmt) (envH : HEnv)
    (hst : H.State) (r : Except (Exit World) (List Val × World)) : Prop :=
  ∃ ob, ExecBody P I envH rest hst ob ∧ match ob with
    | .halt o => Excuses o r
    | .cont env₂ st₂ => ∃ fo, TermRun P I fn.f b env₂ st₂ fo ∧ FRel S Dr fn g₀ hst₀ fo r

/-- The relation on an edge into block `db` from `pH` (none at the function's entry): the
    values live into the block from there are related. -/
def EdgeRel (fn : Fn) (g : Ghost) (hst : H.State) (pH : Option Nat) (db : HBlock) (envH : HEnv)
    (envM : Env) : Prop :=
  match pH with
  | none => db.phis = [] ∧ EnvRel S.z fn.F g hst envH envM (liveGet fn.L db.id)
  | some p => ∃ pb ∈ fn.f.blocks, pb.id = p ∧ db.id ∈ pb.term.succs ∧
      EnvRel S.z fn.F g hst envH envM (liveOut fn.f fn.L pb)

/-- The machine's previous block is where the region of H's ends. -/
def PrevOk (fn : Fn) (pH prev : Option Nat) : Prop :=
  ∀ p, pH = some p → ∃ tp, fn.tb.find? p = some tp ∧ prev = some tp

/-- Arguments of a call to `fn`, against the machine's. -/
def ArgRel (fn : Fn) (g : Ghost) (hst : H.State) (vs : List H.Val) (args : List Val) : Prop :=
  vs.length = fn.f.params.length ∧ args.length = fn.f.params.length ∧
  ∀ (j : Nat) (p : Nat × Ty) (v : H.Val) (a : Val), fn.f.params[j]? = some p → vs[j]? = some v →
    args[j]? = some a → ∃ m, a = Val.int 256 m ∧ v.fits p.2 = true ∧ VRel g S.z (fn.F.D p.1) v m ∧ ValOk hst v ∧
      OrigOk g hst fn.F.R fn.F.fpf (origOf fn.F.O (.var p.1)) v

/-- The call contract of oracle `O` for the section's functions `fns` (by place): from related
    arguments and states, every run of a call that ends is matched by a run of H's. -/
def CallP (fns : Nat → Option Fn) (O : Oracle) : Prop :=
  ∀ kg fg, fns kg = some fg → ∀ args vs g hst w, Inv S hst w g → ArgRel S fg g hst vs args →
    ∀ r, (O fg.f.name args).exec I w = some r →
      ∃ fo, ExecFunc P I fg.f.name vs hst fo ∧ FRel S Dr fg g hst fo r

/-- `TemplOk` for one oracle. -/
def TemplOkC (O : Oracle) (F : Frame) (g : Ghost) (hst : H.State) (w : World) (envH : HEnv)
    (envM : Env) (s : HStmt) (L' : List Nat) (pre : List Stmt) : Prop :=
  ∀ r, (runBodyO O cM envM pre).exec I w = some r → StepOk P I S F g hst envH s L' r

theorem TemplOk.c {O : Oracle} {F : Frame} {g : Ghost} {hst : H.State} {w : World} {envH : HEnv}
    {envM : Env} {s : HStmt} {L' : List Nat} {pre : List Stmt}
    (h : TemplOk P I cM S F g hst w envH envM s L' pre) :
    TemplOkC P I cM S O F g hst w envH envM s L' pre := h O

/-- The machine run of a diamond's template from block `mb`: its statements `ms` in `mb`, the
    branch on `cv`, the arm taken (the join itself, or a block without phis that jumps to it),
    the join's phis, and the template's statements `pre₂` at the start of the join's body. -/
def diaRun (O : Oracle) (mf : Func) (mb : Nat) (ms : List Stmt) (cv : Operand) (t₁ t₂ jn : Nat)
    (jb : Block) (pre₂ : List Stmt) (envM : Env) : FeM Env :=
  runBodyO O cM envM ms >>= fun env₁ => evalInt env₁ cv >>= fun p =>
    (if (if p.2 != 0 then t₁ else t₂) = jn then pure (env₁, mb)
     else match mf.block? (if p.2 != 0 then t₁ else t₂) with
       | some ab => runBodyO O cM env₁ ab.body >>= fun e => pure (e, if p.2 != 0 then t₁ else t₂)
       | none => stuck) >>= fun q => Fe.Sonatina.enter q.1 (some q.2) jb >>= fun e =>
    runBodyO O cM e pre₂

end defs

/-! ## The obligations of a function -/

section obl

variable (P : HSection) (I : Fe.EVM.Env) (cM : Ctx) (S : SecFacts) (Dr : Derived)
  (CP : Oracle → Prop) (Q : Fn → HBlock → Nat → HEnv → Prop)

/-- A statement whose template is a list of machine statements of its block (all but the two
    diamonds and the terminal fixed buffer): run with calls by an oracle that satisfies the call
    contract, they end as H's step does; the walk stays in block `mb`. -/
def StdK (fn : Fn) (b : HBlock) (i : Nat) (s : HStmt) (mb : Nat) (ms : List Stmt) (mb' : Nat)
    (ms' : List Stmt) : Prop :=
  ∀ O, CP O → ∀ g hst w envH envM, Inv S hst w g → EnvRel S.z fn.F g hst envH envM (fn.live b i) →
    ∃ pre, ms = pre ++ ms' ∧ mb' = mb ∧
      TemplOkC P I cM S O fn.F g hst w envH envM s (fn.live b (i + 1)) pre

/-- A statement whose template branches: block `mb` runs the statements `ms` left and branches
    on `cv`; an arm is the join `mb'` or a block without phis that jumps to it; the join's phis
    and the statements `pre₂` its body starts with end the template, whose run (`diaRun`) ends as
    H's step does. -/
def DiaK (fn : Fn) (b : HBlock) (i : Nat) (s : HStmt) (mb : Nat) (ms : List Stmt) (mb' : Nat)
    (ms' : List Stmt) : Prop :=
  ∃ mblk cv t₁ t₂ jb pre₂, fn.c.mf.block? mb = some mblk ∧ mblk.term = .br cv t₁ t₂ ∧
    fn.c.mf.block? mb' = some jb ∧ jb.body = pre₂ ++ ms' ∧
    (∀ a, (a = t₁ ∨ a = t₂) → a ≠ mb' →
      ∃ ab, fn.c.mf.block? a = some ab ∧ ab.phis = [] ∧ ab.term = .jump mb') ∧
    ∀ O, CP O → ∀ g hst w envH envM, Inv S hst w g →
      EnvRel S.z fn.F g hst envH envM (fn.live b i) →
      ∀ r, (diaRun cM O fn.c.mf mb ms cv t₁ t₂ mb' jb pre₂ envM).exec I w = some r →
        StepOk P I S fn.F g hst envH s (fn.live b (i + 1)) r

/-- A terminal fixed buffer (rule S6): every run of the rest of the function from the site that
    ends, with any block runner below the machine's, is matched by H's run of the rest.  The
    site's H environment satisfies the invariant `Q` of H's runs of the function. -/
def FixK (fn : Fn) (b : HBlock) (i : Nat) (mb : Nat) (ms : List Stmt) : Prop :=
  ∀ O, CP O → ∀ g₀ hst₀ g hst w envH envM, Inv S hst w g →
    EnvRel S.z fn.F g hst envH envM (fn.live b i) → Q fn b i envH →
    ∀ B : Env → Option Nat → Nat → FeM (List Val),
      (∀ e p id w r, (B e p id).exec I w = some r → (runBlocksO O cM fn.c.mf e p id).exec I w = some r) →
      ∀ mblk, fn.c.mf.block? mb = some mblk →
        ∀ r, (runBodyO O cM envM ms >>= fun e => termK B mb e mblk.term).exec I w = some r →
          Tail P I S Dr fn g₀ hst₀ b (b.body.drop i) envH hst r

/-- Every statement of every block, where the walk reaches it, is one of the three kinds. -/
def StmtObl (fn : Fn) : Prop :=
  ∀ b ∈ fn.f.blocks, ∀ i s, b.body[i]? = some s → ∀ mb ms cs, fn.pos b i = some (mb, ms, cs) →
    ∀ vm' mb' ms' ds, stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds) →
      StdK P I cM S CP fn b i s mb ms mb' ms' ∨
      DiaK P I cM S CP fn b i s mb ms mb' ms' ∨ FixK P I cM S Dr CP Q fn b i mb ms

/-- Every block's terminator, with the machine statements left in the block its region ends in:
    H halts excusing the machine's result, or both go to related blocks, or both return. -/
def TermObl (fn : Fn) : Prop :=
  ∀ b ∈ fn.f.blocks, ∀ mb ms cs, fn.pos b b.body.length = some (mb, ms, cs) →
    fn.tb.find? b.id = some mb ∧ ∀ mblk, fn.c.mf.block? mb = some mblk →
    ∀ (O : Oracle) g hst w envH envM, Inv S hst w g →
      EnvRel S.z fn.F g hst envH envM (fn.live b b.body.length) →
      ∀ r, (runBodyO O cM envM ms >>= fun e => runTerm e mblk.term).exec I w = some r →
        (∃ o, stepTerm I envH hst b.term = .halt o ∧ Excuses o r) ∨
        (∃ envM' d' db dblk, r = .ok (.goto envM' d', w) ∧ stepTerm I envH hst b.term = .goto db.id ∧
          db ∈ fn.f.blocks ∧ fn.start db = some (d', dblk) ∧
          EdgeRel S fn g hst (some b.id) db envH envM') ∨
        (∃ vals w' valsH, r = .ok (.done vals, w') ∧ stepTerm I envH hst b.term = .ret valsH ∧
          Inv S hst w' g ∧ RetRel S g hst (fn.dret Dr) fn.f.rets valsH vals)

/-- Every block's entry: the machine's phis, entered from the block a source predecessor's
    region ends in, give related values to the values live at the start of its body. -/
def PhiObl (fn : Fn) : Prop :=
  ∀ db ∈ fn.f.blocks, ∀ mb mblk, fn.start db = some (mb, mblk) →
    ∀ pH prev g hst envH envM w env₁, EdgeRel S fn g hst pH db envH envM → PrevOk fn pH prev →
      (Fe.Sonatina.enter envM prev mblk).exec I w = some (.ok (env₁, w)) →
      ∃ envH₁, H.enter envH pH db = some envH₁ ∧ EnvRel S.z fn.F g hst envH₁ env₁ (fn.live db 0)

/-- The function's entry: the machine's entry is the region start of the source entry, or a
    block that only jumps there; related arguments bind related parameters. -/
def EntryObl (fn : Fn) : Prop :=
  ∃ e me be ebl, fn.f.blocks.head? = some e ∧ fn.c.mf.blocks.head? = some me ∧
    fn.start e = some (be, ebl) ∧ (me.id = be ∨ (me.phis = [] ∧ me.body = [] ∧ me.term = .jump be)) ∧
    ∀ args vs g hst envM w, ArgRel S fn g hst vs args →
      (Fe.Sonatina.bind {} fn.c.mf.params args).exec I w = some (.ok (envM, w)) →
      ∃ envH, bindVals {} fn.f.params vs = some envH ∧ EdgeRel S fn g hst none e envH envM

/-- The obligations of one function of the section.  `Q` is an invariant of H's environments at
    the points of the function's runs (before statement `i` of block `b`): it holds at the entry,
    each statement and each edge keep it. -/
structure FnOk (low : Module) (fn : Fn) : Prop where
  hname : low.func? fn.f.name = some fn.c.mf
  hsrc : P.module.func? fn.f.name = some fn.f
  blk : ∀ b ∈ fn.f.blocks, fn.f.block? b.id = some b
  walks : ∀ b ∈ fn.f.blocks, (fn.pos b b.body.length).isSome
  entry : EntryObl I S fn
  phi : PhiObl I S fn
  stmt : StmtObl P I cM S Dr CP Q fn
  term : TermObl I cM S Dr fn
  qEntry : ∀ e, fn.f.blocks.head? = some e → ∀ vs envH, bindVals {} fn.f.params vs = some envH →
    ∀ envH₁, H.enter envH none e = some envH₁ → Q fn e 0 envH₁
  qStep : ∀ b ∈ fn.f.blocks, ∀ i s, b.body[i]? = some s → ∀ envH hst envH' hst', Q fn b i envH →
    ExecBody P I envH [s] hst (.cont envH' hst') → Q fn b (i + 1) envH'
  qEdge : ∀ b ∈ fn.f.blocks, ∀ envH hst d, Q fn b b.body.length envH →
    stepTerm I envH hst b.term = .goto d → ∀ db ∈ fn.f.blocks, db.id = d →
    ∀ envH₁, H.enter envH (some b.id) db = some envH₁ → Q fn db 0 envH₁

/-- What the motive of `blocks_sim` says of a run of machine block `id` of `fn`, entered from
    `prev` with `env` in world `w`, that ends in `r`: it is a run of `runBlocksO` (the
    approximant is below the fixpoint); at a region start it is matched by H's run of the source
    block; at an arm or the join of a diamond, by H's run of the rest of the source block from the
    diamond's statement. -/
def BQ (fn : Fn) (O : Oracle) (env : Env) (prev : Option Nat) (id : Nat) (w : World)
    (r : Except (Exit World) (List Val × World)) : Prop :=
  (runBlocksO O cM fn.c.mf env prev id).exec I w = some r ∧
  (∀ b ∈ fn.f.blocks, ∀ mblk pH envH g g₀ hst hst₀, fn.start b = some (id, mblk) →
    PrevOk fn pH prev → EdgeRel S fn g hst pH b envH env → Inv S hst w g →
    GhostLe fn.F.fpf g₀ g hst₀ hst → (∀ b, g₀.live b → b < hst₀.blocks.size) →
    (∀ envH₁, H.enter envH pH b = some envH₁ → Q fn b 0 envH₁) →
    ∃ fo, ExecBlocks P I fn.f envH pH b.id hst fo ∧ FRel S Dr fn g₀ hst₀ fo r) ∧
  (∀ b ∈ fn.f.blocks, ∀ i s mb ms cs vm' jn ms' ds cs' mblk cv t₁ t₂ jb pre₂ envH envM g g₀ hst hst₀
      w₀,
    b.body[i]? = some s → fn.pos b i = some (mb, ms, cs) →
    stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', jn, ms', ds) →
    fn.pos b (i + 1) = some (jn, ms', cs') →
    fn.c.mf.block? mb = some mblk → mblk.term = .br cv t₁ t₂ → fn.c.mf.block? jn = some jb →
    jb.body = pre₂ ++ ms' → Inv S hst w₀ g → GhostLe fn.F.fpf g₀ g hst₀ hst →
    (∀ b, g₀.live b → b < hst₀.blocks.size) → Q fn b i envH →
    (∀ x, (diaRun cM O fn.c.mf mb ms cv t₁ t₂ jn jb pre₂ envM).exec I w₀ = some x →
      StepOk P I S fn.F g hst envH s (fn.live b (i + 1)) x) →
    ((id = jn ∧ ∃ p, prev = some p ∧ ∀ x, (Fe.Sonatina.enter env (some p) jb >>= fun e =>
        runBodyO O cM e pre₂).exec I w = some x →
        (diaRun cM O fn.c.mf mb ms cv t₁ t₂ jn jb pre₂ envM).exec I w₀ = some x) ∨
     (id ≠ jn ∧ prev = some mb ∧ ∃ ab, fn.c.mf.block? id = some ab ∧ ab.phis = [] ∧
        ab.term = .jump jn ∧ ∀ x, (runBodyO O cM env ab.body >>= fun e =>
          Fe.Sonatina.enter e (some id) jb >>= fun e' => runBodyO O cM e' pre₂).exec I w = some x →
          (diaRun cM O fn.c.mf mb ms cv t₁ t₂ jn jb pre₂ envM).exec I w₀ = some x)) →
    Tail P I S Dr fn g₀ hst₀ b (b.body.drop i) envH hst r)

end obl

/-! ## The simulation -/

section sim

variable {P : HSection} {I : Fe.EVM.Env} {cM : Ctx} {S : SecFacts} {Dr : Derived}
  {CP : Oracle → Prop} {Q : Fn → HBlock → Nat → HEnv → Prop}

/-- "Every run that ends from environment `I` satisfies `Q`" is admissible. -/
theorem admissible_endsAt {α : Type} (I₀ : Fe.EVM.Env)
    (Q : World → Except (Exit World) (α × World) → Prop) :
    admissible (fun x : FeM α => ∀ w r, x.exec I₀ w = some r → Q w r) := by
  have hadm := admissible_ends (α := α) (fun I' w r => I' = I₀ → Q w r)
  have e : (fun x : FeM α => ∀ w r, x.exec I₀ w = some r → Q w r) =
      fun x => ∀ I' w r, x.exec I' w = some r → I' = I₀ → Q w r := by
    funext x
    exact propext ⟨fun hx I' w r hr e => by subst e; exact hx w r hr,
      fun hx w r hr => hx I₀ w r hr rfl⟩
  rw [e]; exact hadm

/-- H's run of a block, from its entry and the run of its body and on. -/
theorem tail_blocks {fn : Fn} {g₀ : Ghost} {hst₀ : H.State} {b : HBlock} {envH envH₁ : HEnv}
    {pH : Option Nat} {hst : H.State} {r : Except (Exit World) (List Val × World)}
    (hb : fn.f.block? b.id = some b) (he : H.enter envH pH b = some envH₁)
    (ht : Tail P I S Dr fn g₀ hst₀ b b.body envH₁ hst r) :
    ∃ fo, ExecBlocks P I fn.f envH pH b.id hst fo ∧ FRel S Dr fn g₀ hst₀ fo r := by
  obtain ⟨ob, hbody, hk⟩ := ht
  cases ob with
  | halt o => exact ⟨.halt o, .bodyHalt hb he hbody, Or.inl ⟨o, rfl, hk⟩⟩
  | cont env₂ st₂ =>
    obtain ⟨fo, hrun, hfr⟩ := hk
    rcases hrun with ⟨d, hd, hr⟩ | ⟨vals, hv, rfl⟩ | ⟨o, ho, rfl⟩
    · exact ⟨fo, .goto hb he hbody hd hr, hfr⟩
    · exact ⟨_, .ret hb he hbody hv, hfr⟩
    · exact ⟨_, .halt hb he hbody ho, hfr⟩

/-- H halts at statement `s` of the rest `s :: rest`: its run of the rest halts so. -/
theorem tail_halt {fn : Fn} {g₀ : Ghost} {hst₀ : H.State} {b : HBlock} {envH : HEnv}
    {hst : H.State} {s : HStmt} {rest : List HStmt} {o : Outcome}
    {r : Except (Exit World) (List Val × World)}
    (hall : ∀ rest, ExecBody P I envH (s :: rest) hst (.halt o)) (hx : Excuses o r) :
    Tail P I S Dr fn g₀ hst₀ b (s :: rest) envH hst r := ⟨.halt o, hall rest, hx⟩

/-- The rest of the block from statement `s` on, from H's step at `s` and the rest after it. -/
theorem tail_step {fn : Fn} {g₀ : Ghost} {hst₀ : H.State} {b : HBlock} {envH envH' : HEnv}
    {hst hst' : H.State} {s : HStmt} {rest : List HStmt}
    {r : Except (Exit World) (List Val × World)}
    (hc : ∀ rest o, ExecBody P I envH' rest hst' o → ExecBody P I envH (s :: rest) hst o)
    (ht : Tail P I S Dr fn g₀ hst₀ b rest envH' hst' r) :
    Tail P I S Dr fn g₀ hst₀ b (s :: rest) envH hst r := by
  obtain ⟨ob, hbody, hk⟩ := ht
  exact ⟨ob, hc rest ob hbody, hk⟩

theorem drop_cons {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l.drop i = a :: l.drop (i + 1) := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hi, rfl⟩ := h
  exact List.drop_eq_getElem_cons hi

theorem pos_zero {fn : Fn} {b : HBlock} {mb : Nat} {mblk : Block}
    (h : fn.start b = some (mb, mblk)) : fn.pos b 0 = some (mb, mblk.body, fn.cs b.id) := by
  simp only [Fn.pos, h, Option.bind_eq_bind, Option.bind_some, walkTo]

theorem start_block {fn : Fn} {b : HBlock} {mb : Nat} {mblk : Block}
    (h : fn.start b = some (mb, mblk)) : fn.c.mf.block? mb = some mblk := by
  simp only [Fn.start, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨_, h1, _, h2, rfl, rfl⟩ := h
  exact h2

/-- The positions of block `b` that the walk reaches, one statement after another. -/
theorem pos_succ {fn : Fn} {b : HBlock} {i : Nat} {s : HStmt} {mb : Nat} {ms : List Stmt}
    {cs : List Nat} (hp : fn.pos b i = some (mb, ms, cs)) (hs : b.body[i]? = some s)
    (hw : (fn.pos b b.body.length).isSome) :
    ∃ vm' mb' ms' ds, stmt fn.c true fn.F.vm s mb ms (calleeOf s cs).1 = some (vm', mb', ms', ds) ∧
      fn.pos b (i + 1) = some (mb', ms', (calleeOf s cs).2) := by
  have hi : i < b.body.length := by
    rw [List.getElem?_eq_some_iff] at hs; exact hs.1
  unfold Fn.pos at hp hw ⊢
  cases hst : fn.start b with
  | none => rw [hst] at hp; cases hp
  | some st =>
    rw [hst] at hp hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hp hw ⊢
    have h1 := walkTo_le (i := i + 1) (by omega) hw
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨vm', mb', ms', ds, h, rfl⟩ := walkTo_succ hp hs hx
    exact ⟨vm', mb', ms', ds, h, hx⟩

theorem head_block {mf : Func} {me : Block} (h : mf.blocks.head? = some me) :
    mf.block? me.id = some me := by
  unfold Func.block?
  cases hb : mf.blocks with
  | nil => rw [hb] at h; cases h
  | cons x xs =>
    rw [hb] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp

theorem mem_of_head {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => cases h
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp

/-- The walk of a source block's statements, inside the step of `blocks_sim`: from the point
    before statement `i`, related, every run of the machine statements left in its block and on
    (the next blocks by the approximant `G`) that ends is matched by H's run of the rest of the
    source block. -/
theorem walk_sim {low : Module} {fn : Fn} (hfn : FnOk P I cM S Dr CP Q low fn) {O : Oracle}
    (hO : CP O) {G : Env → Option Nat → Nat → FeM (List Val)}
    (hG : ∀ env prev id w r, (G env prev id).exec I w = some r → BQ P I cM S Dr Q fn O env prev id w r)
    {b : HBlock} (hb : b ∈ fn.f.blocks) :
    ∀ n i, i + n = b.body.length → ∀ mb ms cs, fn.pos b i = some (mb, ms, cs) →
    ∀ mblk, fn.c.mf.block? mb = some mblk →
    ∀ g₀ hst₀ g hst w envH envM, Inv S hst w g → EnvRel S.z fn.F g hst envH envM (fn.live b i) →
    GhostLe fn.F.fpf g₀ g hst₀ hst → (∀ b, g₀.live b → b < hst₀.blocks.size) → Q fn b i envH →
    ∀ r, (runBodyO O cM envM ms >>= fun e => termK G mb e mblk.term).exec I w = some r →
      Tail P I S Dr fn g₀ hst₀ b (b.body.drop i) envH hst r := by
  intro n
  induction n with
  | zero =>
    intro i hi mb ms cs hp mblk hmb g₀ hst₀ g hst w envH envM hI hE hgl hlt hQ r h
    simp only [Nat.add_zero] at hi
    subst hi
    obtain ⟨htb, hT⟩ := hfn.term b hb mb ms cs hp
    have hT' := hT mblk hmb O g hst w envH envM hI hE
    rw [List.drop_length]
    simp only [termK_eq] at h
    have nil := ExecBody.nil (P := P) (I := I) (env := envH) (st := hst)
    rcases exec_bind_some h with ⟨e, h1, rfl⟩ | ⟨envE, w₁, h1, h2⟩
    · rcases hT' _ (exec_bind_error h1) with ⟨o, ho, hx⟩ | ⟨_, _, _, _, heq, _⟩ | ⟨_, _, _, heq, _⟩
      · exact ⟨_, nil, .halt o, Or.inr (Or.inr ⟨o, ho, rfl⟩), Or.inl ⟨o, rfl, Excuses.of_error hx⟩⟩
      · cases heq
      · cases heq
    · rcases exec_bind_some h2 with ⟨e, h3, rfl⟩ | ⟨nx, w₂, h3, h4⟩
      · rcases hT' _ (by rw [exec_bind_ok h1]; exact h3) with ⟨o, ho, hx⟩ | ⟨_, _, _, _, heq, _⟩ |
          ⟨_, _, _, heq, _⟩
        · exact ⟨_, nil, .halt o, Or.inr (Or.inr ⟨o, ho, rfl⟩), Or.inl ⟨o, rfl, Excuses.of_error hx⟩⟩
        · cases heq
        · cases heq
      · rcases hT' _ (by rw [exec_bind_ok h1]; exact h3) with ⟨o, ho, hx⟩ |
          ⟨envM', d', db, dblk, heq, hgo, hdb, hstart, hedge⟩ | ⟨vals, w', valsH, heq, hret, hI', hrr⟩
        · exact ⟨_, nil, .halt o, Or.inr (Or.inr ⟨o, ho, rfl⟩), Or.inl ⟨o, rfl, Excuses.of_ok hx r⟩⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
          obtain ⟨h5, h6⟩ := heq
          subst h5
          subst w₂
          obtain ⟨fo, hex, hfr⟩ := (hG envM' (some mb) d' w r h4).2.1 db hdb dblk (some b.id) envH
            g g₀ hst hst₀ hstart (fun p hp => ⟨mb, by cases hp; exact htb, rfl⟩) hedge hI hgl hlt
            (fun envH₁ he => hfn.qEdge b hb envH hst db.id hQ hgo db hdb rfl envH₁ he)
          exact ⟨_, nil, fo, Or.inl ⟨db.id, hgo, hex⟩, hfr⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
          obtain ⟨h5, h6⟩ := heq
          subst h5
          subst w₂
          simp only [Fe.M.exec_pure, Option.some.injEq] at h4
          subst h4
          exact ⟨_, nil, _, Or.inr (Or.inl ⟨valsH, hret, rfl⟩),
            Or.inr ⟨vals, w', valsH, hst, g, rfl, rfl, hI', hgl, hrr⟩⟩
  | succ n ih =>
    intro i hi mb ms cs hp mblk hmb g₀ hst₀ g hst w envH envM hI hE hgl hlt hQ r h
    obtain ⟨s, hs⟩ : ∃ s, b.body[i]? = some s :=
      ⟨b.body[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨vm', mb', ms', ds, hstm, hp'⟩ := pos_succ hp hs (hfn.walks b hb)
    rcases hfn.stmt b hb i s hs mb ms cs hp vm' mb' ms' ds hstm with hK | hK | hK
    · obtain ⟨pre, rfl, hmm, hT⟩ := hK O hO g hst w envH envM hI hE
      rw [hmm] at hp'
      rw [drop_cons hs]
      rw [runBodyO_append, bind_assoc] at h
      rcases exec_bind_some h with ⟨e, h1, rfl⟩ | ⟨envM₁, w₁, h1, h2⟩
      · rcases hT _ h1 with ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
        · exact tail_halt hall (Excuses.of_error hx)
        · cases heq
      · rcases hT _ h1 with ⟨o, hall, hx⟩ | ⟨envM', w', heq, envH', hst', g', hI', hE', hgl', hc⟩
        · exact tail_halt hall (Excuses.of_ok hx r)
        · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact tail_step hc (ih (i + 1) (by omega) mb ms' _ hp' mblk hmb g₀ hst₀ g' hst' w₁ envH'
            envM₁ hI' hE' (hgl.trans hgl' hlt) hlt
            (hfn.qStep b hb i s hs envH hst envH' hst' hQ (hc [] _ ExecBody.nil)) r h2)
    · obtain ⟨mblk', cv, t₁, t₂, jb, pre₂, hmb', hbr, hjb, hms', harms, hD⟩ := hK
      rw [hmb] at hmb'
      cases hmb'
      have hstep := hD O hO g hst w envH envM hI hE
      rw [hbr] at h
      simp only [termK] at h
      rcases exec_bind_some h with ⟨e, h1, rfl⟩ | ⟨env₁, w₁, h1, h2⟩
      · rcases hstep _ (by unfold diaRun; exact exec_bind_error h1) with ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
        · rw [drop_cons hs]; exact tail_halt hall (Excuses.of_error hx)
        · cases heq
      · rcases exec_bind_some h2 with ⟨e, h3, rfl⟩ | ⟨⟨u, v⟩, w₂, h3, h4⟩
        · rcases hstep _ (by unfold diaRun; rw [exec_bind_ok h1]; exact exec_bind_error h3) with
            ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
          · rw [drop_cons hs]; exact tail_halt hall (Excuses.of_error hx)
          · cases heq
        · have hq := (hG env₁ (some mb) _ w₂ r h4).2.2 b hb i s mb ms cs vm' mb' ms' ds _ mblk cv
            t₁ t₂ jb pre₂ envH envM g g₀ hst hst₀ w hs hp hstm hp' hmb hbr hjb hms' hI hgl hlt hQ hstep
          by_cases ha : (if v != 0 then t₁ else t₂) = mb'
          · refine hq (Or.inl ⟨ha, mb, rfl, fun x hx => ?_⟩)
            unfold diaRun
            rw [exec_bind_ok h1, exec_bind_ok h3]
            simp only [ha, ite_true, pure_bind]
            exact hx
          · have hor : (if v != 0 then t₁ else t₂) = t₁ ∨ (if v != 0 then t₁ else t₂) = t₂ := by
              split <;> simp
            obtain ⟨ab, hab, hph, hterm⟩ := harms _ hor ha
            refine hq (Or.inr ⟨ha, rfl, ab, hab, hph, hterm, fun x hx => ?_⟩)
            unfold diaRun
            rw [exec_bind_ok h1, exec_bind_ok h3]
            simp only [ha, ite_false, hab, bind_assoc, pure_bind]
            exact hx
    · exact hK O hO g₀ hst₀ g hst w envH envM hI hE hQ G (fun e p id w r h => (hG e p id w r h).1)
        mblk hmb r h

/-- The blocks of a function, run with calls by an oracle that satisfies the call contract: by
    fixpoint induction, every run that ends satisfies `BQ`. -/
theorem blocks_sim {low : Module} {fn : Fn} (hfn : FnOk P I cM S Dr CP Q low fn) {O : Oracle}
    (hO : CP O) : ∀ env prev id w r, (runBlocksO O cM fn.c.mf env prev id).exec I w = some r →
      BQ P I cM S Dr Q fn O env prev id w r := by
  refine runBlocksO.fixpoint_induct O cM fn.c.mf
    (fun G => ∀ env prev id w r, (G env prev id).exec I w = some r →
      BQ P I cM S Dr Q fn O env prev id w r) ?_ ?_
  · exact Fe.M.admissible_arrow (fun env (G : Option Nat → Nat → FeM (List Val)) =>
        ∀ prev id w r, (G prev id).exec I w = some r → BQ P I cM S Dr Q fn O env prev id w r)
      fun env => Fe.M.admissible_arrow (fun prev (G : Nat → FeM (List Val)) =>
        ∀ id w r, (G id).exec I w = some r → BQ P I cM S Dr Q fn O env prev id w r)
      fun prev => Fe.M.admissible_arrow (fun id (x : FeM (List Val)) =>
        ∀ w r, x.exec I w = some r → BQ P I cM S Dr Q fn O env prev id w r)
      fun id => admissible_endsAt I _
  · intro G hG env prev id w r h
    refine ⟨?_, ?_, ?_⟩
    · rw [runBlocksO]
      rcases exec_bind_some h with ⟨e, h1, rfl⟩ | ⟨nx, w₁, h1, h2⟩
      · exact exec_bind_error h1
      · rw [exec_bind_ok h1]
        cases nx with
        | goto e d => exact (hG e (some id) d w₁ r h2).1
        | done v => exact h2
    · intro b hb mblk pH envH g g₀ hst hst₀ hstart hprev hedge hI hgl hlt hQe
      have hblk := start_block hstart
      simp only [stepBlock, hblk, bind_assoc] at h
      rcases exec_bind_some h with ⟨e, h1, -⟩ | ⟨env₁, w₁, h1, h2⟩
      · obtain ⟨a, ha⟩ := Quiet.enter env prev mblk I w _ h1
        cases ha
      · have hw := Quiet.world (Quiet.enter env prev mblk) h1
        subst hw
        obtain ⟨envH₁, he, hE⟩ := hfn.phi b hb id mblk hstart pH prev g hst envH env w env₁ hedge
          hprev h1
        refine tail_blocks (hfn.blk b hb) he ?_
        have h2' : (runBodyO O cM env₁ mblk.body >>= fun e => termK G id e mblk.term).exec I w =
            some r := by
          simp only [termK_eq]; exact h2
        have := walk_sim hfn hO hG hb b.body.length 0 (by omega) id mblk.body (fn.cs b.id)
          (pos_zero hstart) mblk hblk g₀ hst₀ g hst w envH₁ env₁ hI hE hgl hlt (hQe envH₁ he) r h2'
        simpa only [List.drop_zero] using this
    · intro b hb i s mb ms cs vm' jn ms' ds cs' mblk cv t₁ t₂ jb pre₂ envH envM g g₀ hst hst₀ w₀ hs
        hp hstm hp' hmb hbr hjb hms' hI hgl hlt hQ hstep hkind
      have hi : i < b.body.length := by rw [List.getElem?_eq_some_iff] at hs; exact hs.1
      rcases hkind with ⟨rfl, p, rfl, hpre⟩ | ⟨hne, rfl, ab, hab, hph, hterm, hpre⟩
      · simp only [stepBlock, hjb, hms', runBodyO_append, bind_assoc] at h
        have h' : ((Fe.Sonatina.enter env (some p) jb >>= fun e => runBodyO O cM e pre₂) >>=
            fun e => runBodyO O cM e ms' >>= fun e => termK G id e jb.term).exec I w = some r := by
          simp only [bind_assoc, termK_eq]; exact h
        rcases exec_bind_some h' with ⟨e, h1, rfl⟩ | ⟨env₂, w₁, h1, h2⟩
        · rcases hstep _ (hpre _ h1) with ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
          · rw [drop_cons hs]; exact tail_halt hall (Excuses.of_error hx)
          · cases heq
        · rcases hstep _ (hpre _ h1) with ⟨o, hall, hx⟩ |
            ⟨envM', w', heq, envH', hst', g', hI', hE', hgl', hc⟩
          · rw [drop_cons hs]; exact tail_halt hall (Excuses.of_ok hx r)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            obtain ⟨h5, h6⟩ := heq
            subst envM'
            subst w'
            rw [drop_cons hs]
            exact tail_step hc (walk_sim hfn hO hG hb (b.body.length - (i + 1)) (i + 1) (by omega)
              id ms' cs' hp' jb hjb g₀ hst₀ g' hst' w₁ envH' env₂ hI' hE' (hgl.trans hgl' hlt)
              hlt (hfn.qStep b hb i s hs envH hst envH' hst' hQ (hc [] _ ExecBody.nil)) r h2)
      · simp only [stepBlock, hab, enter_nil hph, pure_bind, hterm, runTerm, bind_assoc] at h
        rcases exec_bind_some h with ⟨e, h1, rfl⟩ | ⟨e, w₁, h1, h2⟩
        · rcases hstep _ (hpre _ (exec_bind_error h1)) with ⟨o, hall, hx⟩ | ⟨_, _, heq, _⟩
          · rw [drop_cons hs]; exact tail_halt hall (Excuses.of_error hx)
          · cases heq
        · exact (hG e (some id) jn w₁ r h2).2.2 b hb i s mb ms cs vm' jn ms' ds cs' mblk cv t₁ t₂ jb
            pre₂ envH envM g g₀ hst hst₀ w₀ hs hp hstm hp' hmb hbr hjb hms' hI hgl hlt hQ hstep
            (Or.inl ⟨rfl, id, rfl, fun x hx => hpre x (by rw [exec_bind_ok h1]; exact hx)⟩)

/-- A function run with calls by an oracle that satisfies the call contract satisfies it. -/
theorem func_sim {low : Module} {fns : Nat → Option Fn}
    (hall : ∀ kg fg, fns kg = some fg → FnOk P I cM S Dr (CallP P I S Dr fns) Q low fg)
    {O : Oracle} (hO : CallP P I S Dr fns O) :
    CallP P I S Dr fns (fun name args => runFuncO O cM (low.func? name) args) := by
  intro kg fg hfg args vs g hst w hI hA r h
  have hfn := hall kg fg hfg
  obtain ⟨e, me, be, ebl, he, hme, hstart, hent, hbind⟩ := hfn.entry
  simp only [hfn.hname, runFuncO, hme] at h
  rcases exec_bind_some h with ⟨x, h1, -⟩ | ⟨envM, w₁, h1, h2⟩
  · obtain ⟨a, ha⟩ := Quiet.bindEnv {} fg.c.mf.params args I w _ h1
    cases ha
  · have hw := Quiet.world (Quiet.bindEnv {} fg.c.mf.params args) h1
    subst hw
    obtain ⟨envH, hbv, hedge⟩ := hbind args vs g hst envM w hA h1
    have hR : ∀ prev, (runBlocksO O cM fg.c.mf envM prev be).exec I w = some r →
        ∃ fo, ExecFunc P I fg.f.name vs hst fo ∧ FRel S Dr fg g hst fo r := by
      intro prev hr
      obtain ⟨fo, hex, hfr⟩ := (blocks_sim hfn hO envM prev be w r hr).2.1 e (mem_of_head he) ebl
        none envH g g hst hst hstart (fun p hp => by cases hp) hedge hI (GhostLe.refl _ _ _)
        hI.live_lt (fun envH₁ hen => hfn.qEntry e he vs envH hbv envH₁ hen)
      exact ⟨fo, ExecFunc.mk hfn.hsrc he hbv hex, hfr⟩
    rcases hent with hid | ⟨hph, hbody, hterm⟩
    · rw [hid] at h2; exact hR none h2
    · rw [runBlocksO] at h2
      simp only [stepBlock, head_block hme, enter_nil hph, hbody, runBodyO, hterm, runTerm,
        pure_bind] at h2
      exact hR (some me.id) h2

/-- The call contract of the runs with calls at most `n` deep. -/
theorem callP_runFuncN {low : Module} {fns : Nat → Option Fn}
    (hall : ∀ kg fg, fns kg = some fg → FnOk P I cM S Dr (CallP P I S Dr fns) Q low fg) :
    ∀ n, CallP P I S Dr fns (runFuncN low cM n)
  | 0 => by
    intro kg fg hfg args vs g hst w hI hA r h
    simp only [runFuncN, stuck, Fe.M.exec_diverge, reduceCtorEq] at h
  | n + 1 => func_sim hall (callP_runFuncN hall n)

/-- The call contract of the machine module's runs. -/
theorem callP_runFunc {low : Module} {fns : Nat → Option Fn}
    (hall : ∀ kg fg, fns kg = some fg → FnOk P I cM S Dr (CallP P I S Dr fns) Q low fg) :
    CallP P I S Dr fns (runFunc low cM) := by
  intro kg fg hfg args vs g hst w hI hA r h
  obtain ⟨n, hn⟩ := runFunc_index low cM _ _ I w r h
  exact callP_runFuncN hall n kg fg hfg args vs g hst w hI hA r hn

end sim

end Fe.Sonatina.Stage3.Place
