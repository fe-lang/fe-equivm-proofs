import Fe.Sonatina.Steps.Oracle
import Fe.Sonatina.Steps.Dom
import Fe.Sonatina.Steps.Record

/-!
# The `noreturn` claims of a pass's summary table (design §3.3, review H-3, review 6 F-5)

A pass reads a table of function summaries (`func_behavior`).  Of its claims only `noreturn` is
checked and used: `cfg_cleanup` cuts a block after a call to a function the table claims does
not return (`trimIdx`, `cut`).  `SummariesOk O M`: every function of `M` claimed not to return
reaches no `return` from its entry once paths are cut at calls to claimed-noreturn functions
(`noRetOk`, on a reachable set it checks closed).  Its soundness (`summariesOk_sound`, by
fixpoint induction over the runner of `M`): the run of `M` never returns from such a function
(`NoRetHolds`).  `validatePass` checks the table against the pass input, whose semantics is the
oracle of every step of the pass, and `StepSound` takes `NoRetHolds` of that oracle.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Lean.Order

/-- The table claims that function `g` does not return: its first entry for `g` says so. -/
def noRet (O : Option (List Summary)) (g : String) : Bool :=
  ((O.getD []).find? (·.func == g)).any (·.noreturn)

/-- A statement that calls a function the table claims does not return. -/
def callsNoRet (O : Option (List Summary)) (s : Stmt) : Bool :=
  match s.inst with
  | .call g _ => noRet O g
  | _ => false

/-- The index of the block's first statement that calls a claimed-noreturn function. -/
def trimIdx (O : Option (List Summary)) (b : Block) : Option Nat := b.body.findIdx? (callsNoRet O)

/-- The block is cut by a call to a claimed-noreturn function. -/
def cut (O : Option (List Summary)) (b : Block) : Bool := (trimIdx O b).isSome

/-- Where a block goes once paths are cut at calls to claimed-noreturn functions. -/
def liveSuccs (O : Option (List Summary)) (b : Block) : List Nat :=
  if cut O b then [] else b.term.succs

/-- The blocks reachable from the entry along `liveSuccs`, by a worklist. -/
def liveSet (O : Option (List Summary)) (f : Func) : NatMap Unit :=
  match f.blocks.head? with
  | none => .empty
  | some e =>
    let n := f.blocks.length
    reachAux (.ofList (f.blocks.map fun b => (b.id, (liveSuccs O b).eraseDups)))
      (4 * n * (n + 1) + 4) [e.id] .empty

def _root_.Fe.Sonatina.Term.isRet : Term → Bool
  | .ret _ => true
  | _ => false

/-- `f` does not return: from its entry, cutting paths at calls to claimed-noreturn functions,
    no block reached ends in `return` (on `liveSet`, checked closed). -/
def noRetOk (O : Option (List Summary)) (f : Func) : Bool :=
  match f.blocks.head? with
  | none => true
  | some e =>
    let R := liveSet O f
    (R.find? e.id).isSome && f.blocks.all fun b => (R.find? b.id).isNone || cut O b ||
      (!b.term.isRet && b.term.succs.all fun s => (R.find? s).isSome)

/-- Every function of `M` the table claims does not return passes `noRetOk`. -/
def SummariesOk (O : Option (List Summary)) (M : Module) : Bool :=
  M.funcs.all fun f => !noRet O f.name || noRetOk O f

/-- The oracle never returns from a function the table claims does not return. -/
def NoRetHolds (O : Option (List Summary)) (o : Oracle) : Prop :=
  ∀ g args, noRet O g = true → Returns (fun _ => False) (o g args)

theorem cut_call {O : Option (List Summary)} {b : Block} (h : cut O b = true) :
    ∃ s ∈ b.body, callsNoRet O s = true := by
  unfold cut trimIdx at h
  rw [List.findIdx?_isSome, List.any_eq_true] at h
  exact h

/-- Statements with a call to a function the table claims does not return do not return, under
    an oracle of which the table holds. -/
theorem noRet_runBodyO {O : Option (List Summary)} {o : Oracle} (hnr : NoRetHolds O o) (c : Ctx) :
    ∀ (env : Env) (stmts : List Stmt), (∃ s ∈ stmts, callsNoRet O s = true) →
      Returns (fun _ => False) (runBodyO o c env stmts)
  | _, [], ⟨_, hm, _⟩ => nomatch hm
  | env, s :: rest, ⟨s', hs', hc'⟩ => by
    unfold runBodyO
    by_cases hc : callsNoRet O s = true
    · refine Returns.bind (P := fun _ => False) ?_ fun _ h => h.elim
      rcases s with ⟨dsts, inst⟩
      cases inst
      case call callee args => exact Returns.bind_any fun vs => hnr callee vs hc
      all_goals simp [callsNoRet] at hc
    · rcases List.mem_cons.mp hs' with rfl | hm
      · exact absurd hc' hc
      exact Returns.bind_any fun _ => Returns.bind_any fun env' =>
        noRet_runBodyO hnr c env' rest ⟨s', hm, hc'⟩

/-- A terminator whose targets are all in `R` and that is no `return`: its continuation does not
    return, given block runners that do not return from `R`. -/
theorem noRet_termCont {G : Env → Option Nat → Nat → FeM (List Val)} {R : Nat → Prop}
    (hG : ∀ env prev id, R id → Returns (fun _ => False) (G env prev id)) (id : Nat) (env : Env) :
    ∀ t : Term, t.isRet = false → (∀ s ∈ t.succs, R s) → Returns (fun _ => False) (match t with
      | .jump dest => G env (some id) dest
      | .br cond nz z => do
        let (_, v) ← evalInt env cond
        G env (some id) (if v != 0 then nz else z)
      | .brTable s default cases => do
        let (_, v) ← evalInt env s
        let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
        match (vals.find? (·.1 == v)).map (·.2) <|> default with
        | some dest => G env (some id) dest
        | none => stuck
      | .ret values => values.mapM (evalOperand env)
      | .evmReturn a l => do
        let e ← returnData (← evalWord env a) (← evalWord env l)
        nomatch e
      | .evmRevert a l => do
        let e ← revertData (← evalWord env a) (← evalWord env l)
        nomatch e
      | .evmStop => do
        let e ← stopCall
        nomatch e
      | .evmInvalid => do
        let e ← trap
        nomatch e
      | .evmSelfDestruct a => do
        let e ← Fe.EVM.selfdestruct (← evalWord env a)
        nomatch e
      | .unreachable => do
        let e ← trap
        nomatch e) := by
  intro t hr hs
  cases t with
  | jump d => exact hG _ _ _ (hs d (List.mem_singleton_self _))
  | br c nz z =>
    refine Returns.bind_any fun x => ?_
    rcases x with ⟨_, v⟩
    dsimp only
    split
    · exact hG _ _ _ (hs nz (by simp [Term.succs]))
    · exact hG _ _ _ (hs z (by simp [Term.succs]))
  | brTable s d cases =>
    refine Returns.bind_any fun x => ?_
    rcases x with ⟨_, v⟩
    dsimp only
    refine Returns.bind (Returns.mapM (P := fun p => p.2 ∈ cases.map (·.2)) fun cse hc => ?_)
      fun vals hvals => ?_
    · rcases cse with ⟨o, dest⟩
      exact Returns.bind_any fun _ => Returns.pure (List.mem_map_of_mem hc)
    · split
      · next dest hdest =>
        refine hG _ _ _ (hs dest ?_)
        simp only [Term.succs, List.mem_append]
        revert hdest
        cases hf : (vals.find? (·.1 == v)).map (·.2) with
        | none =>
          intro hdest
          have h' : d = some dest := hdest
          exact Or.inl (by simp [h'])
        | some x =>
          intro hdest
          have h' : x = dest := Option.some.inj hdest
          subst h'
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hf
          exact Or.inr (hvals p (List.mem_of_find?_eq_some hp))
      · exact Returns.stuck _
  | ret vs => simp [Term.isRet] at hr
  | evmReturn a l => dsimp only; returns_auto
  | evmRevert a l => dsimp only; returns_auto
  | evmStop => dsimp only; returns_auto
  | evmInvalid => dsimp only; returns_auto
  | evmSelfDestruct a => dsimp only; returns_auto
  | unreachable => dsimp only; returns_auto

/-- The table holds of the module it is checked against: its run never returns from a function
    claimed not to return.  By fixpoint induction over the module's mutual runner: a body with a
    call to such a function does not return, nor does a block of the checked set. -/
theorem summariesOk_sound {O : Option (List Summary)} {M : Module} (h : SummariesOk O M = true)
    (c : Ctx) : NoRetHolds O (runFunc M c) := by
  intro name args hn
  rw [← runFuncG_none]
  refine runFuncG.fixpoint_induct Guard.none M c
    (fun H => ∀ (env : Env) (stmts : List Stmt), (∃ s ∈ stmts, callsNoRet O s = true) →
      Returns (fun _ => False) (H [] [] env stmts))
    (fun F => ∀ (name : String) (args : List Val), noRet O name = true →
      Returns (fun _ => False) (F [] name args))
    (fun G => ∀ (f : Func) (env : Env) (prev : Option Nat) (id : Nat), noRetOk O f = true →
      ((liveSet O f).find? id).isSome = true → Returns (fun _ => False) (G [] f env prev id))
    ?a1 ?a2 ?a3 ?s1 ?s2 ?s3 name args hn
  case a1 =>
    exact admissible_apply (β := fun _ => List (List Nat) → Env → List Stmt → FeM Env)
      (fun _ H => ∀ (env : Env) (stmts : List Stmt), (∃ s ∈ stmts, callsNoRet O s = true) →
        Returns (fun _ => False) (H [] env stmts)) []
      (admissible_apply (β := fun _ => Env → List Stmt → FeM Env)
        (fun _ H => ∀ (env : Env) (stmts : List Stmt), (∃ s ∈ stmts, callsNoRet O s = true) →
          Returns (fun _ => False) (H env stmts)) []
        (Fe.M.admissible_arrow (fun (env : Env) (H : List Stmt → FeM Env) =>
            ∀ (stmts : List Stmt), (∃ s ∈ stmts, callsNoRet O s = true) →
              Returns (fun _ => False) (H stmts))
          fun env => Fe.M.admissible_arrow (fun (stmts : List Stmt) (x : FeM Env) =>
            (∃ s ∈ stmts, callsNoRet O s = true) → Returns (fun _ => False) x)
          fun stmts => admissible_imp _ (admissible_returns _)))
  case a2 =>
    exact admissible_apply (β := fun _ => String → List Val → FeM (List Val))
      (fun _ F => ∀ (name : String) (args : List Val), noRet O name = true →
        Returns (fun _ => False) (F name args)) []
      (Fe.M.admissible_arrow (fun (name : String) (F : List Val → FeM (List Val)) =>
          ∀ (args : List Val), noRet O name = true → Returns (fun _ => False) (F args))
        fun name => Fe.M.admissible_arrow (fun (args : List Val) (x : FeM (List Val)) =>
          noRet O name = true → Returns (fun _ => False) x)
          fun args => admissible_imp _ (admissible_returns _))
  case a3 =>
    exact admissible_apply (β := fun _ => Func → Env → Option Nat → Nat → FeM (List Val))
      (fun _ G => ∀ (f : Func) (env : Env) (prev : Option Nat) (id : Nat), noRetOk O f = true →
        ((liveSet O f).find? id).isSome = true → Returns (fun _ => False) (G f env prev id)) []
      (Fe.M.admissible_arrow (fun (f : Func) (G : Env → Option Nat → Nat → FeM (List Val)) =>
          ∀ (env : Env) (prev : Option Nat) (id : Nat), noRetOk O f = true →
            ((liveSet O f).find? id).isSome = true → Returns (fun _ => False) (G env prev id))
        fun f => Fe.M.admissible_arrow (fun (env : Env) (G : Option Nat → Nat → FeM (List Val)) =>
          ∀ (prev : Option Nat) (id : Nat), noRetOk O f = true →
            ((liveSet O f).find? id).isSome = true → Returns (fun _ => False) (G prev id))
        fun env => Fe.M.admissible_arrow (fun (prev : Option Nat) (G : Nat → FeM (List Val)) =>
          ∀ (id : Nat), noRetOk O f = true →
            ((liveSet O f).find? id).isSome = true → Returns (fun _ => False) (G id))
        fun prev => Fe.M.admissible_arrow (fun (id : Nat) (x : FeM (List Val)) =>
          noRetOk O f = true → ((liveSet O f).find? id).isSome = true →
            Returns (fun _ => False) x)
        fun id => admissible_imp _ (admissible_imp _ (admissible_returns _)))
  case s1 =>
    intro H F hH hF env stmts hs
    cases stmts with
    | nil => obtain ⟨_, hm, _⟩ := hs; cases hm
    | cons s rest =>
      simp only [List.nil_append, List.headD_nil, List.tail_nil, guarded]
      by_cases hc : callsNoRet O s = true
      · refine Returns.bind (P := fun _ => False) ?_ fun _ h => h.elim
        rcases s with ⟨dsts, inst⟩
        cases inst
        case call callee args =>
          exact Returns.bind_any fun vs => hF callee vs hc
        all_goals simp [callsNoRet] at hc
      · obtain ⟨s', hs', hc'⟩ := hs
        rcases List.mem_cons.mp hs' with rfl | hm
        · exact absurd hc' hc
        exact Returns.bind_any fun _ => Returns.bind_any fun env' => hH env' rest ⟨s', hm, hc'⟩
  case s2 =>
    intro G hG name args hn
    simp only [guarded]
    cases hf : M.func? name with
    | none => exact Returns.stuck _
    | some f =>
      dsimp only
      have hok : noRetOk O f = true := by
        have hfn : f.name = name := by simpa using List.find?_some hf
        have := List.all_eq_true.mp h f (List.mem_of_find?_eq_some hf)
        rw [hfn, hn] at this
        simpa using this
      cases he : f.blocks.head? with
      | none => exact Returns.stuck _
      | some e =>
        have hent : ((liveSet O f).find? e.id).isSome = true := by
          unfold noRetOk at hok
          rw [he] at hok
          simp only [Bool.and_eq_true] at hok
          exact hok.1
        exact Returns.bind_any fun env => hG f env none e.id hok hent
  case s3 =>
    intro H G hH hG f env prev id hok hid
    dsimp only
    cases hb : f.block? id with
    | none => exact Returns.stuck _
    | some b =>
      dsimp only
      simp only [Guard.at, Guard.none, List.lookup, Option.bind_none, Option.getD_none]
      have hmem := List.mem_of_find?_eq_some hb
      have hbid : b.id = id := by simpa using List.find?_some hb
      have hok' := hok
      unfold noRetOk at hok
      cases he : f.blocks.head? with
      | none => rw [List.head?_eq_none_iff] at he; rw [he] at hmem; cases hmem
      | some e =>
      rw [he] at hok
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
        Bool.not_eq_true'] at hok
      rcases hok.2 b hmem with (hr | hc) | ⟨hnr, hs⟩
      · rw [← hbid, hr] at hid; cases hid
      · exact Returns.bind_any fun env₁ =>
          Returns.bind (hH env₁ b.body (cut_call hc)) fun _ h => h.elim
      · refine Returns.bind_any fun env₁ => Returns.bind_any fun env₂ => ?_
        exact noRet_termCont (R := fun s => ((liveSet O f).find? s).isSome = true)
          (fun env prev id hr => hG f env prev id hok' hr)
          id env₂ b.term hnr fun s hs' => hs s hs'

end Fe.Sonatina.Steps
