import Fe.Sonatina.Steps.Defined
import Mathlib.Data.List.Forall2

/-!
# `edge_split` (design §4.11)

The output's blocks are the input's, each with the same id, phis and statements, plus new
blocks `n` that are exactly `{ jump t }`, each the target of one terminator slot, of an input
block `p`.  A terminator slot of the output targets the input's target, or a new block whose
`t` is it, from that block.  A phi's operand from a new block `n` is the input's operand from
`n`'s predecessor; from an input block, the input's own.  A `br` or a `br_table` with a
default may become a `jump` to the target all its slots go to (`termRel`, which `cfg_cleanup`
shares); the entry block keeps its id.

The input evaluates `c` (or `s` and the keys) where the output does not, so the check also
takes the input's dominator tree and checks it and strict SSA: by the definedness invariant
(`Defined.lean`) the input reads only words there, and is not stuck where the output goes on.

The simulation (`ESCtx.R`, with the invariant `BlockInv` of the input): the output at an input
block `b`, entered from `p'`, is the input at `b` entered from `p'` relabelled (a new block
stands for its predecessor); the output at a new block `n` from `p` is the input entering `t`
from `p`, which stutters while the output jumps.
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

/-- An optional target of the output against the input's, related by `P`. -/
def optRel (P : Nat → Nat → Bool) : Option Nat → Option Nat → Bool
  | some t', some t => P t' t
  | none, none => true
  | _, _ => false

/-- The output's terminator against the input's, slot by slot: the same kind and operands, each
    output target related by `P` to the input's in the same slot; a `br`, or a `br_table` with a
    default, may become a `jump` to a target every slot relates to. -/
def termRel (P : Nat → Nat → Bool) : Term → Term → Bool
  | .jump d', .jump d => P d' d
  | .jump d', .br _ nz z => P d' nz && P d' z
  | .jump d', .brTable _ d cs => d.any (P d') && cs.all (P d' ·.2)
  | .br c' nz' z', .br c nz z => decide (c' = c) && P nz' nz && P z' z
  | .brTable s' d' cs', .brTable s d cs =>
    decide (s' = s) && optRel P d' d && cs'.length == cs.length &&
      (cs'.zip cs).all fun (c', c) => decide (c'.1 = c.1) && P c'.2 c.2
  | .ret vs', .ret vs => decide (vs' = vs)
  | .evmReturn a' l', .evmReturn a l => decide (a' = a ∧ l' = l)
  | .evmRevert a' l', .evmRevert a l => decide (a' = a ∧ l' = l)
  | .evmStop, .evmStop | .evmInvalid, .evmInvalid | .unreachable, .unreachable => true
  | _, _ => false

/-- What the check reads of a pair of functions. -/
structure ESCtx where
  B : NatMap Block
  B' : NatMap Block
  /-- The output's terminator slots: block and target. -/
  slots : List (Nat × Nat)

def ESCtx.of (f f' : Func) : ESCtx :=
  ⟨.ofListBy (·.id) f.blocks, .ofListBy (·.id) f'.blocks,
    f'.blocks.flatMap fun b => b.term.succs.map (b.id, ·)⟩

namespace ESCtx

variable (X : ESCtx)

/-- An input block. -/
def orig (id : Nat) : Bool := (X.B.find? id).isSome

/-- The one block whose output slots target `n` (one or more of them). -/
def predOf (n : Nat) : Option Nat :=
  match ((X.slots.filter (·.2 == n)).map (·.1)).eraseDups with
  | [p] => some p
  | _ => none

/-- `n` is a new block that only jumps to the input block `t`. -/
def split (n t : Nat) : Bool :=
  !X.orig n && X.orig t && match X.B'.find? n with
    | some nb => nb.phis.isEmpty && nb.body.isEmpty && match nb.term with
      | .jump t' => t' == t
      | _ => false
    | none => false

/-- The input block an output block stands for as a predecessor. -/
def lab (p : Nat) : Option Nat := if X.orig p then some p else X.predOf p

/-- An output slot of block `b` targeting `t'` where the input's targets `t`. -/
def tgt (b t' t : Nat) : Bool := (t' == t && X.orig t) || (X.split t' t && X.predOf t' == some b)

/-- An output phi against the input's: same value and type, and each operand the input's from
    the block its predecessor stands for. -/
def phiOk (p' p : Phi) : Bool :=
  p'.dst == p.dst && decide (p'.ty = p.ty) && p'.incoming.all fun (o, q') =>
    match X.lab q' with
    | some q => decide ((p.incoming.find? (·.2 == q)).map (·.1) = some o)
    | none => false

def phisOk : List Phi → List Phi → Bool
  | [], [] => true
  | p' :: ps', p :: ps => X.phiOk p' p && phisOk ps' ps
  | _, _ => false

/-- An output block: an input block's, or a new one. -/
def blockOk (b' : Block) : Bool :=
  match X.B.find? b'.id with
  | some b => decide (b'.body = b.body) && X.phisOk b'.phis b.phis &&
    termRel (X.tgt b.id) b'.term b.term
  | none => (match b'.term with | .jump t => X.split b'.id t | _ => false) &&
    (X.predOf b'.id).any X.orig

end ESCtx

/-- The check of an edge split of `f` to `f'`, with the input's dominator tree checked and the
    input in strict SSA on it. -/
def checkEdgeSplit (f f' : Func) : Bool :=
  let X := ESCtx.of f f'
  let T := domTree f
  f'.name == f.name && decide (f'.params = f.params) &&
    (match f.blocks.head?, f'.blocks.head? with
      | some e, some e' => e.id == e'.id
      | _, _ => false) &&
    T.valid f && ssa f T && f'.blocks.all X.blockOk

/-! ## Soundness -/

namespace ESCtx

variable {X : ESCtx}

/-- The simulation relation. -/
def R (X : ESCtx) (s' s : BState) : Prop :=
  s'.1 = s.1 ∧
    ((X.orig s'.2.2 = true ∧ s.2.2 = s'.2.2 ∧ s'.2.1.bind X.lab = s.2.1) ∨
     (∃ p, X.split s'.2.2 s.2.2 = true ∧ X.predOf s'.2.2 = some p ∧ s'.2.1 = some p ∧
       s.2.1 = some p))

theorem R_of_tgt {b d' d : Nat} {env : Env} (hb : X.orig b = true) (h : X.tgt b d' d = true) :
    X.R (env, some b, d') (env, some b, d) := by
  unfold tgt at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨rfl, ?_⟩
  rcases h with ⟨rfl, ho⟩ | ⟨hs, hp⟩
  · exact Or.inl ⟨ho, rfl, by simp [lab, hb]⟩
  · exact Or.inr ⟨b, hs, hp, rfl, rfl⟩

end ESCtx

/-- How two terminators' results correspond: environments related by `E` and targets by `P`,
    or the same values. -/
def NextTgt (E : Env → Env → Prop) (P : Nat → Nat → Prop) : Next → Next → Prop
  | .goto env' d', .goto env d => E env' env ∧ P d' d
  | .done v', .done v => v' = v
  | _, _ => False

theorem Approx.mono {α : Type} {R S : α → α → Prop} {x' x : FeM α} (h : Approx R x' x)
    (hRS : ∀ a' a, R a' a → S a' a) : Approx S x' x := by
  intro I w' w hw
  have := h I w' w hw
  revert this
  rcases x'.exec I w' with _ | (_ | ⟨a', _⟩) <;> rcases x.exec I w with _ | (_ | ⟨a, _⟩) <;>
    simp only [ResRel] <;> first | exact id | exact fun h => ⟨hRS _ _ h.1, h.2⟩ | exact fun h => h

/-- `mapM` of related lists by related functions gives related lists. -/
theorem Approx.mapM_rel {α β : Type} {P : α → α → Prop} {Q : β → β → Prop}
    {f' f : α → FeM β} (hf : ∀ a' a, P a' a → Approx Q (f' a') (f a)) :
    ∀ {l' l : List α}, List.Forall₂ P l' l → Approx (List.Forall₂ Q) (l'.mapM f') (l.mapM f)
  | [], [], .nil => by simpa using Approx.pure List.Forall₂.nil
  | a' :: l', a :: l, .cons hp hl => by
    rw [List.mapM_cons, List.mapM_cons]
    exact Approx.bind (hf a' a hp) fun b' b hb =>
      Approx.bind (mapM_rel hf hl) fun bs' bs hbs => Approx.pure (.cons hb hbs)

/-- A find in lists whose keys agree finds related entries. -/
theorem find_rel {P : Nat → Nat → Prop} (v : Nat) :
    ∀ {l' l : List (Nat × Nat)}, List.Forall₂ (fun a' a => a'.1 = a.1 ∧ P a'.2 a.2) l' l →
      ((l'.find? (·.1 == v)).map (·.2) = none ∧ (l.find? (·.1 == v)).map (·.2) = none) ∨
      ∃ d' d, (l'.find? (·.1 == v)).map (·.2) = some d' ∧ (l.find? (·.1 == v)).map (·.2) = some d ∧
        P d' d
  | [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | a' :: l', a :: l, .cons ⟨hk, hp⟩ hl => by
    simp only [List.find?_cons, hk]
    split
    · exact Or.inr ⟨_, _, rfl, rfl, hp⟩
    · exact find_rel v hl

/-- A `list` related to another by `Forall₂` has each element of the second related to one of
    the first. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, h => nomatch h
  | a :: _, _ :: _, .cons hr hl, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨a, List.mem_cons_self .., hr⟩
    · obtain ⟨a', ha', hr'⟩ := forall₂_mem_right hl h
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

/-- A terminator `termRel P` accepts, run in an environment that binds less, approximates the
    input's, targets related by `P`, when the input's operands are integers. -/
theorem approx_runTerm (P : Nat → Nat → Bool) {env' env : Env} (hr : EnvSub env' env)
    (t' t : Term) (h : termRel P t' t = true) (hdef : ∀ op ∈ t.args, ∃ v, intVal env op = some v) :
    Approx (NextTgt (fun e' e => e' = env' ∧ e = env) fun d' d => P d' d = true)
      (runTerm env' t') (runTerm env t) := by
  cases t' <;> cases t <;> simp only [termRel, Bool.false_eq_true] at h
  case jump.jump d' d => exact Approx.pure ⟨⟨rfl, rfl⟩, h⟩
  case jump.br d' c nz z =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨v, hv⟩ := hdef c (List.mem_singleton_self _)
    refine Approx.pure_total ?_
    unfold runTerm
    refine Total.bind (P := fun _ => True) (by rw [evalInt_eq, hv]; exact Total.lift rfl trivial)
      fun x _ => ?_
    rcases x with ⟨_, n⟩
    refine Total.pure ⟨⟨rfl, rfl⟩, ?_⟩
    dsimp only
    split
    · exact h.1
    · exact h.2
  case jump.brTable d' s dflt cs =>
    cases dflt with
    | none => simp at h
    | some d =>
    simp only [Option.any, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨htgt, hall⟩ := h
    obtain ⟨vs, hvs⟩ := hdef s (List.mem_cons_self ..)
    refine Approx.pure_total ?_
    unfold runTerm
    refine Total.bind (P := fun _ => True) (by rw [evalInt_eq, hvs]; exact Total.lift rfl trivial)
      fun x _ => ?_
    rcases x with ⟨_, v⟩
    dsimp only
    refine Total.bind (P := fun vals => List.Forall₂ (fun c p => p.2 = c.2) cs vals)
      (Total.mapM fun cse hc => ?_) fun vals hvals => ?_
    · rcases cse with ⟨o, dest⟩
      obtain ⟨vo, hvo⟩ := hdef o (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      exact Total.bind (P := fun _ => True) (by rw [evalInt_eq, hvo]; exact Total.lift rfl trivial)
        fun y _ => Total.pure rfl
    · cases hf : (vals.find? (·.1 == v)).map (·.2) with
      | none => exact Total.pure ⟨⟨rfl, rfl⟩, htgt⟩
      | some x =>
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hf
        obtain ⟨c, hc, hpc⟩ := forall₂_mem_right hvals (List.mem_of_find?_eq_some hp)
        refine Total.pure ⟨⟨rfl, rfl⟩, ?_⟩
        rw [hpc]; exact hall c hc
  case br.br c' nz' z' c nz z =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := h
    unfold runTerm
    refine Approx.bind (Approx.evalInt hr c') fun ⟨_, v⟩ _ e => e ▸ ?_
    exact Approx.pure ⟨⟨rfl, rfl⟩, by split <;> assumption⟩
  case brTable.brTable s' d' cs' s d cs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨rfl, hd⟩, hlen⟩, hcs⟩ := h
    have hF : List.Forall₂ (fun (c' c : Operand × Nat) => c'.1 = c.1 ∧ P c'.2 c.2 = true)
        cs' cs := by
      rw [List.forall₂_iff_zip]
      exact ⟨hlen, fun hm => by
        have := hcs _ hm
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using this⟩
    unfold runTerm
    refine Approx.bind (Approx.evalInt hr s') fun ⟨_, v⟩ _ e => e ▸ ?_
    refine Approx.bind (R := List.Forall₂ fun (a' a : Nat × Nat) =>
        a'.1 = a.1 ∧ P a'.2 a.2 = true) (Approx.mapM_rel ?_ hF) fun vals' vals hv => ?_
    · rintro ⟨o', t'⟩ ⟨o, t⟩ ⟨ho, ht⟩
      simp only at ho ht
      subst ho
      exact Approx.bind (Approx.evalInt hr o') fun _ _ e => e ▸ Approx.pure ⟨rfl, ht⟩
    · rcases find_rel (P := fun d' d => P d' d = true) v hv with ⟨h₁, h₂⟩ | ⟨e', e, h₁, h₂, he⟩
      · rw [h₁, h₂]
        cases d' <;> cases d <;> simp only [optRel, Bool.false_eq_true] at hd
        · exact Approx.stuck _
        · exact Approx.pure ⟨⟨rfl, rfl⟩, hd⟩
      · rw [h₁, h₂]
        exact Approx.pure ⟨⟨rfl, rfl⟩, he⟩
  case ret.ret vs' vs =>
    simp only [decide_eq_true_eq] at h
    subst h
    unfold runTerm
    exact Approx.bind (Approx.mapM' (Approx.evalOperand hr) _) fun _ _ e => e ▸ Approx.pure rfl
  case evmReturn.evmReturn a' l' a l =>
    simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold runTerm
    exact Approx.bind (Approx.evalWord hr a') fun _ _ e => e ▸ Approx.bind (Approx.evalWord hr l')
      fun _ _ e => e ▸ Approx.bind (approx_returnData _ _) fun e _ _ => nomatch e
  case evmRevert.evmRevert a' l' a l =>
    simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold runTerm
    exact Approx.bind (Approx.evalWord hr a') fun _ _ e => e ▸ Approx.bind (Approx.evalWord hr l')
      fun _ _ e => e ▸ Approx.bind (approx_revertData _ _) fun e _ _ => nomatch e
  case evmStop.evmStop => unfold runTerm; exact Approx.bind approx_stopCall fun e _ _ => nomatch e
  case evmInvalid.evmInvalid => unfold runTerm; exact Approx.bind approx_trap fun e _ _ => nomatch e
  case unreachable.unreachable => unfold runTerm; exact Approx.stuck _

theorem ESCtx.find_B (f f' : Func) (id : Nat) : (ESCtx.of f f').B.find? id = f.block? id := by
  simp only [ESCtx.of, NatMap.find?_ofListBy, Func.block?]

theorem ESCtx.find_B' (f f' : Func) (id : Nat) : (ESCtx.of f f').B'.find? id = f'.block? id := by
  simp only [ESCtx.of, NatMap.find?_ofListBy, Func.block?]

theorem ESCtx.phisOk_forall₂ {X : ESCtx} :
    ∀ {ps' ps : List Phi}, X.phisOk ps' ps = true → List.Forall₂ (fun p' p => X.phiOk p' p = true) ps' ps
  | [], [], _ => .nil
  | p' :: ps', p :: ps, h => by
    simp only [ESCtx.phisOk, Bool.and_eq_true] at h
    exact .cons h.1 (phisOk_forall₂ h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [ESCtx.phisOk] at h

theorem ESCtx.phisOk_dsts {X : ESCtx} :
    ∀ {ps' ps : List Phi}, X.phisOk ps' ps = true →
      ps'.map (fun phi => (phi.dst, phi.ty)) = ps.map (fun phi => (phi.dst, phi.ty))
  | [], [], _ => rfl
  | p' :: ps', p :: ps, h => by
    simp only [ESCtx.phisOk, ESCtx.phiOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [List.map_cons, h.1.1.1, h.1.1.2, phisOk_dsts h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ESCtx.phisOk] at h

/-- Entering a block whose phis the check accepts approximates entering the input's from the
    block its predecessor stands for. -/
theorem approx_enter {X : ESCtx} {b' b : Block} (h : X.phisOk b'.phis b.phis = true) (env : Env)
    (prev' : Option Nat) : Approx Eq (enter env prev' b') (enter env (prev'.bind X.lab) b) := by
  unfold enter
  rw [ESCtx.phisOk_dsts h]
  refine Approx.bind (R := List.Forall₂ Eq) (Approx.mapM_rel ?_ (ESCtx.phisOk_forall₂ h))
    fun vals' vals hv => ?_
  · intro p' p hp
    simp only [ESCtx.phiOk, Bool.and_eq_true, List.all_eq_true] at hp
    obtain ⟨_, hinc⟩ := hp
    cases prev' with
    | none => exact Approx.stuck _
    | some q' =>
      dsimp only [Option.bind]
      rcases hf : p'.incoming.find? (·.2 == q') with _ | ⟨o, q''⟩
      · rw [hf]; exact Approx.stuck _
      rw [hf]
      have hq : q'' = q' := by simpa using List.find?_some hf
      subst hq
      have hl := hinc _ (List.mem_of_find?_eq_some hf)
      simp only at hl
      rcases hlab : X.lab q'' with _ | q
      · rw [hlab] at hl; cases hl
      rw [hlab] at hl
      dsimp only
      simp only [decide_eq_true_eq] at hl
      rcases hg : p.incoming.find? (·.2 == q) with _ | ⟨o', q₂⟩
      · rw [hg] at hl; cases hl
      rw [hg] at hl
      rw [hg]
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      exact Approx.evalOperand (EnvSub.refl env) _
  · rw [List.forall₂_eq_eq_eq] at hv
    subst hv
    exact Approx.bindVals _ _ _

/-- An edge split is sound: the output function, its calls run by an oracle that approximates
    itself and returns integers on integers, approximates the well-formed input function on
    integers. -/
theorem edgeSplit_sound {sig : Sigs} {syms : List String} {o : Oracle} (ho : Oracle.Mono o)
    (hoi : o.IntRet) (c : Ctx) {f f' : Func} (hwf : f.wf sig syms = true)
    (h : checkEdgeSplit f f' = true) : FuncRef o c (some f') (some f) := by
  let X := ESCtx.of f f'
  let T := domTree f
  have hm := Func.wf_machine hwf
  simp only [checkEdgeSplit, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, hparams⟩, hentry⟩, hv⟩, hs⟩, hblocks⟩ := h
  -- The simulation, with the invariant of the input's state.
  let R : BState → BState → Prop := fun s' s => X.R s' s ∧ BlockInv f T s
  -- One output block of an input block steps with the input's.
  have lock : ∀ env prev' b, X.orig b = true → BlockInv f T (env, prev'.bind X.lab, b) →
      Approx (NextRel R b b) (stepBlock o c f' env prev' b)
        (stepBlock o c f env (prev'.bind X.lab) b) := by
    intro env prev' b horig hinv
    refine Approx.mono (Approx.strengthen (S := NextRel X.R b b) ?_
      (stepBlock_inv hwf hv hoi c hinv)) fun n' n ⟨hn, hni⟩ => ?_
    · unfold stepBlock
      cases h' : f'.block? b with
      | none => exact Approx.stuck _
      | some b' =>
        have hb'id : b'.id = b := by simpa using List.find?_some h'
        have hok := hblocks b' (List.mem_of_find?_eq_some h')
        obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.mp horig
        have hbb' : f.block? b = some bb := by rw [← ESCtx.find_B]; exact hbb
        have hbbid : bb.id = b := by simpa using List.find?_some hbb'
        simp only [ESCtx.blockOk, hb'id] at hok
        rw [show (ESCtx.of f f').B.find? b = some bb from hbb] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨hbody, hphis⟩, hterm⟩ := hok
        rw [hbb']
        dsimp only
        refine Approx.bind (Approx.strengthen (approx_enter hphis env prev')
          (point_zero hwf hv hinv hbb')) fun env₁ env₁' ⟨e, h₀⟩ => ?_
        cases e
        rw [hbody]
        have htake := point_take hwf hoi c hbb' h₀ bb.body.length le_rfl
        rw [List.take_length] at htake
        refine Approx.bind (Approx.strengthen (Approx.runBodyO ho hoi rfl env₁ bb.body h₀.1.int
          (Func.machine_block hm hbb').2.1) htake) fun env₂ env₂' ⟨e, hpi⟩ => ?_
        cases e
        rw [hbbid] at hterm
        have hdef : ∀ op ∈ bb.term.args, ∃ v, intVal env₂ op = some v := fun op hop => by
          obtain ⟨n, hn⟩ := term_defined hwf hs hbb' hinv.2.2.1 hpi op hop
          exact ⟨_, hn⟩
        refine Approx.mono (approx_runTerm _ (EnvSub.refl env₂) _ _ hterm hdef) fun n' n hn => ?_
        cases n' <;> cases n <;> simp only [NextTgt, NextRel] at hn ⊢
        · obtain ⟨⟨rfl, rfl⟩, ht⟩ := hn
          exact ESCtx.R_of_tgt horig ht
        · exact hn
    · cases n' <;> cases n <;> simp only [NextRel, NextInv] at hn hni ⊢
      · exact ⟨hn, hni⟩
      · exact hn
  have sim : Sim o c f' f R := by
    refine Sim.of_steps fun s' s hR => ?_
    rcases s' with ⟨env, prev', b'⟩
    rcases s with ⟨env₀, prev, b⟩
    obtain ⟨⟨he, hR⟩, hinv⟩ := hR
    simp only at he hR
    subst he
    rcases hR with ⟨horig, rfl, hprev⟩ | ⟨p, hsplit, hpred, rfl, rfl⟩
    · left; subst hprev; exact lock env prev' _ horig hinv
    · right
      refine ⟨b, ?_, ?_⟩
      · simp only [ESCtx.split, Bool.and_eq_true, Bool.not_eq_true'] at hsplit
        obtain ⟨⟨_, _⟩, hnb⟩ := hsplit
        rcases hfind : X.B'.find? b' with _ | nb
        · rw [hfind] at hnb; cases hnb
        rw [hfind] at hnb
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hnb
        obtain ⟨⟨hph, hbo⟩, htm⟩ := hnb
        have hnb' : f'.block? b' = some nb := by rw [← ESCtx.find_B']; exact hfind
        intro I w
        rcases hterm : nb.term with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rw [hterm] at htm <;>
          simp only [beq_iff_eq, Bool.false_eq_true] at htm
        subst htm
        simp [stepBlock, hnb', Fe.Sonatina.enter, hph, hbo, hterm, Fe.Sonatina.bind, runBodyO,
          runTerm]
      · simp only [ESCtx.split, Bool.and_eq_true, Bool.not_eq_true'] at hsplit
        refine ⟨⟨rfl, Or.inl ⟨hsplit.1.2, rfl, ?_⟩⟩, hinv⟩
        simp [ESCtx.lab, hsplit.1.1, hpred]
  intro args hargs
  unfold runFuncO
  dsimp only
  cases he : f.blocks.head? with
  | none => rw [he] at hentry; simp at hentry
  | some e =>
  cases he' : f'.blocks.head? with
  | none => rw [he, he'] at hentry; simp at hentry
  | some e' =>
  rw [he, he'] at hentry
  simp only [beq_iff_eq] at hentry
  dsimp only
  rw [hparams]
  refine Approx.bind (Approx.strengthen (Approx.bindVals _ _ _) (entry_inv hwf hv he hargs))
    fun env env₀ ⟨e₁, hi⟩ => ?_
  cases e₁
  have horig : X.orig e.id = true := by
    have : (f.block? e.id).isSome = true := by
      unfold Func.block?
      exact List.find?_isSome.mpr ⟨e, List.mem_of_mem_head? he, by simp⟩
    show ((ESCtx.of f f').B.find? e.id).isSome = true
    rw [ESCtx.find_B]; exact this
  exact Sim.approx sim (env, none, e'.id) (env, none, e.id)
    ⟨⟨rfl, Or.inl ⟨hentry ▸ horig, hentry, rfl⟩⟩, hi⟩

end Fe.Sonatina.Steps
