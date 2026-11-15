import Fe.Sonatina.CheckEvent
import Fe.EVM.FrameCalls

/-!
# The bytes of one block

The block lemma of the checker's soundness proof.  `run_ends`: a path of block `b`'s bytes that
`Check.run` accepts, from an EVM state where the path is (`PathRel`: the pc, the symbolic stack's
words on top of the EVM stack under the valuation `ρ` of the IR's values, the exit going where
the block's exit `e0` goes) and whose world agrees with the IR's (`Agree`), ends as `Ends`
says for the world the block's events leave (`Trace`): out of gas or stack, failing where an
event fails (`Fails`), at the code of the successor `e0` goes to with that successor's
entry stack on top, or halting as `e0` halts.  The proof is by induction on `run`'s fuel, each
opcode stepped by its lemma of `CheckStep.lean` or `CheckEvent.lean`, the steps gathered with
`Steps`: `XstepN` through states whose instruction makes no message call or creation (`Calm`),
which gives `XiOk` of a checked frame as well as its result.

The code the EVM runs is the section's followed by any bytes (a constructor's arguments):
`decode_append` and `D_J_append` make the checker's decoding and jump destinations the EVM's.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

theorem get?_append {a c : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ c).get? i = a.get? i := by
  have h' : i < (a ++ c).size := by simp [ByteArray.size_append]; omega
  simp only [ByteArray.get?, h, h', dite_true, Option.some.injEq]
  exact ByteArray.get_append_left h

theorem extract'_append {a c : ByteArray} {b e : Nat} (h : e ≤ a.size) :
    (a ++ c).extract' b e = a.extract' b e := by
  unfold ByteArray.extract'
  split
  · exact Reasoning.Theory.extract_append_left a c b e h
  · congr 2
    rw [Reasoning.Theory.byteArray_toList_eq, Reasoning.Theory.byteArray_toList_eq,
      ByteArray.data_append, Array.toList_append]
    by_cases hb : b ≤ a.size
    · rw [List.drop_append_of_le_length (by simpa using hb),
        List.take_append_of_le_length (by simp; omega)]
    · rw [show e - b = 0 by omega, List.take_zero, List.take_zero]

/-- An instruction that lies in the code decodes the same with bytes after the code. -/
theorem decode_append {code tail : ByteArray} {pc : UInt256} {op : Operation}
    {a : Option (UInt256 × Nat)} (h : decode code pc = some (op, a))
    (hn : pc.toNat + 1 + (a.map (·.2)).getD 0 ≤ code.size) :
    decode (code ++ tail) pc = some (op, a) := by
  unfold decode at h ⊢
  rw [get?_append (by omega)]
  cases hi : code.get? pc.toNat >>= Ethereum.EVM.parseInstr with
  | none => simp [hi] at h
  | some instr =>
    simp only [hi, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    split
    · rfl
    · next hw =>
      rw [if_neg hw] at hn
      simp only [Option.map_some, Option.getD_some] at hn
      rw [extract'_append (by omega)]

theorem N_gt (i : Nat) (op : Operation) : i < N i op := by simp [N]; omega

theorem get?_none {c : ByteArray} {i : Nat} (h : ¬ i < c.size) :
    c.get? i >>= Ethereum.EVM.parseInstr = none := by
  simp [ByteArray.get?, h]

/-- The jump destinations found from `i` include those found before. -/
theorem mem_D_J_aux_of_mem {c : ByteArray} {x : UInt256} :
    ∀ (n i : Nat) (r : Array UInt256), c.size - i ≤ n → x ∈ r → x ∈ D_J_aux c i r
  | n, i, r, hn, hx => by
    rw [D_J_aux]
    split
    · exact hx
    · next op hop =>
      have hi : i < c.size := by
        by_contra hc
        rw [get?_none hc] at hop
        cases hop
      match n, hn with
      | 0, hn => omega
      | n + 1, hn =>
        refine mem_D_J_aux_of_mem n _ _ (by have := N_gt i op; omega) ?_
        split
        · exact Array.mem_push_of_mem _ hx
        · exact hx

/-- A `JUMPDEST` of the one pass from `i` is one `D_J_aux` finds from there. -/
theorem mem_instrs_D_J {c : ByteArray} {pc : Nat} {a : Option Nat} {n : Nat} :
    ∀ (f i : Nat) (bs : List UInt8) (r : Array UInt256), bs = c.data.toList.drop i →
      (pc, .JUMPDEST, a, n) ∈ instrs f bs i → UInt256.ofNat pc ∈ D_J_aux c i r
  | 0, _, _, _, _, h => by simp [instrs] at h
  | _ + 1, _, [], _, _, h => by simp [instrs] at h
  | f + 1, i, b :: bs, r, hbs, h => by
    have hrest : bs = c.data.toList.drop (i + 1) := by
      rw [← List.drop_drop, ← hbs, List.drop_one, List.tail_cons]
    have hget : c.get? i = some b := by rw [Check.get?_drop, ← hbs]; rfl
    unfold instrs at h
    rw [D_J_aux]
    cases hop : parseByte b with
    | none => simp only [hop] at h; cases h
    | some op =>
    simp only [hop] at h
    rw [parseByte_eq] at hop
    split
    · next hn => rw [hget] at hn; simp [hop] at hn
    · next op' hop' =>
      rw [hget] at hop'
      have hop'' : op' = op := by simpa [hop] using hop'.symm
      subst hop''
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        rw [if_pos rfl]
        exact mem_D_J_aux_of_mem c.size _ _ (by omega) (Array.mem_push_self ..)
      · exact mem_instrs_D_J f _ _ _ (by rw [hrest, List.drop_drop]; rfl) h

theorem jumpdests_D_J {code : ByteArray} {t : Nat} (h : (jumpdests code).contains t = true) :
    (D_J code 0).contains (UInt256.ofNat t) = true := by
  simp only [Array.contains_iff_mem]
  simp only [jumpdests, List.contains_iff_mem, List.mem_filterMap] at h
  obtain ⟨⟨pc, op, a, n⟩, hmem, he⟩ := h
  by_cases hj : op = .JUMPDEST
  · subst hj
    simp at he
    subst he
    exact mem_instrs_D_J _ 0 _ #[] (by simp) hmem
  · simp [hj] at he

/-- A jump destination of the code is one of the code followed by other bytes. -/
theorem mem_D_J_aux_append {code tail : ByteArray} {x : UInt256} :
    ∀ (n i : Nat) (r : Array UInt256), code.size - i ≤ n → x ∈ D_J_aux code i r →
      x ∈ D_J_aux (code ++ tail) i r
  | n, i, r, hn, hx => by
    by_cases hi : i < code.size
    · have hg := get?_append (c := tail) hi
      rw [D_J_aux] at hx ⊢
      split at hx
      · next hnone =>
        split
        · exact hx
        · next op hop => rw [hg, hnone] at hop; cases hop
      · next op hop =>
        split
        · next hnone => rw [hg, hop] at hnone; cases hnone
        · next op' hop' =>
          rw [hg, hop] at hop'
          cases hop'
          match n, hn with
          | 0, hn => omega
          | n + 1, hn => exact mem_D_J_aux_append n _ _ (by have := N_gt i op; omega) hx
    · rw [D_J_aux] at hx
      split at hx
      · exact mem_D_J_aux_of_mem _ i r le_rfl hx
      · next op hop => rw [get?_none hi] at hop; cases hop

theorem D_J_append {code tail : ByteArray} {x : UInt256} (h : (D_J code 0).contains x = true) :
    (D_J (code ++ tail) 0).contains x = true := by
  simp only [Array.contains_iff_mem] at h ⊢
  exact mem_D_J_aux_append _ 0 #[] le_rfl h

theorem mapM_some_iff {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ws : List β}, l.mapM f = some ws ↔ List.Forall₂ (fun a b => f a = some b) l ws
  | [], ws => by cases ws <;> simp
  | a :: l, ws => by
    have ih := @mapM_some_iff _ _ f l
    cases hfa : f a <;> cases hl : l.mapM f <;> cases ws <;>
      simp_all [List.mapM_cons, ← ih]

open Fe Fe.EVM

variable {K : Bool} {M : List Made}

/-- The symbolic stack `es` holds the top of the EVM stack `stk`, the words `B` below it. -/
def StackRel (I : ExecutionEnv) (ρ : Nat → UInt256) (es : List Expr) (B stk : List UInt256) :
    Prop :=
  ∃ ws, es.mapM (·.eval I ρ) = some ws ∧ stk = ws ++ B

/-- `XstepN` through states each calm or with `K` set, each step that goes on keeping the
    environment.  `K` is set for a section that makes message calls. -/
inductive Steps (K : Bool) (D : Array UInt256) :
    State → Except ExecutionException (State × Option (HaltCause × ByteArray)) → Nat → Prop
  | step {s : State} {r : Except ExecutionException (State × Option (HaltCause × ByteArray))}
      (hc : Calm s ∨ K = true) (h : Xstep D s = r)
      (henv : ∀ t, r = .ok (t, none) → t.executionEnv = s.executionEnv) : Steps K D s r 1
  | trans {s s' : State} {r : Except ExecutionException (State × Option (HaltCause × ByteArray))}
      {n : Nat} (hc : Calm s ∨ K = true) (h : Xstep D s = .ok (s', none))
      (henv : s'.executionEnv = s.executionEnv) (rest : Steps K D s' r n) :
      Steps K D s r (n + 1)

theorem Steps.xstepN {D : Array UInt256} {s : State}
    {r : Except ExecutionException (State × Option (HaltCause × ByteArray))} {n : Nat}
    (h : Steps K D s r n) : XstepN D s r n := by
  induction h with
  | step _ h _ => exact .step _ _ h
  | trans _ h _ _ ih => exact .trans _ _ _ _ h ih

/-- A last step, which does not go on. -/
theorem Steps.last {D : Array UInt256} {s : State}
    {r : Except ExecutionException (State × Option (HaltCause × ByteArray))} (hc : Calm s)
    (h : Xstep D s = r) (hr : ∀ t, r ≠ .ok (t, none)) : Steps K D s r 1 :=
  .step (.inl hc) h fun t ht => absurd ht (hr t)

/-- The bytes reach `s'` from `s` in `n` steps, none of them halting. -/
def Reach (K : Bool) (D : Array UInt256) (s s' : State) (n : Nat) : Prop :=
  (n = 0 ∧ s' = s) ∨ Steps K D s (.ok (s', none)) n

/-- The bytes halt from `s` as the IR's halting terminator does on the world `w`. -/
def HaltEnds (K : Bool) (M : List Made) (D : Array UInt256) (s : State) (w : World) :
    Operation → List UInt256 → Prop
  | .RETURN, [a, l] => ∃ n s', Steps K D s
      (.ok (s', some (.success, w.memory.readWithPadding a.toNat l.toNat))) n ∧
      s'.accountMap = w.accounts ∧ s'.substate.logSeries = w.logs ∧ w.calls = M
  | .REVERT, [a, l] => ∃ n s', Steps K D s
      (.ok (s', some (.revert, w.memory.readWithPadding a.toNat l.toNat))) n
  | .STOP, [] => ∃ n s', Steps K D s (.ok (s', some (.success, .empty))) n ∧
      s'.accountMap = w.accounts ∧ s'.substate.logSeries = w.logs ∧ w.calls = M
  | .INVALID, [] => ∃ n, Steps K D s (.error .InvalidInstruction) n
  | _, _ => False

/-- The world after a block's events, from `w`: each event's operation on its operands' words
    gives the word `ρ` gives its result, until one fails or is stuck (the model's `gas` on an
    empty feed). -/
inductive Trace (I : ExecutionEnv) (ρ : Nat → UInt256) :
    List Event → World → Option (Except (Fe.Exit World) World) → Prop
  | nil (w : World) : Trace I ρ [] w (some (.ok w))
  | ok {ev : Event} {evs : List Event} {w w' : World} {r : Option (Except (Fe.Exit World) World)}
      {args : List UInt256} (ha : ev.args.mapM (·.eval I ρ) = some args)
      (hr : (evRun ev.op args).exec I w = some (.ok (ev.result.map ρ, w')))
      (rest : Trace I ρ evs w' r) : Trace I ρ (ev :: evs) w r
  | fail {ev : Event} {evs : List Event} {w : World} {e : Fe.Exit World} {args : List UInt256}
      (ha : ev.args.mapM (·.eval I ρ) = some args)
      (hr : (evRun ev.op args).exec I w = some (.error e)) :
      Trace I ρ (ev :: evs) w (some (.error e))
  | stuck {ev : Event} {evs : List Event} {w : World} {args : List UInt256}
      (ha : ev.args.mapM (·.eval I ρ) = some args)
      (hr : (evRun ev.op args).exec I w = none) : Trace I ρ (ev :: evs) w none

/-- An exit that goes to a successor: a `goto`, a `br` or a `br_table`. -/
def Exit.IsJump : Exit → Prop
  | .goto _ | .br .. | .table .. => True
  | _ => False

/-- A path's exit `ex` is the block's `e0`, or one a conditional jump narrowed it to, which goes
    where `e0` goes. -/
def ExitRel (I : ExecutionEnv) (ρ : Nat → UInt256) (e0 ex : Exit) : Prop :=
  ex = e0 ∨ (ex.next I ρ = e0.next I ρ ∧ (∀ op args, e0 ≠ .halt op args ∧ ex ≠ .halt op args) ∧
    ex.IsJump ∧ e0.IsJump)

/-- How the bytes of block `b` end from `s`, the block's events ending as `r` says, the words
    `B` below the path's stack: out of gas or stack, failing where an event fails (`Fails`), at
    the code of the successor the exit `e0` goes to with its entry stack on top and the
    world agreeing, the words below it `B` if the function may return from there, halting as
    `e0` does, returning as `e0` does to the return address with exactly the values above `B`,
    or at the code of the next of the calls `cls` with its arguments on top, and, if the callee
    returns, the address of the code the run goes on at with its results on top, which `run`
    accepts.  The bytes reach the successor in no step only where the path's exit `ex` has
    selected it. -/
def Ends (K : Bool) (M : List Made) (code : ByteArray) (I : ExecutionEnv) (ρ : Nat → UInt256) (c : Ctx)
    (hints : List BlockHint) (place : Nat → Option Nat) (b : Nat) (B : List UInt256)
    (e0 ex : Exit) (cls : List CallSeg) (s : State) (r : Option (Except (Fe.Exit World) World)) :
    Prop :=
  (∃ n e, Steps K (D_J I.code 0) s (.error e) n ∧ (e = .OutOfGass ∨ e = .StackOverflow)) ∨
  (∃ f e n, r = some (.error f) ∧ Fails f e ∧ Steps K (D_J I.code 0) s (.error e) n) ∨
  ∃ w, r = some (.ok w) ∧
    ((∃ S n s' pc' exprs B', cls = [] ∧ (∀ op args, e0 ≠ .halt op args) ∧ e0.IsJump ∧
        (n = 0 → ex.selected = some S) ∧
        Reach K (D_J I.code 0) s s' n ∧
        (∀ d, e0.next I ρ = some d → d = S) ∧
        place S = some pc' ∧ s'.machineState.pc.toNat = pc' ∧ c.arrival hints b S = some exprs ∧
        StackRel I ρ exprs B' s'.machineState.stack ∧ (c.frame.exact S = true → B' = B) ∧
        s'.executionEnv = I ∧ Agree M s' w) ∨
     (∃ op args ws, cls = [] ∧ e0 = .halt op args ∧ args.mapM (·.eval I ρ) = some ws ∧
       HaltEnds K M (D_J I.code 0) s w op ws) ∨
     (∃ vals ws n s', cls = [] ∧ e0 = .ret vals ∧ vals.mapM (·.eval I ρ) = some ws ∧
       Steps K (D_J I.code 0) s (.ok (s', none)) n ∧ s'.machineState.pc = ρ c.frame.retId ∧
       s'.machineState.stack = ws ++ B ∧ s'.executionEnv = I ∧ Agree M s' w) ∨
     (∃ cs more ce n s' ws k restE restW ex' fuel', cls = cs :: more ∧
       c.frame.callee cs.callee = some ce ∧ ce.returns = true ∧
       Steps K (D_J I.code 0) s (.ok (s', none)) n ∧ s'.machineState.pc.toNat = ce.offset ∧
       cs.args.mapM (·.eval I ρ) = some ws ∧ restE.mapM (·.eval I ρ) = some restW ∧
       s'.machineState.stack = ws ++ UInt256.ofNat k :: restW ++ B ∧ validJump code k = true ∧
       run code c hints place b fuel' ⟨k, cs.dsts.map .atom ++ restE, cs.events, ex', more⟩ =
         true ∧ ex'.Valid I ρ ∧ ExitRel I ρ e0 ex' ∧ s'.executionEnv = I ∧ Agree M s' w) ∨
     (∃ cs ce n s' ws t, cls = [cs] ∧ c.frame.callee cs.callee = some ce ∧ ce.returns = false ∧
       Steps K (D_J I.code 0) s (.ok (s', none)) n ∧ s'.machineState.pc.toNat = ce.offset ∧
       cs.args.mapM (·.eval I ρ) = some ws ∧ s'.machineState.stack = ws ++ t ∧
       s'.executionEnv = I ∧ Agree M s' w))

/-- A step that does not halt adds to how the bytes end. -/
theorem Ends.cons {code : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint} {place : Nat → Option Nat} {b : Nat} {B : List UInt256}
    {e0 ex ex₁ : Exit} {cls : List CallSeg} {s s₁ : State}
    {r : Option (Except (Fe.Exit World) World)} (hc : Calm s ∨ K = true)
    (hstep : Xstep (D_J I.code 0) s = .ok (s₁, none)) (henv : s₁.executionEnv = s.executionEnv)
    (h : Ends K M code I ρ c hints place b B e0 ex₁ cls s₁ r) :
    Ends K M code I ρ c hints place b B e0 ex cls s r := by
  rcases h with ⟨n, e, hx, he⟩ | ⟨f, e, n, hr, hf, hx⟩ |
    ⟨w, hr, ⟨S, n, s', pc', exprs, B', hcl, hnh, hj, -, hreach, hrest⟩ | hhalt | hret | hcall |
      hcall⟩
  · exact .inl ⟨n + 1, e, .trans hc hstep henv hx, he⟩
  · exact .inr (.inl ⟨f, e, n + 1, hr, hf, .trans hc hstep henv hx⟩)
  · refine .inr (.inr ⟨w, hr, .inl ⟨S, n + 1, s', pc', exprs, B', hcl, hnh, hj,
      fun h => absurd h n.succ_ne_zero, .inr ?_, hrest⟩⟩)
    rcases hreach with ⟨rfl, rfl⟩ | hx
    · exact .step hc hstep fun t ht => by cases ht; exact henv
    · exact .trans hc hstep henv hx
  · obtain ⟨op, args, ws, hcl, he, hws, hh⟩ := hhalt
    refine .inr (.inr ⟨w, hr, .inr (.inl ⟨op, args, ws, hcl, he, hws, ?_⟩)⟩)
    match op, ws, hh with
    | .RETURN, [_, _], ⟨n, s', hx, h⟩ => exact ⟨n + 1, s', .trans hc hstep henv hx, h⟩
    | .REVERT, [_, _], ⟨n, s', hx⟩ => exact ⟨n + 1, s', .trans hc hstep henv hx⟩
    | .STOP, [], ⟨n, s', hx, h⟩ => exact ⟨n + 1, s', .trans hc hstep henv hx, h⟩
    | .INVALID, [], ⟨n, hx⟩ => exact ⟨n + 1, .trans hc hstep henv hx⟩
  · obtain ⟨vals, ws, n, s', h0, h1, h2, hx, h3⟩ := hret
    exact .inr (.inr ⟨w, hr, .inr (.inr (.inl ⟨vals, ws, n + 1, s', h0, h1, h2,
      .trans hc hstep henv hx, h3⟩))⟩)
  · obtain ⟨cs, more, ce, n, s', ws, k, restE, restW, ex', fuel', h1, h2, h3, hx, h4⟩ := hcall
    exact .inr (.inr ⟨w, hr, .inr (.inr (.inr (.inl ⟨cs, more, ce, n + 1, s', ws, k, restE,
      restW, ex', fuel', h1, h2, h3, .trans hc hstep henv hx, h4⟩)))⟩)
  · obtain ⟨cs, ce, n, s', ws, t, h1, h2, h3, hx, h4⟩ := hcall
    exact .inr (.inr ⟨w, hr, .inr (.inr (.inr (.inr ⟨cs, ce, n + 1, s', ws, t, h1, h2, h3,
      .trans hc hstep henv hx, h4⟩)))⟩)

/-- What the checker decodes at `pc` the bytes decode at the EVM's pc, whatever follows the
    code. -/
theorem opAt_decode {code tail : ByteArray} {pc next : Nat} {op : Operation} {arg : Option Nat}
    {s : State} (hsize : code.size < UInt256.size) (h : opAt code pc = some (op, arg, next))
    (hcode : s.executionEnv.code = code ++ tail)
    (hpc : s.machineState.pc.toNat = pc) :
    ∃ a, decode s.executionEnv.code s.machineState.pc = some (op, a) ∧
      arg = ((a.map (·.1.toNat)).orElse fun _ => if op == .PUSH0 then some 0 else none) ∧
      next = pc + 1 + (a.map (·.2)).getD 0 ∧ next ≤ code.size := by
  simp only [opAt, Option.filter_eq_some_iff] at h
  obtain ⟨h, hn⟩ := h
  have h := codeTree_find hsize h
  simp only [Hints.decodeAt, Option.map_eq_some_iff] at h
  obtain ⟨⟨op', a⟩, hd, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hs : UInt256.ofNat pc = s.machineState.pc := by
    rw [← hpc, Reasoning.Theory.u256_ofNat_toNat]
  rw [hs] at hd
  refine ⟨a, ?_, rfl, rfl, by simpa using hn⟩
  rw [hcode, decode_append hd (by rw [hpc]; simpa using hn)]

/-- One step that moves on adds to how the bytes end. -/
theorem Ends.moves {code : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint}
    {place : Nat → Option Nat} {b : Nat} {B : List UInt256}
    {cls : List CallSeg} {e0 ex : Exit} {s : State}
    {r : Option (Except (Fe.Exit World) World)}
    {pc : UInt256} {stk : List UInt256} (henv : s.executionEnv = I) (hc : Calm s)
    (hm : Moves s pc stk)
    (h : ∀ g, Xstep (D_J s.executionEnv.code 0) s = .ok ({ s with machineState :=
      { s.machineState with
        pc := pc, stack := stk, gasAvailable := g
        execLength := s.machineState.execLength + 1 } }, none) →
      ∃ ex₁, Ends K M code I ρ c hints place b B e0 ex₁ cls
      { s with machineState := { s.machineState with
      pc := pc, stack := stk, gasAvailable := g
      execLength := s.machineState.execLength + 1 } } r) :
    Ends K M code I ρ c hints place b B e0 ex cls s r := by
  subst henv
  rcases hm with hx | hx | ⟨g, hx⟩
  · exact .inl ⟨1, _, .last hc hx (by simp), .inl rfl⟩
  · exact .inl ⟨1, _, .last hc hx (by simp), .inr rfl⟩
  · obtain ⟨_, h⟩ := h g hx
    exact Ends.cons (.inl hc) hx rfl h

/-- An event's step adds to how the bytes end. -/
theorem Ends.event {code : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint}
    {place : Nat → Option Nat} {b : Nat} {B : List UInt256}
    {cls : List CallSeg} {e0 ex ex₁ : Exit} {s : State}
    {r : Option (Except (Fe.Exit World) World)} {ev : Event} {evs : List Event} {w : World}
    {args t : List UInt256}
    (henv : s.executionEnv = I) (hc : Calm s ∨ K = true) (hm : EvMoves s ev.op args t)
    (hw : Agree M s w)
    (hargs : ev.args.mapM (·.eval I ρ) = some args) (htr : Trace I ρ (ev :: evs) w r)
    (h : ∀ s' w', s'.machineState.pc = s.machineState.pc + ⟨1⟩ →
      s'.machineState.stack = (ev.result.map ρ).toList ++ t → s'.executionEnv = I → Agree M s' w' →
      Trace I ρ evs w' r → Ends K M code I ρ c hints place b B e0 ex₁ cls s' r) :
    Ends K M code I ρ c hints place b B e0 ex cls s r := by
  subst henv
  rcases hm M w hw with hx | hx | ⟨f, e, he, hx, hf⟩ | ⟨r', w', s', he, hx, hpc, hst, henv', hw'⟩
  · exact .inl ⟨1, _, .step hc hx fun t ht => by simp at ht, .inl rfl⟩
  · exact .inl ⟨1, _, .step hc hx fun t ht => by simp at ht, .inr rfl⟩
  · cases htr with
    | ok ha hr _ => rw [hargs] at ha; cases ha; rw [he] at hr; cases hr
    | fail ha hr =>
      rw [hargs] at ha; cases ha; rw [he] at hr; cases hr
      exact .inr (.inl ⟨f, e, 1, rfl, hf, .step hc hx fun t ht => by simp at ht⟩)
    | stuck ha hr => rw [hargs] at ha; cases ha; rw [he] at hr; cases hr
  · cases htr with
    | ok ha hr hrest =>
      rw [hargs] at ha; cases ha; rw [he] at hr; cases hr
      exact Ends.cons hc hx henv' (h s' w' hpc hst henv' hw' hrest)
    | fail ha hr => rw [hargs] at ha; cases ha; rw [he] at hr; cases hr
    | stuck ha hr => rw [hargs] at ha; cases ha; rw [he] at hr; cases hr

/-- A halting opcode ends the bytes as the IR's halting terminator does. -/
theorem Ends.halt {code : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint}
    {place : Nat → Option Nat} {b : Nat} {B : List UInt256}
    {cls : List CallSeg} {ex : Exit} {s : State} {w : World} {op : Operation}
    {args : List Expr} {ws t : List UInt256} (hcl : cls = []) (henv : s.executionEnv = I)
    (hc : Calm s)
    (hop : haltOps.contains op = true)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, none))
    (hs : s.machineState.stack = ws ++ t) (hk : ws.length = (δ op).getD 0)
    (hargs : args.mapM (·.eval I ρ) = some ws) (hw : Agree M s w) :
    Ends K M code I ρ c hints place b B (.halt op args) ex cls s (some (.ok w)) := by
  subst henv
  refine (?_ : _ ∨ HaltEnds K M _ s w op ws).elim .inl fun h => .inr (.inr ⟨w, rfl, .inr (.inl ⟨op,
    args, ws, hcl, rfl, hargs, h⟩)⟩)
  simp only [haltOps, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hop
  rcases hop with rfl | rfl | rfl | rfl <;>
    rcases ws with _ | ⟨a, _ | ⟨l, _ | ⟨_, _⟩⟩⟩ <;> simp [δ] at hk <;>
    simp only [List.cons_append, List.nil_append] at hs
  · have h := step_return s hdec
    simp only [hs] at h
    split_ifs at h with h1 h2
    · exact .inl ⟨1, _, .last hc h (by simp), .inl rfl⟩
    · exact .inl ⟨1, _, .last hc h (by simp), .inr rfl⟩
    · right; simp only [HaltEnds]; rw [← hw.memory]
      exact ⟨1, _, .last hc h (by simp), hw.accounts, hw.logs,
        hw.calls_of_stop hc fun _ h' => by rw [h] at h'; simp at h'⟩
  · have h := step_revert s hdec
    simp only [hs] at h
    split_ifs at h with h1 h2
    · exact .inl ⟨1, _, .last hc h (by simp), .inl rfl⟩
    · exact .inl ⟨1, _, .last hc h (by simp), .inr rfl⟩
    · right; simp only [HaltEnds]; rw [← hw.memory]
      exact ⟨1, _, .last hc h (by simp)⟩
  · have h := step_stop s hdec
    split_ifs at h with h1
    · exact .inl ⟨1, _, .last hc h (by simp), .inr rfl⟩
    · exact .inr ⟨1, _, .last hc h (by simp), hw.accounts, hw.logs,
        hw.calls_of_stop hc fun _ h' => by rw [h] at h'; simp at h'⟩
  · exact .inr ⟨1, .last hc (step_invalid s hdec) (by simp)⟩

theorem StackRel.cons {I : ExecutionEnv} {ρ : Nat → UInt256} {es : List Expr}
    {B stk : List UInt256} {e : Expr} {v : UInt256} (h : StackRel I ρ es B stk)
    (he : e.eval I ρ = some v) : StackRel I ρ (e :: es) B (v :: stk) := by
  obtain ⟨ws, hm, rfl⟩ := h
  exact ⟨v :: ws, by simp [List.mapM_cons, he, hm], rfl⟩

/-- The top `k` of a symbolic stack: their words on top of the EVM stack. -/
theorem StackRel.split {I : ExecutionEnv} {ρ : Nat → UInt256} {es : List Expr}
    {B stk : List UInt256} (h : StackRel I ρ es B stk) {k : Nat} (hk : k ≤ es.length) :
    ∃ ws t, (es.take k).mapM (·.eval I ρ) = some ws ∧ stk = ws ++ t ∧
      StackRel I ρ (es.drop k) B t ∧ ws.length = k := by
  obtain ⟨ws, hm, rfl⟩ := h
  have h2 := mapM_some_iff.mp hm
  have hl := h2.length_eq
  refine ⟨ws.take k, ws.drop k ++ B, mapM_some_iff.mpr (List.forall₂_take k h2), ?_,
    ⟨ws.drop k, mapM_some_iff.mpr (List.forall₂_drop k h2), rfl⟩, by simp; omega⟩
  rw [← List.append_assoc, List.take_append_drop]

theorem StackRel.get {I : ExecutionEnv} {ρ : Nat → UInt256} {es : List Expr}
    {B stk : List UInt256} (h : StackRel I ρ es B stk) {i : Nat} {e : Expr}
    (he : es[i]? = some e) : ∃ v, e.eval I ρ = some v ∧ stk[i]? = some v := by
  obtain ⟨ws, hm, rfl⟩ := h
  have h2 := mapM_some_iff.mp hm
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp he).1
  have hl := h2.length_eq
  refine ⟨ws[i]'(by omega), ?_, by rw [List.getElem?_append_left (by omega)]; simp⟩
  have := List.forall₂_iff_get.mp h2
  have := this.2 i hi (by omega)
  simp only [List.get_eq_getElem] at this
  rw [← (List.getElem?_eq_some_iff.mp he).2]
  exact this

theorem StackRel.set {I : ExecutionEnv} {ρ : Nat → UInt256} {es : List Expr}
    {B stk : List UInt256} (h : StackRel I ρ es B stk) {i : Nat} {e : Expr} {v : UInt256}
    (hi : i < es.length) (he : e.eval I ρ = some v) :
    StackRel I ρ (es.set i e) B (stk.set i v) := by
  obtain ⟨ws, hm, rfl⟩ := h
  have h2 := mapM_some_iff.mp hm
  have hl := h2.length_eq
  refine ⟨ws.set i v, mapM_some_iff.mpr ?_, by rw [List.set_append_left _ _ (by omega)]⟩
  rw [List.forall₂_iff_get] at h2 ⊢
  refine ⟨by simp [hl], fun j h1 h3 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_set]
  split_ifs with hj
  · exact he
  · simpa using h2.2 j (by simpa using h1) (by simpa using h3)

/-- A pure opcode has a value on as many words as it pops. -/
theorem opEval_total {ee : ExecutionEnv} {op : Operation} {ws : List UInt256}
    (hp : pureOps.contains op = true) (hk : δ op = some ws.length) :
    ∃ r, opEval ee op ws = some r := by
  simp only [pureOps, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [δ] at hk
    simp [opEval, evalOp, envOp]

theorem pc_add (x : UInt256) (k : Nat) (h : x.toNat + k < UInt256.size) :
    (x + UInt256.ofNat k).toNat = x.toNat + k := by
  obtain ⟨⟨x, hx⟩⟩ := x
  show ((⟨x, hx⟩ + Fin.ofNat UInt256.size k : Fin UInt256.size)).val = x + k
  rw [Fin.val_add]
  simp only [Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt (by simp [UInt256.toNat] at h; omega : k < UInt256.size)]
  exact Nat.mod_eq_of_lt (by simpa [UInt256.toNat] using h)

theorem pc_one (x : UInt256) (h : x.toNat + 1 < UInt256.size) :
    (x + ⟨1⟩).toNat = x.toNat + 1 := pc_add x 1 h

/-- The EVM state is where path `p` of a block's bytes is: the code, the pc, the symbolic stack
    on top of the words `B`, and the exit going where the block's exit `e0` goes. -/
structure PathRel (code tail : ByteArray) (I : ExecutionEnv) (ρ : Nat → UInt256)
    (B : List UInt256) (e0 : Exit) (p : Path) (s : State) : Prop where
  env : s.executionEnv = I
  code : I.code = code ++ tail
  pc : s.machineState.pc.toNat = p.pc
  stack : StackRel I ρ p.stack B s.machineState.stack
  valid : p.exit.Valid I ρ
  exit : ExitRel I ρ e0 p.exit

theorem arrives_rel {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx} {hints : List BlockHint}
    {b S : Nat} {es : List Expr} {B stk : List UInt256} (ha : arrives c hints b S es = true)
    (h : StackRel I ρ es B stk) :
    ∃ exprs B', c.arrival hints b S = some exprs ∧ StackRel I ρ exprs B' stk ∧
      (c.frame.exact S = true → B' = B) := by
  unfold arrives at ha
  split at ha
  · next exprs he =>
    split_ifs at ha with hx
    · simp only [beq_iff_eq] at ha
      subst ha
      exact ⟨es, B, he, h, fun _ => rfl⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
      obtain ⟨ws, t, hm, rfl, -, -⟩ := h.split ha.1
      exact ⟨exprs, t, he, ⟨ws, by rw [← ha.2]; exact hm, rfl⟩, fun h => absurd h hx⟩
  · cases ha

/-- Where the exit goes the block's exit goes. -/
theorem PathRel.next {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256}
    {B : List UInt256} {e0 : Exit}
    {p : Path} {s : State} (hp : PathRel code tail I ρ B e0 p s) :
    p.exit.next I ρ = e0.next I ρ := by
  rcases hp.exit with h | h
  · rw [h]
  · exact h.1

/-- An instruction with an immediate is a `PUSHn`, its immediate as wide as it says. -/
theorem decode_push {code : ByteArray} {pc : UInt256} {op : Operation} {x : UInt256} {wd : Nat}
    (h : decode code pc = some (op, some (x, wd))) :
    ∃ q, op = .Push q ∧ q ≠ .PUSH0 := by
  unfold decode at h
  cases hi : code.get? pc.toNat >>= Ethereum.EVM.parseInstr with
  | none => simp [hi] at h
  | some instr =>
    simp only [hi, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · cases h
    · next hw =>
      cases instr with
      | Push q => exact ⟨q, rfl, by rintro rfl; simp [argOnNBytesOfInstr] at hw⟩
      | _ => simp [argOnNBytesOfInstr] at hw

/-- An instruction without an immediate width decodes without one. -/
theorem decode_none {code : ByteArray} {pc : UInt256} {op : Operation}
    {a : Option (UInt256 × Nat)} (h : decode code pc = some (op, a))
    (hw : argOnNBytesOfInstr op = 0) : a = none := by
  unfold decode at h
  cases hi : code.get? pc.toNat >>= Ethereum.EVM.parseInstr with
  | none => simp [hi] at h
  | some instr =>
    simp only [hi, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp [hw] at h
    exact h.symm

theorem way_not_halt {e : Exit} {cond : Expr} {taken : Bool} {w : Way}
    (h : e.way cond taken = some w) (op : Operation) (args : List Expr) : e ≠ .halt op args := by
  rintro rfl; simp [Exit.way] at h

theorem way_exit_not_halt {e e' : Exit} {cond : Expr} {taken : Bool}
    (h : e.way cond taken = some (.exit e')) (op : Operation) (args : List Expr) :
    e' ≠ .halt op args := by
  rintro rfl
  unfold Exit.way at h
  split at h
  · split at h <;> (try split_ifs at h) <;> simp at h
  · split at h
    · split_ifs at h <;> simp at h
    · cases h
  · cases h

theorem ne_zero_toNat (a : UInt256) : (a != ⟨0⟩) = (a.toNat != 0) := by
  obtain ⟨⟨a, ha⟩⟩ := a
  by_cases h : a = 0
  · subst h; rfl
  · have : ((⟨⟨a, ha⟩⟩ : UInt256) != ⟨0⟩) = true := by
      simp only [bne_iff_ne, ne_eq, UInt256.mk.injEq]; exact fun h' => h (by simpa using h')
    rw [this]; simpa [UInt256.toNat] using h

/-- An exit that has selected a successor is no halt, nor is the block's. -/
theorem e0_not_halt {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256}
    {B : List UInt256} {e0 : Exit}
    {p : Path} {s : State} {S : Nat} (hp : PathRel code tail I ρ B e0 p s)
    (hS : p.exit.selected = some S) (op : Operation) (args : List Expr) : e0 ≠ .halt op args := by
  rcases hp.exit with h | h
  · rw [← h]; intro he; rw [he] at hS; simp [Exit.selected] at hS
  · exact (h.2.1 op args).1

/-- A path's exit that has selected a successor is a jump, and so is the block's. -/
theorem isJump_of_selected {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256}
    {B : List UInt256} {e0 : Exit} {p : Path} {s : State} {S : Nat}
    (hp : PathRel code tail I ρ B e0 p s) (hS : p.exit.selected = some S) : e0.IsJump := by
  rcases hp.exit with h | h
  · rw [← h]
    cases hx : p.exit <;> rw [hx] at hS <;> simp [Exit.selected] at hS <;> trivial
  · exact h.2.2.2

/-- A path's exit that reads a conditional jump is a jump, and so is the block's. -/
theorem isJump_of_way {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256}
    {B : List UInt256} {e0 : Exit} {p : Path} {s : State} {cond : Expr} {taken : Bool} {w : Way}
    (hp : PathRel code tail I ρ B e0 p s) (hw : p.exit.way cond taken = some w) :
    e0.IsJump := by
  rcases hp.exit with h | h
  · rw [← h]
    cases hx : p.exit <;> rw [hx] at hw <;> simp [Exit.way] at hw <;> trivial
  · exact h.2.2.2

/-- A conditional jump's narrowed exit is a jump's. -/
theorem way_exit_isJump {e e' : Exit} {cond : Expr} {taken : Bool}
    (h : e.way cond taken = some (.exit e')) : e'.IsJump := by
  unfold Exit.way at h
  split at h
  · split at h <;> (try split_ifs at h) <;> simp at h
  · split at h
    · split_ifs at h <;> simp at h
      cases h; trivial
    · cases h
  · cases h

/-- The block lemma: a path of block `b`'s bytes that `run` accepts ends from a state where it
    is as the block's exit `e0` and events say, the words below its stack `B`. -/
theorem run_ends {code tail : ByteArray} {I : ExecutionEnv} {ρ : Nat → UInt256} {c : Ctx}
    {hints : List BlockHint} {place : Nat → Option Nat} {b : Nat} {e0 : Exit}
    (hsize : code.size < UInt256.size)
    (hretj : c.frame.returns = true → (D_J I.code 0).contains (ρ c.frame.retId) = true) :
    ∀ fuel p s w r B, (∀ ev ∈ p.events, messageOps.contains ev.op = true → K = true) →
      run code c hints place b fuel p = true → PathRel code tail I ρ B e0 p s →
      Agree M s w → Trace I ρ p.events w r → Ends K M code I ρ c hints place b B e0 p.exit p.calls s r
  | 0, p, s, w, r, B, _, h, _, _, _ => by simp [run] at h
  | fuel + 1, p, s, w, r, B, hK, h, hp, hw, htr => by
    unfold run at h
    by_cases harr : (p.events.isEmpty && p.calls.isEmpty &&
        (p.exit.selected.bind place) == some p.pc) = true
    · rw [if_pos harr] at h
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at harr
      obtain ⟨⟨hev, hcl0⟩, hsel⟩ := harr
      split at h
      · next S hS =>
        rw [hev] at htr
        cases htr
        obtain ⟨exprs, B', hex, hrel, hB⟩ := arrives_rel h hp.stack
        have hpl : place S = some p.pc := by simpa [hS] using hsel
        exact .inr (.inr ⟨w, rfl, .inl ⟨S, 0, s, p.pc, exprs, B', hcl0, e0_not_halt hp hS,
          isJump_of_selected hp hS, fun _ => hS,
          .inl ⟨rfl, rfl⟩,
          fun d hd => selected_sound hS hp.valid (hp.next ▸ hd), hpl, hp.pc, hex, hrel, hB,
          hp.env, hw⟩⟩)
      · cases h
    rw [if_neg harr] at h
    split at h
    · cases h
    next op arg next hop =>
    obtain ⟨a, hdec, harg, hnext, hle⟩ := opAt_decode hsize hop (hp.env ▸ hp.code) hp.pc
    simp only at h
    have hw' : ∀ g pc' stk', supplyOf s = [] ∧ Calm s →
        Xstep (D_J s.executionEnv.code 0) s = .ok ({ s with machineState := { s.machineState with
          pc := pc', stack := stk', gasAvailable := g
          execLength := s.machineState.execLength + 1 } }, none) →
        Agree M { s with machineState := { s.machineState with
        pc := pc', stack := stk', gasAvailable := g
        execLength := s.machineState.execLength + 1 } } w := fun _ _ _ hq hx =>
      hw.quiet hx hq.1 hq.2 rfl rfl rfl rfl
    -- The opcode supplies no entry of the feed unless it is `GAS`.
    have hquiet : op ≠ .GAS → callOps.contains op = false → supplyOf s = [] ∧ Calm s :=
      fun hg hc => ⟨supplyOf_eq hdec hg hc, calm_of hdec hc⟩
    -- A step to `next` with the stack `es`, the events unchanged.
    have cont : ∀ (pc' : UInt256) (stk : List UInt256) (es : List Expr), Calm s → op ≠ .GAS →
        Moves s pc' stk → pc'.toNat = next → StackRel I ρ es B stk →
        run code c hints place b fuel { p with pc := next, stack := es } = true →
        Ends K M code I ρ c hints place b B e0 p.exit p.calls s r :=
      fun pc' stk es hc hg hm hn hst hrun =>
      Ends.moves hp.env hc hm fun g hx => ⟨_, run_ends hsize hretj fuel
        { p with pc := next, stack := es } _ w r B hK
        hrun ⟨hp.env, hp.code, hn, hst, hp.valid, hp.exit⟩ (hw' g _ _ (hquiet hg (by simpa [Calm, hdec] using hc)) hx) htr⟩
    have hone : next = p.pc + 1 → (s.machineState.pc + ⟨1⟩).toNat = next := fun hn => by
      rw [pc_one _ (by rw [hp.pc]; omega), hp.pc, hn]
    have hnone : arg = none → a = none ∧ op ≠ .PUSH0 := by
      intro ha
      rw [ha] at harg
      cases a with
      | some x => simp at harg
      | none =>
        refine ⟨rfl, fun hq => ?_⟩
        subst hq
        simp at harg
    by_cases h1 : (op == .JUMPDEST) = true
    · rw [if_pos h1] at h
      simp only [beq_iff_eq] at h1
      subst h1
      have ha := decode_none hdec rfl
      subst ha
      exact cont _ _ _ (calm_of hdec (by decide)) (by decide) (jumpdest_moves hdec)
        (hone (by simpa using hnext)) hp.stack h
    rw [if_neg h1] at h
    obtain ⟨v, rfl⟩ | rfl : (∃ v, arg = some v) ∨ arg = none := by cases arg <;> simp
    · simp only at h
      cases a with
      | some xw =>
        obtain ⟨x, wd⟩ := xw
        simp only [Option.map_some, Option.orElse_some, Option.some.injEq] at harg
        subst harg
        obtain ⟨q, rfl, hq⟩ := decode_push hdec
        refine cont _ _ _ (calm_of hdec (by simp [callOps])) (by simp) (push_moves hq hdec) ?_
          (hp.stack.cons (by simp [Expr.eval, Reasoning.Theory.u256_ofNat_toNat])) h
        simp only [Option.map_some, Option.getD_some] at hnext
        rw [Nat.succ_eq_add_one, pc_add _ _ (by rw [hp.pc]; omega), hp.pc, hnext]; omega
      | none =>
        simp only [Option.map_none, Option.orElse_none] at harg
        split_ifs at harg with hq
        · simp only [beq_iff_eq] at hq
          subst hq
          simp only [Option.some.injEq] at harg
          subst harg
          exact cont _ _ _ (calm_of hdec (by decide)) (by decide) (push0_moves hdec)
            (hone (by simpa using hnext))
            (hp.stack.cons rfl) h
    obtain ⟨rfl, hq⟩ := hnone rfl
    simp only at h
    rw [if_neg (by simpa using hq)] at h
    have hone' := hone (by simpa using hnext)
    by_cases h2 : (op == .POP) = true
    · rw [if_pos h2] at h
      simp only [beq_iff_eq] at h2
      subst h2
      split at h
      · next e rest hes =>
        obtain ⟨ws, t, -, hs, hrest, hl⟩ := hp.stack.split (k := 1) (by simp [hes])
        obtain ⟨v, rfl⟩ : ∃ v, ws = [v] := by
          match ws, hl with
          | [v], _ => exact ⟨v, rfl⟩
        rw [hes] at hrest
        exact cont _ _ _ (calm_of hdec (by decide)) (by decide) (pop_moves hdec hs) hone' hrest h
      · cases h
    rw [if_neg h2] at h
    obtain ⟨n, hn⟩ | hn : (∃ n, dupN op = some n) ∨ dupN op = none := by
      cases dupN op <;> simp
    · rw [hn] at h
      simp only at h
      split at h
      · next e he =>
        obtain ⟨d, rfl⟩ : ∃ d, op = .Dup d := by cases op <;> simp [dupN] at hn ⊢
        obtain ⟨v, hv, hsv⟩ := hp.stack.get he
        exact cont _ _ _ (calm_of hdec (by simp [callOps])) (by simp) (dup_moves hn hdec hsv) hone'
          (hp.stack.cons hv) h
      · cases h
    rw [hn] at h
    simp only at h
    obtain ⟨n, hn'⟩ | hn' : (∃ n, swapN op = some n) ∨ swapN op = none := by
      cases swapN op <;> simp
    · rw [hn'] at h
      simp only at h
      split at h
      · next x e hx he =>
        obtain ⟨q, rfl⟩ : ∃ q, op = .Exchange q := by cases op <;> simp [swapN] at hn' ⊢
        obtain ⟨vx, hvx, hsx⟩ := hp.stack.get hx
        obtain ⟨ve, hve, hse⟩ := hp.stack.get he
        have hl0 : 0 < p.stack.length := (List.getElem?_eq_some_iff.mp hx).1
        have hln : n < p.stack.length := (List.getElem?_eq_some_iff.mp he).1
        exact cont _ _ _ (calm_of hdec (by simp [callOps])) (by simp) (swap_moves hn' hdec hsx hse)
          hone'
          ((hp.stack.set hl0 hve).set (by simpa using hln) hvx) h
      · cases h
    rw [hn'] at h
    simp only at h
    by_cases h3 : pureOps.contains op = true
    · rw [if_pos h3] at h
      split at h
      · next k hk =>
        split at h
        · next e he =>
          split_ifs at h with hlt
          obtain ⟨ws, t, hm, hs, hrest, hl⟩ := hp.stack.split (k := k) (by omega)
          have hev := mkOp_eval (ee := I) (env := ρ) he
          rw [hm] at hev
          obtain ⟨v, hv⟩ := opEval_total (ee := I) h3 (by rw [hk, hl])
          have hpm := pure_moves h3 hdec hs (by rw [hp.env]; exact hv)
          exact cont _ _ _ (calm_of_mem hdec (by decide) h3)
            (by rintro rfl; exact absurd h3 (by decide)) hpm hone'
            (hrest.cons (by rw [hev]; simpa using hv)) h
        · cases h
      · cases h
    rw [if_neg h3] at h
    by_cases h4 : (readOps.contains op || writeOps.contains op) = true
    · rw [if_pos h4] at h
      split at h
      · next k ev events hk hevs =>
        split_ifs at h with hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨hop, hkl⟩, htake⟩ := hc
        obtain ⟨ws, t, hm, hs, hrest, hl⟩ := hp.stack.split hkl
        have hargs : ev.args.mapM (·.eval I ρ) = some ws := htake ▸ hm
        have hem := event_evMoves h4 hdec hs (by rw [hk, hl])
        rw [hevs] at htr
        -- A message call is calm only if the section makes none.
        have hcK : Calm s ∨ K = true := by
          by_cases hco : callOps.contains op = true
          · refine .inr (hK ev (by rw [hevs]; exact .head _) ?_)
            have hall := List.all_eq_true.mp (by decide : (readOps ++ writeOps).all
              (fun o => !callOps.contains o || messageOps.contains o) = true) op
              (by simpa [List.contains_append] using h4)
            rw [hop]
            simp only [hco, Bool.not_true, Bool.false_or] at hall
            exact hall
          · exact .inl (calm_of hdec (by simpa using hco))
        refine Ends.event (ex₁ := p.exit) hp.env hcK (hop ▸ hem) hw hargs htr
          fun s' w' hpc hst henv hw2 htr' => ?_
        have hpc' : s'.machineState.pc.toNat = next := by rw [hpc]; exact hone'
        split at h
        · next _ _ id hr _ =>
          rw [hr] at hst
          exact run_ends hsize hretj fuel ⟨next, .atom id :: p.stack.drop k, events, p.exit,
            p.calls⟩ _ w' r B (fun ev' h' => hK ev' (by rw [hevs]; exact .tail _ h')) h
            ⟨henv, hp.code, hpc', by
              simpa [hst] using hrest.cons (e := .atom id) (v := ρ id) rfl, hp.valid, hp.exit⟩
            hw2 htr'
        · next _ _ hr _ =>
          rw [hr] at hst
          exact run_ends hsize hretj fuel ⟨next, p.stack.drop k, events, p.exit, p.calls⟩ _ w'
            r B (fun ev' h' => hK ev' (by rw [hevs]; exact .tail _ h')) h ⟨henv, hp.code, hpc', by simpa [hst] using hrest, hp.valid, hp.exit⟩ hw2 htr'
        · cases h
      · cases h
    rw [if_neg h4] at h
    -- Arrival at a successor's code, the events done.
    have arrive : ∀ (s₁ : State) (S pc' : Nat) (es : List Expr), p.events = [] → p.calls = [] →
        s₁.executionEnv = I → Agree M s₁ w → s₁.machineState.pc.toNat = pc' → place S = some pc' →
        (∀ d, e0.next I ρ = some d → d = S) → StackRel I ρ es B s₁.machineState.stack →
        arrives c hints b S es = true → (∀ op args, e0 ≠ .halt op args) → e0.IsJump →
        Ends K M code I ρ c hints place b B e0 (.goto S) p.calls s₁ r := by
      intro s₁ S pc' es hev hcl0 henv hw₁ hpc hpl hnx hst ha hnh hj
      rw [hev] at htr
      cases htr
      obtain ⟨exprs, B', hex, hrel, hB⟩ := arrives_rel ha hst
      exact .inr (.inr ⟨w, rfl, .inl ⟨S, 0, s₁, pc', exprs, B', hcl0, hnh, hj, fun _ => rfl,
        .inl ⟨rfl, rfl⟩, hnx, hpl, hpc, hex, hrel, hB, henv, hw₁⟩⟩)
    -- The block's exit is no halt where a jump's condition reads it.
    have nohalt : ∀ {cond taken w}, p.exit.way cond taken = some w →
        ∀ op args, e0 ≠ .halt op args := fun hw op args => by
      rcases hp.exit with h' | h'
      · rw [← h']; exact way_not_halt hw op args
      · exact (h'.2.1 op args).1
    by_cases h5 : haltOps.contains op = true
    · rw [if_pos h5] at h
      split at h
      · next hop' args hex =>
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨hev, hcl0⟩, rfl⟩, hkl⟩, htake⟩ := h
        have he0 : e0 = .halt hop' args := by
          rcases hp.exit with h' | h'
          · rw [← h', hex]
          · exact absurd hex (h'.2.1 hop' args).2
        rw [hev] at htr
        cases htr
        obtain ⟨ws, t, hm, hs, -, hl⟩ := hp.stack.split hkl
        rw [he0]
        exact Ends.halt hcl0 hp.env (calm_of_mem hdec (by decide) h5) h5 hdec hs hl (htake ▸ hm)
          hw
      · cases h
    rw [if_neg h5] at h
    have hjump : ∀ {t : Nat}, validJump code t = true →
        (D_J s.executionEnv.code 0).contains (UInt256.ofNat t) = true ∧
          (UInt256.ofNat t).toNat = t := fun hj => by
      simp only [validJump, Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ⟨by rw [hp.env, hp.code]; exact D_J_append (jumpdests_D_J hj.2),
        by rw [toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩
    by_cases h6 : (op == .JUMP) = true
    · rw [if_pos h6] at h
      simp only [beq_iff_eq] at h6
      subst h6
      split at h
      · next t rest hes =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨hj, h⟩ := h
        obtain ⟨hjd, htn⟩ := hjump hj
        obtain ⟨ws, tl, hm, hs, hrest, -⟩ := hp.stack.split (k := 1) (by simp [hes])
        simp only [hes, List.take_succ_cons, List.take_zero, List.mapM_cons, List.mapM_nil,
          Expr.eval, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hm
        subst hm
        rw [hes, List.drop_succ_cons, List.drop_zero] at hrest
        have hmv := jump_moves hdec hs hjd
        split at h
        · -- The next call.
          next cs more hev hcl =>
          rw [hev] at htr
          cases htr
          split at h
          · next ce hce =>
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hoff, hlen⟩, htake⟩, h⟩ := h
            obtain ⟨wsA, t2, hmA, htl, hrest2, hlA⟩ := hrest.split hlen
            rw [htake] at hmA
            rcases hmv with hx | hx | ⟨g, hx⟩
            · exact .inl ⟨1, _, .last (calm_of hdec (by decide)) (hp.env ▸ hx) (by simp),
                .inl rfl⟩
            · exact .inl ⟨1, _, .last (calm_of hdec (by decide)) (hp.env ▸ hx) (by simp),
                .inr rfl⟩
            · have hst := Steps.step (K := K) (D := D_J s.executionEnv.code 0)
                (.inl (calm_of hdec (by decide))) hx (fun t ht => by cases ht; rfl)
              have hwj := hw' g _ _ (hquiet (by decide) (by decide)) hx
              rw [hp.env] at hst hwj
              split at h
              · next hret =>
                split at h
                · next k rest' hk =>
                  simp only [Bool.and_eq_true] at h
                  obtain ⟨hkj, hrun⟩ := h
                  rw [hk] at hrest2
                  obtain ⟨wsK, t3, hmK, ht2, hrest3, -⟩ := hrest2.split (k := 1) (by simp)
                  simp only [List.take_succ_cons, List.take_zero, List.mapM_cons, List.mapM_nil,
                    Expr.eval, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                    Option.some.injEq] at hmK
                  subst hmK
                  simp only [List.drop_succ_cons, List.drop_zero] at hrest3
                  obtain ⟨restW, hmR, rfl⟩ := hrest3
                  refine .inr (.inr ⟨w, rfl, .inr (.inr (.inr (.inl ⟨cs, more, ce, 1, _, wsA, k,
                    rest', restW, p.exit, fuel, hcl, hce, hret, hst, ?_, hmA, hmR, ?_,
                    hkj, hrun, hp.valid, hp.exit, rfl, hwj⟩)))⟩)
                  · show (UInt256.ofNat t).toNat = _
                    rw [htn, hoff]
                  · show [].append tl = _
                    simp [htl, ht2]
                · cases h
              · next hret =>
                simp only [Bool.and_eq_true, List.isEmpty_iff] at h
                obtain ⟨⟨rfl, -⟩, -⟩ := h
                obtain ⟨restW, -, rfl⟩ := hrest2
                exact .inr (.inr ⟨w, rfl, .inr (.inr (.inr (.inr ⟨cs, ce, 1, _, wsA, restW ++ B,
                  hcl, hce, by simpa using hret, hst,
                  by show (UInt256.ofNat t).toNat = _; rw [htn, hoff],
                  hmA, by show [].append tl = _; simp [htl],
                  rfl, hwj⟩)))⟩)
          · cases h
        · next hnc =>
          refine Ends.moves hp.env (calm_of hdec (by decide)) hmv fun g hx => ?_
          split_ifs at h with harr'
          · simp only [List.isEmpty_iff, beq_iff_eq] at harr'
            split at h
            · next S hS =>
              exact ⟨_, arrive _ S t rest harr'.1.1 harr'.1.2 hp.env
                (hw' g _ _ (hquiet (by decide) (by decide)) hx) htn
                (by simpa [hS] using harr'.2)
                (fun d hd => selected_sound hS hp.valid (hp.next ▸ hd)) hrest h
                (e0_not_halt hp hS) (isJump_of_selected hp hS)⟩
            · cases h
          · exact ⟨_, run_ends hsize hretj fuel { p with pc := t, stack := rest } _ w r B hK h
              ⟨hp.env, hp.code, htn, hrest, hp.valid, hp.exit⟩ (hw' g _ _ (hquiet (by decide) (by decide)) hx)
              htr⟩
      · -- A return.
        next r' rest hes =>
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨hev, hcl⟩, hrt⟩, rfl⟩, h⟩ := h
        split at h
        · next vals hex =>
          simp only [beq_iff_eq] at h
          subst h
          have he0 : e0 = .ret rest := by
            rcases hp.exit with h' | h'
            · rw [← h', hex]
            · rw [hex] at h'; exact h'.2.2.1.elim
          rw [hev] at htr
          cases htr
          obtain ⟨ws, tl, hm, hs, hrest, -⟩ := hp.stack.split (k := 1) (by simp [hes])
          simp only [hes, List.take_succ_cons, List.take_zero, List.mapM_cons, List.mapM_nil,
            Expr.eval, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hm
          subst hm
          rw [hes, List.drop_succ_cons, List.drop_zero] at hrest
          obtain ⟨wsV, hmV, rfl⟩ := hrest
          rcases jump_moves hdec hs (by rw [hp.env]; exact hretj hrt) with hx | hx | ⟨g, hx⟩
          · exact .inl ⟨1, _, .last (calm_of hdec (by decide)) (hp.env ▸ hx) (by simp), .inl rfl⟩
          · exact .inl ⟨1, _, .last (calm_of hdec (by decide)) (hp.env ▸ hx) (by simp),
              .inr rfl⟩
          · have hst := Steps.step (K := K) (D := D_J s.executionEnv.code 0)
              (.inl (calm_of hdec (by decide))) hx (fun t ht => by cases ht; rfl)
            have hwj := hw' g _ _ (hquiet (by decide) (by decide)) hx
            rw [hp.env] at hst hwj
            exact .inr (.inr ⟨w, rfl, .inr (.inr (.inl ⟨rest, wsV, 1, _, hcl, he0, hmV, hst, rfl,
              by show [].append (wsV ++ B) = _; simp, rfl,
              hwj⟩))⟩)
        · cases h
      · cases h
    rw [if_neg h6] at h
    by_cases h7 : (op == .JUMPI) = true
    · rw [if_pos h7] at h
      simp only [beq_iff_eq] at h7
      subst h7
      split at h
      · next t cond rest hes =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨hev, hcl0⟩, hj⟩, htk⟩, hnt⟩ := h
        simp only [List.isEmpty_iff] at hev
        obtain ⟨hjd, htn⟩ := hjump hj
        obtain ⟨ws, tl, hm, hs, hrest, -⟩ := hp.stack.split (k := 2) (by simp [hes])
        obtain ⟨cv, hcv, rfl⟩ : ∃ cv, cond.eval I ρ = some cv ∧ ws = [UInt256.ofNat t, cv] := by
          cases hc : cond.eval I ρ with
          | none => simp [hes, List.mapM_cons, Expr.eval, hc] at hm
          | some cv => exact ⟨cv, rfl, by simpa [hes, List.mapM_cons, Expr.eval, hc] using hm.symm⟩
        rw [hes, List.drop_succ_cons, List.drop_succ_cons, List.drop_zero] at hrest
        refine Ends.moves hp.env (calm_of hdec (by decide)) (jumpi_moves hdec hs fun _ => hjd)
          fun g hx => ?_
        have hw₁ := hw' g _ _ (hquiet (by decide) (by decide)) hx
        by_cases hc : (cv != ⟨0⟩) = true
        · simp only [hc, if_true] at hw₁ ⊢
          have ht : (cv.toNat != 0) = true := by rw [← ne_zero_toNat]; exact hc
          split at htk
          · next S hS =>
            simp only [Bool.and_eq_true, beq_iff_eq] at htk
            have hn := way_sound hS hcv ht hp.valid
            exact ⟨_, arrive _ S t rest hev (by simpa using hcl0) hp.env hw₁ htn htk.1
              (fun d hd => by rw [← hp.next, hn] at hd; cases hd; rfl) hrest htk.2 (nohalt hS)
              (isJump_of_way hp hS)⟩
          · next hS => exact (way_sound hS hcv ht hp.valid).elim
          · cases htk
        · simp only [hc, Bool.false_eq_true, if_false] at hw₁ ⊢
          have ht : (cv.toNat != 0) = false := by rw [← ne_zero_toNat]; simpa using hc
          split at hnt
          · next S hS =>
            have hn := way_sound hS hcv ht hp.valid
            exact ⟨_, run_ends hsize hretj fuel
              { p with pc := next, stack := rest, exit := .goto S } _ w r B hK hnt
              ⟨hp.env, hp.code, hone', hrest, trivial,
              .inr ⟨by rw [← hp.next, hn]; rfl, fun op args =>
                ⟨nohalt hS op args, by simp⟩, trivial, isJump_of_way hp hS⟩⟩ hw₁ htr⟩
          · next hS => exact (way_sound hS hcv ht hp.valid).elim
          · next e' hS =>
            have hn := way_sound hS hcv ht hp.valid
            exact ⟨_, run_ends hsize hretj fuel { p with pc := next, stack := rest, exit := e' } _
              w r B hK hnt ⟨hp.env, hp.code, hone', hrest, hn.2,
              .inr ⟨by rw [hn.1, hp.next], fun op args =>
                ⟨nohalt hS op args, way_exit_not_halt hS op args⟩, way_exit_isJump hS,
                isJump_of_way hp hS⟩⟩
              hw₁ htr⟩
          · cases hnt
      · cases h
    rw [if_neg h7] at h
    cases h

end Fe.Sonatina.Check
