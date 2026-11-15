import Fe.Sonatina.CheckSound
import Ethereum.Theory.OpcodeLemmas

/-!
# One step of the bytes

The per-opcode lemmas of the checker's soundness proof: for each opcode `Check.run` moves the
abstract stack over, one `Xstep` of the bytes runs out of gas or of stack, or moves on to the
next pc and the stack the opcode leaves, the frame otherwise unchanged but for its gas
(`Moves`).  They come from EVMLean's `step_*` lemmas and hold of any code: `pure_moves`
covers every opcode of `pureOps` at once, by its value `opEval`; `dup_moves` and
`swap_moves` every `DUPn` and `SWAPn`.  The opcodes that read or write state and the halts
are EVMLean's `step_*` lemmas themselves.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

/-- One step of the bytes from `s` runs out of gas or stack, or moves to `pc` with `stack`,
    the frame otherwise as it was but for the gas. -/
def Moves (s : State) (pc : UInt256) (stack : List UInt256) : Prop :=
  Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    Xstep (D_J s.executionEnv.code 0) s = .error .StackOverflow ∨
    ∃ g, Xstep (D_J s.executionEnv.code 0) s = .ok ({ s with machineState :=
      { s.machineState with
        pc := pc, stack := stack, gasAvailable := g
        execLength := s.machineState.execLength + 1 } }, none)

theorem moves_of {s : State} {pc : UInt256} {stack : List UInt256} {c : Nat} {ovf : Prop}
    [Decidable ovf]
    (h : Xstep (D_J s.executionEnv.code 0) s =
      if s.machineState.gasAvailable.toNat < c then .error .OutOfGass
      else if ovf then .error .StackOverflow
      else .ok ({ s with machineState := { s.machineState with
        pc := pc, stack := stack, gasAvailable := s.machineState.gasAvailable.subNat c
        execLength := s.machineState.execLength + 1 } }, none)) :
    Moves s pc stack := by
  unfold Moves
  rw [h]
  split_ifs
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨_, rfl⟩)

set_option hygiene false in
/-- `Moves` from the step lemma `l` of EVMLean, the stack `s` steps on given by `hs`. -/
local macro "moves_from " l:ident : tactic => `(tactic| (
    have h := $l s hdec
    simp only [hs, List.cons_append, List.nil_append] at h
    exact moves_of h))

/-- A pure opcode moves on with its value on the stack, in place of its operands. -/
theorem pure_moves {s : State} {op : Operation} {args t : List UInt256} {r : UInt256}
    (hp : pureOps.contains op = true)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, none))
    (hs : s.machineState.stack = args ++ t) (hr : opEval s.executionEnv op args = some r) :
    Moves s (s.machineState.pc + ⟨1⟩) (r :: t) := by
  simp only [pureOps, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hp
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [opEval, evalOp, envOp] at hr <;>
  subst hr <;>
  simp only [List.cons_append, List.nil_append] at hs <;>
  first
    | moves_from step_add
    | moves_from step_sub
    | moves_from step_mul
    | moves_from step_div
    | moves_from step_sdiv
    | moves_from step_mod
    | moves_from step_smod
    | moves_from step_addmod
    | moves_from step_mulmod
    | moves_from step_exp
    | moves_from step_signextend
    | moves_from step_lt
    | moves_from step_gt
    | moves_from step_slt
    | moves_from step_sgt
    | moves_from step_eq
    | moves_from step_iszero
    | moves_from step_and
    | moves_from step_or
    | moves_from step_xor
    | moves_from step_not
    | moves_from step_byte
    | moves_from step_shl
    | moves_from step_shr
    | moves_from step_sar
    | moves_from step_address
    | moves_from step_origin
    | moves_from step_caller
    | moves_from step_callvalue
    | moves_from step_calldataload
    | moves_from step_calldatasize
    | moves_from step_codesize
    | moves_from step_chainid
    | moves_from step_timestamp
    | moves_from step_number
    | moves_from step_gaslimit
    | moves_from step_basefee
    | moves_from step_coinbase
    | moves_from step_prevrandao
    | (have h := step_blockhash s hdec
       simp only [hs, List.cons_append, List.nil_append, Bool.or_eq_true, decide_eq_true_eq,
         Array.getD_eq_getD_getElem?, Array.getElem?_map] at h
       exact moves_of h)

theorem split_stack {l : List UInt256} {n : Nat} (h : n ≤ l.length) :
    ∃ pre t, l = pre ++ t ∧ pre.length = n :=
  ⟨_, _, (List.take_append_drop n l).symm, List.length_take_of_le h⟩

/-- `DUPn` moves on with the `n`-th word copied on top. -/
theorem dup_moves {s : State} {d : Operation.DOp} {n : Nat} {a : UInt256}
    (hn : dupN (.Dup d) = some n)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Dup d, none))
    (ha : s.machineState.stack[n - 1]? = some a) :
    Moves s (s.machineState.pc + ⟨1⟩) (a :: s.machineState.stack) := by
  have h1 : 1 ≤ n := by cases d <;> simp [dupN, serializeInstr, serializeDupInstr] at hn <;> omega
  have hle := (List.getElem?_eq_some_iff.mp ha).1
  obtain ⟨pre, t, hs, hlen⟩ := split_stack (l := s.machineState.stack) (n := n) (by omega)
  cases d <;> simp [dupN, serializeInstr, serializeDupInstr] at hn <;> subst hn
  all_goals
    repeat
      obtain ⟨_, pre, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      simp at hlen
    try rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp only [hs, List.cons_append, List.nil_append] at ha ⊢
    simp at ha
    subst ha
    first
    | moves_from step_dup1
    | moves_from step_dup2
    | moves_from step_dup3
    | moves_from step_dup4
    | moves_from step_dup5
    | moves_from step_dup6
    | moves_from step_dup7
    | moves_from step_dup8
    | moves_from step_dup9
    | moves_from step_dup10
    | moves_from step_dup11
    | moves_from step_dup12
    | moves_from step_dup13
    | moves_from step_dup14
    | moves_from step_dup15
    | moves_from step_dup16

/-- `SWAPn` moves on with the top word and the `n + 1`-th swapped. -/
theorem swap_moves {s : State} {x : Operation.ExOp} {n : Nat} {a e : UInt256}
    (hn : swapN (.Exchange x) = some n)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Exchange x, none))
    (ha : s.machineState.stack[0]? = some a) (he : s.machineState.stack[n]? = some e) :
    Moves s (s.machineState.pc + ⟨1⟩) ((s.machineState.stack.set 0 e).set n a) := by
  have hle := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨pre, t, hs, hlen⟩ := split_stack (l := s.machineState.stack) (n := n + 1) (by omega)
  cases x <;> simp [swapN, serializeInstr, serializeSwapInstr] at hn <;> subst hn
  all_goals
    repeat
      obtain ⟨_, pre, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      simp at hlen
    try rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp only [hs, List.cons_append, List.nil_append] at ha he ⊢
    simp at ha he
    subst ha he
    first
    | moves_from step_swap1
    | moves_from step_swap2
    | moves_from step_swap3
    | moves_from step_swap4
    | moves_from step_swap5
    | moves_from step_swap6
    | moves_from step_swap7
    | moves_from step_swap8
    | moves_from step_swap9
    | moves_from step_swap10
    | moves_from step_swap11
    | moves_from step_swap12
    | moves_from step_swap13
    | moves_from step_swap14
    | moves_from step_swap15
    | moves_from step_swap16

/-- `PUSHn` moves past its immediate with it on top. -/
theorem push_moves {s : State} {op : Operation.POp} {arg : UInt256} {w : Nat} (h0 : op ≠ .PUSH0)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.Push op, some (arg, w))) :
    Moves s (s.machineState.pc + UInt256.ofNat w.succ) (arg :: s.machineState.stack) :=
  moves_of (step_push s op arg w h0 hdec)

theorem push0_moves {s : State}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, none)) :
    Moves s (s.machineState.pc + ⟨1⟩) (⟨0⟩ :: s.machineState.stack) :=
  moves_of (step_push0 s hdec)

theorem pop_moves {s : State} {a : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.POP, none))
    (hs : s.machineState.stack = a :: t) :
    Moves s (s.machineState.pc + ⟨1⟩) t := by
  have h := step_pop s hdec
  simp only [hs] at h
  exact moves_of h

theorem jumpdest_moves {s : State}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.JUMPDEST, none)) :
    Moves s (s.machineState.pc + ⟨1⟩) s.machineState.stack :=
  moves_of (step_jumpdest s hdec)

/-- `JUMP` to a valid destination moves there. -/
theorem jump_moves {s : State} {a : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.JUMP, none))
    (hs : s.machineState.stack = a :: t) (hj : (D_J s.executionEnv.code 0).contains a = true) :
    Moves s a t := by
  have h := step_jump s hdec
  simp only [hs, hj, not_true_eq_false, if_false] at h
  exact moves_of h

/-- `JUMPI` moves to its destination, valid when the condition is not zero, or past itself. -/
theorem jumpi_moves {s : State} {a b : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, none))
    (hs : s.machineState.stack = a :: b :: t)
    (hj : b != ⟨0⟩ → (D_J s.executionEnv.code 0).contains a = true) :
    Moves s (if b != ⟨0⟩ then a else s.machineState.pc + ⟨1⟩) t := by
  have h := step_jumpi s hdec
  have hn : ¬((b != ⟨0⟩) = true ∧ ¬(D_J s.executionEnv.code 0).contains a = true) :=
    fun ⟨h1, h2⟩ => h2 (hj h1)
  simp only [hs, hn, if_false] at h
  exact moves_of h

end Fe.Sonatina.Check
