import Fe.Sonatina.CheckStep
import Fe.EVM.World
import Reasoning.Memory

/-!
# One step of the bytes on state

The bytes' steps on an event's opcode against the model's world.  `Agree s w`: the EVM state
holds the world's memory, accounts and logs.  `evRun op args` is what the event does to the
world, by the functions of `Fe.EVM` the interpreter's EVM instructions run.  `EvMoves`: one
`Xstep` runs out of gas or stack, or fails under a static call where the world's operation
does, or does what it does and moves on with the word it reads on top, the states still
agreeing.  `event_evMoves` gives it for every opcode of `readOps` and `writeOps` from
EVMLean's `step_*` lemmas.  The logs agree too, so the proof reaches profile `P1`.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The EVM state holds the model's world: its memory, accounts and logs. -/
structure Agree (s : State) (w : World) : Prop where
  memory : s.machineState.memory = w.memory
  accounts : s.accountMap = w.accounts
  logs : s.substate.logSeries = w.logs

/-- What an event does to the model's world, on its operands top first: for a read, the word. -/
def evRun : Operation → List UInt256 → FeM (Option UInt256)
  | .SLOAD, [k] => some <$> sload k
  | .MLOAD, [a] => some <$> mload a
  | .KECCAK256, [p, l] => some <$> keccak256 p l
  | .SSTORE, [k, v] => do sstore k v; return none
  | .MSTORE, [a, v] => do mstore a v; return none
  | .MSTORE8, [a, v] => do mstore8 a v; return none
  | .CODECOPY, [d, o, l] => do codecopy d o l; return none
  | .CALLDATACOPY, [d, o, l] => do calldatacopy d o l; return none
  | .MCOPY, [d, o, l] => do mcopy d o l; return none
  | .LOG0, [p, l] => do logData p l #[]; return none
  | .LOG1, [p, l, a] => do logData p l #[a]; return none
  | .LOG2, [p, l, a, b] => do logData p l #[a, b]; return none
  | .LOG3, [p, l, a, b, c] => do logData p l #[a, b, c]; return none
  | .LOG4, [p, l, a, b, c, d] => do logData p l #[a, b, c, d]; return none
  | _, _ => Fe.M.diverge

/-- One step of the bytes on an event's opcode, its operands `args` on top of `t`: it runs out of
    gas or stack, or fails under a static call as the world's operation does, or does what the
    world's operation does and moves on with the read word on top. -/
def EvMoves (s : State) (op : Operation) (args t : List UInt256) : Prop :=
  ∀ w, Agree s w →
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    Xstep (D_J s.executionEnv.code 0) s = .error .StackOverflow ∨
    ((evRun op args).exec s.executionEnv w = some (.error .static) ∧
      Xstep (D_J s.executionEnv.code 0) s = .error .StaticModeViolation) ∨
    ∃ r w' s', (evRun op args).exec s.executionEnv w = some (.ok (r, w')) ∧
      Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧ s'.machineState.stack = r.toList ++ t ∧
      s'.executionEnv = s.executionEnv ∧ Agree s' w'

/-- The word `MLOAD` pushes is the model's `mload`. -/
theorem mloadValue (mem : ByteArray) (a : UInt256) :
    (if a.toNat ≥ mem.size then (⟨0⟩ : UInt256)
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) =
      uInt256OfByteArray (mem.readWithPadding a.toNat 32) := by
  rw [Reasoning.Theory.uInt256OfByteArray_eq]
  split_ifs with h
  · have h0 := Reasoning.Theory.empty_readWithPadding_word_zero
    rw [Reasoning.Theory.uInt256OfByteArray_eq] at h0
    rw [← h0]
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    simp [h]
  · rfl

set_option hygiene false in
/-- `EvMoves` from the step lemma `l` of EVMLean. -/
local macro "evmoves_from " l:ident : tactic => `(tactic| (
    intro w ⟨hm, ha, hl⟩
    have h := $l s hdec
    simp only [hs, mloadValue, hm, ha, hl] at h
    rw [h]
    split_ifs <;> first
      | exact .inl rfl
      | exact .inr (.inl rfl)
      | exact .inr (.inr (.inl ⟨by simp_all [evRun, Fe.EVM.logData, Fe.EVM.emit], rfl⟩))
      | exact .inr (.inr (.inr ⟨_, _, _, rfl, rfl, rfl, by simp [Fe.EVM.slotWord], rfl,
          ⟨by simp [hm], by simp [ha], by simp [hl]⟩⟩))
      | exact .inr (.inr (.inr ⟨none, _, _, by simp [evRun, Fe.EVM.logData, Fe.EVM.emit, *]; rfl,
          rfl, rfl, by simp, rfl, ⟨by simp [hm], by simp [ha], by simp [hl]⟩⟩))))

theorem sload_evMoves {s : State} {k : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SLOAD, none))
    (hs : s.machineState.stack = k :: t) : EvMoves s .SLOAD [k] t := by
  evmoves_from step_sload

theorem mload_evMoves {s : State} {a : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, none))
    (hs : s.machineState.stack = a :: t) : EvMoves s .MLOAD [a] t := by
  evmoves_from step_mload

theorem keccak_evMoves {s : State} {p l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.KECCAK256, none))
    (hs : s.machineState.stack = p :: l :: t) : EvMoves s .KECCAK256 [p, l] t := by
  evmoves_from step_keccak

theorem mstore_evMoves {s : State} {a v : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, none))
    (hs : s.machineState.stack = a :: v :: t) : EvMoves s .MSTORE [a, v] t := by
  evmoves_from step_mstore

theorem mstore8_evMoves {s : State} {a v : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MSTORE8, none))
    (hs : s.machineState.stack = a :: v :: t) : EvMoves s .MSTORE8 [a, v] t := by
  evmoves_from step_mstore8

theorem codecopy_evMoves {s : State} {d o l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CODECOPY, none))
    (hs : s.machineState.stack = d :: o :: l :: t) : EvMoves s .CODECOPY [d, o, l] t := by
  evmoves_from step_codecopy

theorem calldatacopy_evMoves {s : State} {d o l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALLDATACOPY, none))
    (hs : s.machineState.stack = d :: o :: l :: t) : EvMoves s .CALLDATACOPY [d, o, l] t := by
  evmoves_from step_calldatacopy

theorem mcopy_evMoves {s : State} {d o l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.MCOPY, none))
    (hs : s.machineState.stack = d :: o :: l :: t) : EvMoves s .MCOPY [d, o, l] t := by
  evmoves_from step_mcopy

theorem log0_evMoves {s : State} {p l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LOG0, none))
    (hs : s.machineState.stack = p :: l :: t) : EvMoves s .LOG0 [p, l] t := by
  evmoves_from step_log0

theorem log1_evMoves {s : State} {p l x : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LOG1, none))
    (hs : s.machineState.stack = p :: l :: x :: t) : EvMoves s .LOG1 [p, l, x] t := by
  evmoves_from step_log1

theorem log2_evMoves {s : State} {p l x y : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LOG2, none))
    (hs : s.machineState.stack = p :: l :: x :: y :: t) : EvMoves s .LOG2 [p, l, x, y] t := by
  evmoves_from step_log2

theorem log3_evMoves {s : State} {p l x y z : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LOG3, none))
    (hs : s.machineState.stack = p :: l :: x :: y :: z :: t) :
    EvMoves s .LOG3 [p, l, x, y, z] t := by
  evmoves_from step_log3

theorem log4_evMoves {s : State} {p l x y z u : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.LOG4, none))
    (hs : s.machineState.stack = p :: l :: x :: y :: z :: u :: t) :
    EvMoves s .LOG4 [p, l, x, y, z, u] t := by
  evmoves_from step_log4

theorem sstore_evMoves {s : State} {k v : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SSTORE, none))
    (hs : s.machineState.stack = k :: v :: t) : EvMoves s .SSTORE [k, v] t := by
  intro w ⟨hm, ha, hl⟩
  have h := step_sstore s hdec
  simp only [hs] at h
  rw [h]
  by_cases h1 : s.machineState.gasAvailable.toNat < Csstore s
  · rw [if_pos h1]; exact .inl rfl
  rw [if_neg h1]
  by_cases h2 : (k :: v :: t).length - 2 + 0 > 1024
  · rw [if_pos h2]; exact .inr (.inl rfl)
  rw [if_neg h2]
  by_cases h3 : ¬s.executionEnv.perm = true
  · rw [if_pos h3]
    exact .inr (.inr (.inl ⟨by simp [evRun, Fe.EVM.sstore, h3], rfl⟩))
  rw [if_neg h3]
  by_cases h4 : s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos h4]; exact .inl rfl
  rw [if_neg h4]
  refine .inr (.inr (.inr ⟨none,
    { w with accounts := Fe.EVM.storeWord s.executionEnv.codeOwner w.accounts k v }, _, ?_, rfl,
    rfl, by simp, rfl, ⟨hm, ?_, ?_⟩⟩))
  · simp only [not_not] at h3
    simp [evRun, Fe.EVM.sstore, h3]
  · simp only [Fe.EVM.storeWord, ha]
  · show Substate.logSeries (Option.option _ _ _) = _
    cases Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner <;> exact hl

/-- An event's opcode, its operands on top, steps as `EvMoves` says. -/
theorem event_evMoves {s : State} {op : Operation} {args t : List UInt256}
    (hp : (readOps.contains op || writeOps.contains op) = true)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, none))
    (hs : s.machineState.stack = args ++ t) (hk : δ op = some args.length) :
    EvMoves s op args t := by
  simp only [readOps, writeOps, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨g, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
      <;>
      simp [δ] at hk
    simp only [List.cons_append, List.nil_append] at hs
  · exact sload_evMoves hdec hs
  · exact mload_evMoves hdec hs
  · exact keccak_evMoves hdec hs
  · exact sstore_evMoves hdec hs
  · exact mstore_evMoves hdec hs
  · exact mstore8_evMoves hdec hs
  · exact codecopy_evMoves hdec hs
  · exact calldatacopy_evMoves hdec hs
  · exact mcopy_evMoves hdec hs
  · exact log0_evMoves hdec hs
  · exact log1_evMoves hdec hs
  · exact log2_evMoves hdec hs
  · exact log3_evMoves hdec hs
  · exact log4_evMoves hdec hs

end Fe.Sonatina.Check
