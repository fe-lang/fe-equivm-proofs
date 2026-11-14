import Fe.Sonatina.CheckStep
import Fe.EVM.World
import Reasoning.Memory

/-!
# One step of the bytes on state

The bytes' steps on an event's opcode against the model's world.  `Agree s w`: the EVM state
holds the world's memory, accounts, logs and return data, and the world's feed is the one the
bytes' run supplies from `s` (`Feeds`: at each `GAS`, the word it pushes).  `evRun op args` is what the event does to the
world, by the functions of `Fe.EVM` the interpreter's EVM instructions run.  `EvMoves`: one
`Xstep` runs out of gas or stack, or fails under a static call where the world's operation
does (`Fails`: a write under a static call, a copy past the return data), or does what it does
and moves on with the word it reads on top, the states still agreeing.  `event_evMoves` gives it for every opcode of `readOps` and `writeOps` from
EVMLean's `step_*` lemmas.  The logs agree too, so the proof reaches profile `P1`.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The entry of the feed a step of the bytes from `s` supplies: the word `GAS` pushes, which
    the model's `gas` reads from its feed. -/
def supplyOf (s : State) : List Supply :=
  match decode s.executionEnv.code s.machineState.pc with
  | some (.GAS, _) =>
    [{ gas := (s.machineState.gasAvailable.subNat GasConstants.Gbase).toUInt256
       substate := default, orig := default }]
  | _ => []

/-- `f` is the feed the bytes' run from `s` supplies, step by step until it stops: the
    model's run under it reads at each step what the bytes compute there. -/
inductive Feeds : State → List Supply → Prop
  | stop {s : State} (h : ∀ s', Xstep (D_J s.executionEnv.code 0) s ≠ .ok (s', none)) :
      Feeds s []
  | step {s s' : State} {f : List Supply}
      (h : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) (rest : Feeds s' f) :
      Feeds s (supplyOf s ++ f)

/-- A step that goes on supplies its entry and the rest of the run's. -/
theorem Feeds.next {s s' : State} {f : List Supply} (h : Feeds s f)
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) :
    ∃ f', f = supplyOf s ++ f' ∧ Feeds s' f' := by
  cases h with
  | stop h => exact absurd hx (h s')
  | step h rest =>
    rw [hx] at h
    cases h
    exact ⟨_, rfl, rest⟩

/-- Every run of the bytes supplies a feed: each step that goes on spends gas. -/
theorem feeds_exists : ∀ (n : Nat) (s : State), s.machineState.gasAvailable.toNat < n →
    ∃ f, Feeds s f
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
    by_cases hx : ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)
    · obtain ⟨s', hx⟩ := hx
      have := Xstep_gas_decreases_of_continues hx
      obtain ⟨f, hf⟩ := feeds_exists n s' (by omega)
      exact ⟨_, .step hx hf⟩
    · exact ⟨[], .stop fun s' h => hx ⟨s', h⟩⟩

/-- An opcode other than `GAS` supplies nothing. -/
theorem supplyOf_eq {s : State} {op : Operation} {a : Option (UInt256 × Nat)}
    (h : decode s.executionEnv.code s.machineState.pc = some (op, a)) (hop : op ≠ .GAS) :
    supplyOf s = [] := by
  unfold supplyOf
  rw [h]
  split
  · next h' => cases h'; exact absurd rfl hop
  · rfl

/-- The EVM state holds the model's world: its memory, accounts, logs and return data, and the
    world's feed is what the bytes' run supplies from there. -/
structure Agree (s : State) (w : World) : Prop where
  memory : s.machineState.memory = w.memory
  accounts : s.accountMap = w.accounts
  logs : s.substate.logSeries = w.logs
  returnData : s.machineState.returnData = w.returnData
  feed : Feeds s w.feed

/-- A step that supplies nothing and keeps memory, accounts, logs and return data keeps the
    world agreeing. -/
theorem Agree.quiet {s s' : State} {w : World} (hw : Agree s w)
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) (hq : supplyOf s = [])
    (hm : s'.machineState.memory = s.machineState.memory) (ha : s'.accountMap = s.accountMap)
    (hl : s'.substate.logSeries = s.substate.logSeries)
    (hr : s'.machineState.returnData = s.machineState.returnData) : Agree s' w := by
  obtain ⟨f', hf, hF⟩ := hw.feed.next hx
  rw [hq, List.nil_append] at hf
  exact ⟨hm.trans hw.memory, ha.trans hw.accounts, hl.trans hw.logs, hr.trans hw.returnData,
    hf ▸ hF⟩

/-- What an event does to the model's world, on its operands top first: for a read, the word. -/
def evRun : Operation → List UInt256 → FeM (Option UInt256)
  | .SLOAD, [k] => some <$> sload k
  | .MLOAD, [a] => some <$> mload a
  | .KECCAK256, [p, l] => some <$> keccak256 p l
  | .SELFBALANCE, [] => some <$> selfbalance
  | .BALANCE, [a] => some <$> balance a
  | .EXTCODESIZE, [a] => some <$> extcodesize a
  | .RETURNDATASIZE, [] => some <$> returndatasize
  | .GAS, [] => some <$> gas
  | .SSTORE, [k, v] => do sstore k v; return none
  | .MSTORE, [a, v] => do mstore a v; return none
  | .MSTORE8, [a, v] => do mstore8 a v; return none
  | .CODECOPY, [d, o, l] => do codecopy d o l; return none
  | .CALLDATACOPY, [d, o, l] => do calldatacopy d o l; return none
  | .MCOPY, [d, o, l] => do mcopy d o l; return none
  | .RETURNDATACOPY, [d, o, l] => do returndatacopy d o l; return none
  | .LOG0, [p, l] => do logData p l #[]; return none
  | .LOG1, [p, l, a] => do logData p l #[a]; return none
  | .LOG2, [p, l, a, b] => do logData p l #[a, b]; return none
  | .LOG3, [p, l, a, b, c] => do logData p l #[a, b, c]; return none
  | .LOG4, [p, l, a, b, c, d] => do logData p l #[a, b, c, d]; return none
  | _, _ => Fe.M.diverge

/-- An event's failure in the model is the bytes' exception: a write under a static call, a
    copy past the end of the return data. -/
def Fails : Fe.Exit World → ExecutionException → Prop
  | .static, e => e = .StaticModeViolation
  | .oob, e => e = .InvalidMemoryAccess
  | _, _ => False

/-- One step of the bytes on an event's opcode, its operands `args` on top of `t`: it runs out of
    gas or stack, or fails as the world's operation does, or does what the world's operation
    does and moves on with the read word on top. -/
def EvMoves (s : State) (op : Operation) (args t : List UInt256) : Prop :=
  ∀ w, Agree s w →
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    Xstep (D_J s.executionEnv.code 0) s = .error .StackOverflow ∨
    (∃ f e, (evRun op args).exec s.executionEnv w = some (.error f) ∧
      Xstep (D_J s.executionEnv.code 0) s = .error e ∧ Fails f e) ∨
    ∃ r w' s', (evRun op args).exec s.executionEnv w = some (.ok (r, w')) ∧
      Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧ s'.machineState.stack = r.toList ++ t ∧
      s'.executionEnv = s.executionEnv ∧ Agree s' w'

/-- An event's step that goes on, supplying nothing, with the world's operation doing to the
    world what the step does to the state. -/
theorem evMoves_ok {s s' : State} {op : Operation} {args t : List UInt256} {w w' : World}
    {r : Option UInt256} (hw : Agree s w) (hq : supplyOf s = [])
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none))
    (he : (evRun op args).exec s.executionEnv w = some (.ok (r, w')))
    (hpc : s'.machineState.pc = s.machineState.pc + ⟨1⟩)
    (hst : s'.machineState.stack = r.toList ++ t) (henv : s'.executionEnv = s.executionEnv)
    (hm : s'.machineState.memory = w'.memory) (ha : s'.accountMap = w'.accounts)
    (hl : s'.substate.logSeries = w'.logs) (hr : s'.machineState.returnData = w'.returnData)
    (hf : w'.feed = w.feed) :
    ∃ r w' s', (evRun op args).exec s.executionEnv w = some (.ok (r, w')) ∧
      Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧ s'.machineState.stack = r.toList ++ t ∧
      s'.executionEnv = s.executionEnv ∧ Agree s' w' := by
  obtain ⟨f', hf', hF⟩ := hw.feed.next hx
  rw [hq, List.nil_append] at hf'
  exact ⟨r, w', s', he, hx, hpc, hst, henv, ⟨hm, ha, hl, hr, by rw [hf, hf']; exact hF⟩⟩

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
/-- A field of `Agree` after an event's step, from the one before it. -/
local macro "agree_field" : tactic => `(tactic| first
  | rfl
  | simp [hw.memory, hw.accounts, hw.logs, hw.returnData, Fe.EVM.logData, Fe.EVM.emit])

set_option hygiene false in
/-- `EvMoves` from the step lemma `l` of EVMLean. -/
local macro "evmoves_from " l:ident : tactic => `(tactic| (
    intro w hw
    have h := $l s hdec
    simp only [hs, mloadValue, hw.memory, hw.accounts, hw.logs, hw.returnData] at h
    split_ifs at h <;> first
      | exact .inl h
      | exact .inr (.inl h)
      | exact .inr (.inr (.inl ⟨.static, _, by simp_all [evRun, Fe.EVM.logData, Fe.EVM.emit],
          h, rfl⟩))
      | exact .inr (.inr (.inl ⟨.oob, _, by simp_all [evRun, Fe.EVM.returndatacopy], h, rfl⟩))
      | exact .inr (.inr (.inr (evMoves_ok hw (supplyOf_eq hdec (by decide)) h rfl rfl
          (by simp [Fe.EVM.slotWord]) rfl (by agree_field) (by agree_field) (by agree_field)
          (by agree_field) (by rfl))))
      | exact .inr (.inr (.inr (evMoves_ok (r := none) hw (supplyOf_eq hdec (by decide)) h
          (by simp [evRun, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.returndatacopy, *]; rfl) rfl
          (by simp) rfl (by agree_field) (by agree_field) (by agree_field) (by agree_field)
          (by rfl))))))

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

theorem selfbalance_evMoves {s : State} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SELFBALANCE, none))
    (hs : s.machineState.stack = t) : EvMoves s .SELFBALANCE [] t := by
  evmoves_from step_selfbalance

theorem balance_evMoves {s : State} {a : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.BALANCE, none))
    (hs : s.machineState.stack = a :: t) : EvMoves s .BALANCE [a] t := by
  evmoves_from step_balance

theorem extcodesize_evMoves {s : State} {a : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.EXTCODESIZE, none))
    (hs : s.machineState.stack = a :: t) : EvMoves s .EXTCODESIZE [a] t := by
  evmoves_from step_extcodesize

theorem returndatasize_evMoves {s : State} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.RETURNDATASIZE, none))
    (hs : s.machineState.stack = t) : EvMoves s .RETURNDATASIZE [] t := by
  evmoves_from step_returndatasize

theorem returndatacopy_evMoves {s : State} {d o l : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.RETURNDATACOPY, none))
    (hs : s.machineState.stack = d :: o :: l :: t) : EvMoves s .RETURNDATACOPY [d, o, l] t := by
  evmoves_from step_returndatacopy

/-- `GAS` pushes the gas left, which the feed supplies the model's `gas`. -/
theorem gas_evMoves {s : State} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.GAS, none))
    (hs : s.machineState.stack = t) : EvMoves s .GAS [] t := by
  intro w hw
  have h := step_gas s hdec
  split_ifs at h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨f', hf, hF⟩ := hw.feed.next h
    have hq : supplyOf s =
        [⟨(s.machineState.gasAvailable.subNat GasConstants.Gbase).toUInt256, default, default⟩] := by
      unfold supplyOf; rw [hdec]
    rw [hq] at hf
    refine .inr (.inr (.inr ⟨_, { w with feed := f' }, _,
      by simp [evRun, Fe.EVM.gas, Fe.EVM.next, hf]; rfl, h, rfl, by simp [hs], rfl,
      ⟨hw.memory, hw.accounts, hw.logs, hw.returnData, hF⟩⟩))

theorem sstore_evMoves {s : State} {k v : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SSTORE, none))
    (hs : s.machineState.stack = k :: v :: t) : EvMoves s .SSTORE [k, v] t := by
  intro w hw
  have h := step_sstore s hdec
  simp only [hs] at h
  by_cases h1 : s.machineState.gasAvailable.toNat < Csstore s
  · rw [if_pos h1] at h; exact .inl h
  rw [if_neg h1] at h
  by_cases h2 : (k :: v :: t).length - 2 + 0 > 1024
  · rw [if_pos h2] at h; exact .inr (.inl h)
  rw [if_neg h2] at h
  by_cases h3 : ¬s.executionEnv.perm = true
  · rw [if_pos h3] at h
    exact .inr (.inr (.inl ⟨.static, _, by simp [evRun, Fe.EVM.sstore, h3], h, rfl⟩))
  rw [if_neg h3] at h
  by_cases h4 : s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos h4] at h; exact .inl h
  rw [if_neg h4] at h
  simp only [not_not] at h3
  refine .inr (.inr (.inr (evMoves_ok (r := none) hw (supplyOf_eq hdec (by decide)) h
    (w' := { w with accounts := Fe.EVM.storeWord s.executionEnv.codeOwner w.accounts k v })
    (by simp [evRun, Fe.EVM.sstore, h3]) rfl (by simp) rfl hw.memory ?_ ?_ hw.returnData rfl)))
  · simp only [Fe.EVM.storeWord, hw.accounts]
  · show Substate.logSeries (Option.option _ _ _) = _
    cases Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner <;> exact hw.logs

/-- An event's opcode, its operands on top, steps as `EvMoves` says. -/
theorem event_evMoves {s : State} {op : Operation} {args t : List UInt256}
    (hp : (readOps.contains op || writeOps.contains op) = true)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, none))
    (hs : s.machineState.stack = args ++ t) (hk : δ op = some args.length) :
    EvMoves s op args t := by
  simp only [readOps, writeOps, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨g, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩
      <;>
      simp [δ] at hk
    simp only [List.cons_append, List.nil_append] at hs
  · exact sload_evMoves hdec hs
  · exact mload_evMoves hdec hs
  · exact keccak_evMoves hdec hs
  · exact selfbalance_evMoves hdec hs
  · exact balance_evMoves hdec hs
  · exact extcodesize_evMoves hdec hs
  · exact returndatasize_evMoves hdec hs
  · exact gas_evMoves hdec hs
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
  · exact returndatacopy_evMoves hdec hs

end Fe.Sonatina.Check
