import Fe.Sonatina.CheckStep
import Fe.EVM.World
import Reasoning.Memory
import Fe.EVM.LogsAppend
import Fe.EVM.Invariant

/-!
# One step of the bytes on state

The bytes' steps on an event's opcode against the model's world.  `Agree M s w`: the EVM state
holds the world's memory, accounts, logs and return data, the world's feed is the one the bytes'
run supplies from `s`, and the calls the world has made followed by those the bytes' run makes
from `s` are `M` (`Fut`: at each step, the entry `supplyOf` gives, the word `GAS` pushes or the
inputs a message call reads, and the call or creation `madeOf` gives, what `XstepOk` asks of the
step).  `Fut.xOk`: a run whose calls and creations satisfy a condition satisfies `XOk`.
`evRun op args` is what the event does to the world, by the functions of `Fe.EVM` the
interpreter's EVM instructions run.  `EvMoves`: one `Xstep` runs out of gas or stack, or fails
under a static call where the world's operation does (`Fails`: a write under a static call, a
copy past the return data), or does what it does and moves on with the word it reads on top, the
states still agreeing.  `event_evMoves` gives it for every opcode of `readOps` and `writeOps`
from EVMLean's `step_*` lemmas, `CALL` the model's `call` on the feed's entry (`call_evMoves`).
The logs agree too, so the proof reaches profile `P1`.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The opcodes that make a message call or a creation. -/
def callOps : List Operation := [.CREATE, .CREATE2, .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL]

/-- The instruction at the state's pc, as `Xstep` decodes it, makes no message call or
    creation. -/
def Calm (s : State) : Prop :=
  callOps.contains (decode s.executionEnv.code s.machineState.pc |>.getD (.STOP, .none)).1 = false

theorem calm_of {s : State} {op : Operation} {a : Option (UInt256 × Nat)}
    (h : decode s.executionEnv.code s.machineState.pc = some (op, a))
    (hc : callOps.contains op = false) : Calm s := by
  simp only [Calm, h, Option.getD_some]
  exact hc

/-- An opcode of a list without calls or creations is calm. -/
theorem calm_of_mem {s : State} {op : Operation} {a : Option (UInt256 × Nat)}
    {L : List Operation} (h : decode s.executionEnv.code s.machineState.pc = some (op, a))
    (hL : L.all (!callOps.contains ·) = true) (hop : L.contains op = true) : Calm s := by
  refine calm_of h ?_
  have := List.all_eq_true.mp hL op (by simpa using hop)
  simpa using this

/-- The state `Z` hands an instruction's step: the memory it expands paid for. -/
def zState (s : State) (op : Operation) : State :=
  { s with machineState.gasAvailable :=
      s.machineState.gasAvailable.subNat (memoryExpansionCost s op) }

/-- The state a message call's inputs are read from, as `step` and `stepOk` read them. -/
def callState (s : State) (op : Operation) : State :=
  { zState s op with machineState.execLength := s.machineState.execLength + 1 }

theorem Z_ok {D : Array UInt256} {op : Operation} {s s' : State} {c : Nat}
    (h : Z D op s = .ok (s', c)) : s' = zState s op ∧ c = C' (zState s op) op :=
  Z_ok_eq_charged_cost h

/-- A step that goes on passed `Z`. -/
theorem Z_of_Xstep {D : Array UInt256} {s : State}
    {r : State × Option (HaltCause × ByteArray)} (h : Xstep D s = .ok r) :
    ∃ c, Z D (decode s.executionEnv.code s.machineState.pc |>.getD (.STOP, .none)).1 s =
      .ok (zState s (decode s.executionEnv.code s.machineState.pc |>.getD (.STOP, .none)).1, c) := by
  cases hz : Z D (decode s.executionEnv.code s.machineState.pc |>.getD (.STOP, .none)).1 s with
  | error e => simp [Xstep, hz] at h
  | ok p =>
    obtain ⟨s', c⟩ := p
    obtain ⟨rfl, -⟩ := Z_ok hz
    exact ⟨c, rfl⟩

/-- The gas a message call forwards is the model's `forwardedGas` of the cap `Cgascap`. -/
theorem forwardedGas_Cgascap (t r : AccountAddress) (value gasArg : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    forwardedGas (.ofNat (Cgascap t r value gasArg σ μ A)) gasArg value =
      .ofNat (Ccallgas t r value gasArg σ μ A) := by
  have hle := Cgascap_le t r value gasArg σ μ A
  have hto : (UInt256.ofNat (Cgascap t r value gasArg σ μ A)).toNat =
      Cgascap t r value gasArg σ μ A := by
    show (Fin.ofNat _ _).val = _
    simp only [Fin.ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle gasArg.val.isLt)
  unfold forwardedGas Ccallgas
  rw [hto, Nat.min_eq_left hle]
  by_cases hv : value = ⟨0⟩
  · subst hv
    rfl
  · rw [if_neg hv]
    split
    · exact absurd rfl hv
    · rfl

/-- The entry of the feed a step of the bytes from `s` supplies: the word `GAS` pushes, which
    the model's `gas` reads, and for a message call the inputs the EVM hands the callee and the
    model's `message` reads, made or not: the gas cap, the substate with the callee's address
    accessed, and the transaction's original account map. -/
def supplyOf (s : State) : List Supply :=
  let call (op : Operation) (gas t value : UInt256) (r : AccountAddress) : List Supply :=
    [⟨.ofNat (Cgascap (.ofUInt256 t) r value gas s.accountMap (callState s op).machineState
        s.substate), (s.addAccessedAccount (.ofUInt256 t)).substate, s.σ₀⟩]
  match decode s.executionEnv.code s.machineState.pc, s.machineState.stack with
  | some (.GAS, _), _ =>
    [{ gas := (s.machineState.gasAvailable.subNat GasConstants.Gbase).toUInt256
       substate := default, orig := default }]
  | some (.CALL, _), gas :: t :: value :: _ => call .CALL gas t value (.ofUInt256 t)
  | some (.STATICCALL, _), gas :: t :: _ => call .STATICCALL gas t ⟨0⟩ (.ofUInt256 t)
  | some (.DELEGATECALL, _), gas :: t :: _ =>
    call .DELEGATECALL gas t ⟨0⟩ (.ofUInt256 (.ofNat s.executionEnv.codeOwner))
  | _, _ => []

/-! ## The calls a step makes, as `stepOk` asks of them -/

open Ethereum.EVM.Invariant in
/-- The message call `call` makes, if it makes one: what `callOk` asks `Q` of. -/
def callMade (gas source recipient t value value' inOffset inSize : UInt256) (permission : Bool)
    (evmState : State) : List Made :=
  if value ≤ (evmState.accountMap.get? evmState.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))
      ∧ evmState.executionEnv.depth < 1024 then
    [.theta (callArgs gas source recipient t value value' inOffset inSize permission evmState)]
  else []

/-- The creation `create` makes, if it makes one: what `createOk` asks `Q` of. -/
def createMade (value offset size : UInt256) (salt : Option ByteArray) (evmState : State) :
    List Made :=
  let i := evmState.machineState.memory.readWithPadding offset.toNat size.toNat
  let I := evmState.executionEnv
  let σ := evmState.accountMap
  let self : Account := σ.get? I.codeOwner |>.getD default
  if ¬ self.nonce.toNat ≥ 2 ^ 64 - 1 then
    if h : value ≤ (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
        ∧ i.size ≤ 49152 then
      [.lambda
        { σ := σ.insert I.codeOwner {self with nonce := self.nonce + ⟨1⟩}
          σ₀ := evmState.σ₀, A := evmState.substate, s := I.codeOwner, o := I.sender
          g := .ofNat (L evmState.machineState.gasAvailable.toNat), p := .ofNat I.gasPrice
          v := value, i := i, e := ⟨I.depth.val + 1, Nat.succ_lt_succ h.2.1⟩, ζ := salt
          H := I.header, bvh := I.blobVersionedHashes, blocks := I.blocks, w := I.perm }]
    else []
  else []

/-- The message call or creation one instruction makes, if any, as `stepOk` reads it. -/
def madeAt (gasCost : ℕ) (instr : Operation × Option (UInt256 × Nat)) (state : State) :
    List Made :=
  let st : State := { state with machineState.execLength := state.machineState.execLength + 1 }
  let charged : State :=
    { st with machineState.gasAvailable := st.machineState.gasAvailable.subNat gasCost }
  match instr.1 with
  | .CREATE => match st.machineState.stack.pop3 with
    | some (_, value, offset, size) => createMade value offset size none charged
    | none => []
  | .CREATE2 => match st.machineState.stack.pop4 with
    | some (_, value, offset, size, salt) =>
      createMade value offset size (some salt.toByteArray) charged
    | none => []
  | .CALL => match st.machineState.stack.pop7 with
    | some (_, μ₀, μ₁, μ₂, μ₃, μ₄, _, _) =>
      callMade μ₀ (.ofNat state.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄
        state.executionEnv.perm st
    | none => []
  | .CALLCODE => match st.machineState.stack.pop7 with
    | some (_, μ₀, μ₁, μ₂, μ₃, μ₄, _, _) =>
      callMade μ₀ (.ofNat state.executionEnv.codeOwner) (.ofNat state.executionEnv.codeOwner)
        μ₁ μ₂ μ₂ μ₃ μ₄ state.executionEnv.perm st
    | none => []
  | .DELEGATECALL => match st.machineState.stack.pop6 with
    | some (_, μ₀, μ₁, μ₃, μ₄, _, _) =>
      callMade μ₀ (.ofNat state.executionEnv.source) (.ofNat state.executionEnv.codeOwner) μ₁
        ⟨0⟩ state.executionEnv.weiValue μ₃ μ₄ state.executionEnv.perm st
    | none => []
  | .STATICCALL => match st.machineState.stack.pop6 with
    | some (_, μ₀, μ₁, μ₃, μ₄, _, _) =>
      callMade μ₀ (.ofNat state.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ false st
    | none => []
  | _ => []

/-- The message call or creation the step from `s` makes, if any, as `XstepOk` reads it: none
    where `Z` stops the step. -/
def madeOf (s : State) : List Made :=
  match Z (D_J s.executionEnv.code 0)
      (decode s.executionEnv.code s.machineState.pc |>.getD (.STOP, .none)).1 s with
  | .ok (sZ, cost) => madeAt cost (decode s.executionEnv.code s.machineState.pc |>.getD
      (.STOP, .none)) { sZ with executionEnv.depth := s.executionEnv.depth }
  | .error _ => []

open Ethereum.EVM.Invariant in
theorem callMade_ok {Q : CallPreds} {gas source recipient t value value' inOffset inSize : UInt256}
    {permission : Bool} {evmState : State}
    (h : ∀ c ∈ callMade gas source recipient t value value' inOffset inSize permission evmState,
      c.Ok Q) :
    callOk Q gas source recipient t value value' inOffset inSize permission evmState := by
  intro hm
  exact h _ (by simp only [callMade, if_pos hm]; exact List.mem_singleton_self _)

open Ethereum.EVM.Invariant in
theorem createMade_ok {Q : CallPreds} {value offset size : UInt256} {salt : Option ByteArray}
    {evmState : State} (h : ∀ c ∈ createMade value offset size salt evmState, c.Ok Q) :
    createOk Q value offset size salt evmState := by
  intro hn hm
  exact h _ (by simp only [createMade, if_pos hn, dif_pos hm]; exact List.mem_singleton_self _)

open Ethereum.EVM.Invariant in
/-- `stepOk` holds of a step whose call or creation satisfies `Q`. -/
theorem madeAt_ok {Q : CallPreds} {gasCost : ℕ} {instr : Operation × Option (UInt256 × Nat)}
    {state : State} (h : ∀ c ∈ madeAt gasCost instr state, c.Ok Q) :
    stepOk Q gasCost instr state := by
  unfold stepOk
  unfold madeAt at h
  dsimp only
  dsimp only at h
  split
  next heq =>
    intro _ _ _ _ hp
    simp only [heq, hp] at h
    exact createMade_ok h
  next heq =>
    intro _ _ _ _ _ hp
    simp only [heq, hp] at h
    exact createMade_ok h
  next heq =>
    intro _ _ _ _ _ _ _ _ hp
    simp only [heq, hp] at h
    exact callMade_ok h
  next heq =>
    intro _ _ _ _ _ _ _ _ hp
    simp only [heq, hp] at h
    exact callMade_ok h
  next heq =>
    intro _ _ _ _ _ _ _ hp
    simp only [heq, hp] at h
    exact callMade_ok h
  next heq =>
    intro _ _ _ _ _ _ _ hp
    simp only [heq, hp] at h
    exact callMade_ok h
  · trivial

open Ethereum.EVM.Invariant in
/-- `XstepOk` holds of a state whose step's call or creation satisfies `Q`. -/
theorem madeOf_xstepOk {Q : CallPreds} {s : State} (h : ∀ c ∈ madeOf s, c.Ok Q) :
    XstepOk Q (D_J s.executionEnv.code 0) s := by
  intro sZ cost hZ
  unfold madeOf at h
  rw [hZ] at h
  exact madeAt_ok h

/-- A calm step makes no call nor creation. -/
theorem Calm.madeOf {s : State} (h : Calm s) : madeOf s = [] := by
  unfold Calm at h
  unfold Fe.Sonatina.Check.madeOf
  split
  · unfold madeAt
    generalize (decode s.executionEnv.code s.machineState.pc).getD (.STOP, .none) = instr at h ⊢
    split <;> simp_all [callOps]
  · rfl

/-- `f` is the feed the bytes' run from `s` supplies and `m` the calls and creations it makes,
    step by step until it stops: the model's run under `f` reads at each step what the bytes
    compute there.  The step that stops counts what `XstepOk` asks of it too, which is nothing
    where it halts. -/
inductive Fut : State → List Supply → List Made → Prop
  | stop {s : State} (h : ∀ s', Xstep (D_J s.executionEnv.code 0) s ≠ .ok (s', none)) :
      Fut s [] (madeOf s)
  | step {s s' : State} {f : List Supply} {m : List Made}
      (h : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) (rest : Fut s' f m) :
      Fut s (supplyOf s ++ f) (madeOf s ++ m)

/-- A step that goes on supplies its entry and makes its call, then the rest of the run's. -/
theorem Fut.next {s s' : State} {f : List Supply} {m : List Made} (h : Fut s f m)
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) :
    ∃ f' m', f = supplyOf s ++ f' ∧ m = madeOf s ++ m' ∧ Fut s' f' m' := by
  cases h with
  | stop h => exact absurd hx (h s')
  | step h rest =>
    rw [hx] at h
    cases h
    exact ⟨_, _, rfl, rfl, rest⟩

/-- Every run of the bytes supplies a feed: each step that goes on spends gas. -/
theorem fut_exists : ∀ (n : Nat) (s : State), s.machineState.gasAvailable.toNat < n →
    ∃ f m, Fut s f m
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
    by_cases hx : ∃ s', Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)
    · obtain ⟨s', hx⟩ := hx
      have := Xstep_gas_decreases_of_continues hx
      obtain ⟨f, m, hf⟩ := fut_exists n s' (by omega)
      exact ⟨_, _, .step hx hf⟩
    · exact ⟨[], _, .stop fun s' h => hx ⟨s', h⟩⟩

open Ethereum.EVM.Invariant in
/-- A run whose calls and creations satisfy `Q` satisfies `XOk`. -/
theorem Fut.xOk {Q : CallPreds} {s : State} {f : List Supply} {m : List Made} (h : Fut s f m)
    (hQ : ∀ c ∈ m, c.Ok Q) : ∀ n, XOk Q n (D_J s.executionEnv.code 0) s := by
  induction h with
  | stop h =>
    intro n
    cases n with
    | zero => trivial
    | succ n => exact ⟨madeOf_xstepOk hQ, fun s' hs' => absurd hs' (h s')⟩
  | @step s s' f m hx _ ih =>
    intro n
    cases n with
    | zero => trivial
    | succ n =>
      refine ⟨madeOf_xstepOk fun c hc => hQ c (List.mem_append_left _ hc), fun t ht => ?_⟩
      rw [hx] at ht
      cases ht
      have henv := Xstep_executionEnv_eq hx
      have := ih (fun c hc => hQ c (List.mem_append_right _ hc)) n
      rw [henv] at this
      rw [show { s' with executionEnv.depth := s.executionEnv.depth } = s' by rw [← henv]]
      exact this

/-- An opcode other than `GAS` and the message calls supplies nothing. -/
theorem supplyOf_eq {s : State} {op : Operation} {a : Option (UInt256 × Nat)}
    (h : decode s.executionEnv.code s.machineState.pc = some (op, a)) (hop : op ≠ .GAS)
    (hc : callOps.contains op = false) : supplyOf s = [] := by
  unfold supplyOf
  rw [h]
  split <;> simp_all [callOps]

/-- The EVM state holds the model's world: its memory, accounts, logs and return data; the
    world's feed is what the bytes' run supplies from there, and the calls the world made and
    those the bytes' run makes from there are `M`. -/
structure Agree (M : List Made) (s : State) (w : World) : Prop where
  memory : s.machineState.memory = w.memory
  accounts : s.accountMap = w.accounts
  logs : s.substate.logSeries = w.logs
  returnData : s.machineState.returnData = w.returnData
  fut : ∃ m, Fut s w.feed m ∧ w.calls ++ m = M

/-- A calm step that supplies nothing and keeps memory, accounts, logs and return data keeps
    the world agreeing. -/
theorem Agree.quiet {M : List Made} {s s' : State} {w : World} (hw : Agree M s w)
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none)) (hq : supplyOf s = [])
    (hc : Calm s)
    (hm : s'.machineState.memory = s.machineState.memory) (ha : s'.accountMap = s.accountMap)
    (hl : s'.substate.logSeries = s.substate.logSeries)
    (hr : s'.machineState.returnData = s.machineState.returnData) : Agree M s' w := by
  obtain ⟨m, hF, hM⟩ := hw.fut
  obtain ⟨f', m', hf, hm', hF'⟩ := hF.next hx
  rw [hq, List.nil_append] at hf
  rw [hc.madeOf, List.nil_append] at hm'
  exact ⟨hm.trans hw.memory, ha.trans hw.accounts, hl.trans hw.logs, hr.trans hw.returnData,
    ⟨m', by rw [hf]; exact hF', by rw [← hm']; exact hM⟩⟩

/-- Where the bytes stop at a calm state, the world has made the calls `M`. -/
theorem Agree.calls_of_stop {M : List Made} {s : State} {w : World} (hw : Agree M s w)
    (hc : Calm s) (hx : ∀ s', Xstep (D_J s.executionEnv.code 0) s ≠ .ok (s', none)) :
    w.calls = M := by
  obtain ⟨m, hF, hM⟩ := hw.fut
  generalize w.feed = f at hF
  cases hF with
  | stop _ => rwa [hc.madeOf, List.append_nil] at hM
  | step h _ => exact absurd h (hx _)

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
  | .CALL, [g, a, v, ap, al, rp, rl] => some <$> call g a v ap al rp rl
  | .STATICCALL, [g, a, ap, al, rp, rl] => some <$> staticcall g a ap al rp rl
  | .DELEGATECALL, [g, a, ap, al, rp, rl] => some <$> delegatecall g a ap al rp rl
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
  ∀ M w, Agree M s w →
    Xstep (D_J s.executionEnv.code 0) s = .error .OutOfGass ∨
    Xstep (D_J s.executionEnv.code 0) s = .error .StackOverflow ∨
    (∃ f e, (evRun op args).exec s.executionEnv w = some (.error f) ∧
      Xstep (D_J s.executionEnv.code 0) s = .error e ∧ Fails f e) ∨
    ∃ r w' s', (evRun op args).exec s.executionEnv w = some (.ok (r, w')) ∧
      Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧ s'.machineState.stack = r.toList ++ t ∧
      s'.executionEnv = s.executionEnv ∧ Agree M s' w'

/-- A calm event's step that goes on, supplying nothing, with the world's operation doing to the
    world what the step does to the state. -/
theorem evMoves_ok {M : List Made} {s s' : State} {op : Operation} {args t : List UInt256}
    {w w' : World} {r : Option UInt256} (hw : Agree M s w) (hq : supplyOf s = []) (hc : Calm s)
    (hx : Xstep (D_J s.executionEnv.code 0) s = .ok (s', none))
    (he : (evRun op args).exec s.executionEnv w = some (.ok (r, w')))
    (hpc : s'.machineState.pc = s.machineState.pc + ⟨1⟩)
    (hst : s'.machineState.stack = r.toList ++ t) (henv : s'.executionEnv = s.executionEnv)
    (hm : s'.machineState.memory = w'.memory) (ha : s'.accountMap = w'.accounts)
    (hl : s'.substate.logSeries = w'.logs) (hr : s'.machineState.returnData = w'.returnData)
    (hf : w'.feed = w.feed) (hcl : w'.calls = w.calls) :
    ∃ r w' s', (evRun op args).exec s.executionEnv w = some (.ok (r, w')) ∧
      Xstep (D_J s.executionEnv.code 0) s = .ok (s', none) ∧
      s'.machineState.pc = s.machineState.pc + ⟨1⟩ ∧ s'.machineState.stack = r.toList ++ t ∧
      s'.executionEnv = s.executionEnv ∧ Agree M s' w' := by
  obtain ⟨m, hF, hM⟩ := hw.fut
  obtain ⟨f', m', hf', hm', hF'⟩ := hF.next hx
  rw [hq, List.nil_append] at hf'
  rw [hc.madeOf, List.nil_append] at hm'
  exact ⟨r, w', s', he, hx, hpc, hst, henv, ⟨hm, ha, hl, hr, ⟨m', by rw [hf, hf']; exact hF',
    by rw [hcl, ← hm']; exact hM⟩⟩⟩

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
    intro M w hw
    have h := $l s hdec
    simp only [hs, mloadValue, hw.memory, hw.accounts, hw.logs, hw.returnData] at h
    split_ifs at h <;> first
      | exact .inl h
      | exact .inr (.inl h)
      | exact .inr (.inr (.inl ⟨.static, _, by simp_all [evRun, Fe.EVM.logData, Fe.EVM.emit],
          h, rfl⟩))
      | exact .inr (.inr (.inl ⟨.oob, _, by simp_all [evRun, Fe.EVM.returndatacopy], h, rfl⟩))
      | exact .inr (.inr (.inr (evMoves_ok hw (supplyOf_eq hdec (by decide) (by decide))
          (calm_of hdec (by decide)) h rfl rfl
          (by simp [Fe.EVM.slotWord]) rfl (by agree_field) (by agree_field) (by agree_field)
          (by agree_field) (by rfl) (by rfl))))
      | exact .inr (.inr (.inr (evMoves_ok (r := none) hw (supplyOf_eq hdec (by decide) (by decide))
          (calm_of hdec (by decide)) h
          (by simp [evRun, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.returndatacopy, *]; rfl) rfl
          (by simp) rfl (by agree_field) (by agree_field) (by agree_field) (by agree_field)
          (by rfl) (by rfl))))))

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
  intro M w hw
  have h := step_gas s hdec
  split_ifs at h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨m, hF, hM⟩ := hw.fut
    obtain ⟨f', m', hf, hm', hF'⟩ := hF.next h
    have hq : supplyOf s =
        [⟨(s.machineState.gasAvailable.subNat GasConstants.Gbase).toUInt256, default, default⟩] := by
      unfold supplyOf; rw [hdec]
    rw [hq] at hf
    rw [(calm_of hdec (by decide)).madeOf, List.nil_append] at hm'
    refine .inr (.inr (.inr ⟨_, { w with feed := f' }, _,
      by simp [evRun, Fe.EVM.gas, Fe.EVM.next, hf]; rfl, h, rfl, by simp [hs], rfl,
      ⟨hw.memory, hw.accounts, hw.logs, hw.returnData, ⟨m', hF', by rw [← hm']; exact hM⟩⟩⟩))

theorem sstore_evMoves {s : State} {k v : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.SSTORE, none))
    (hs : s.machineState.stack = k :: v :: t) : EvMoves s .SSTORE [k, v] t := by
  intro M w hw
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
  refine .inr (.inr (.inr (evMoves_ok (r := none) hw (supplyOf_eq hdec (by decide) (by decide))
    (calm_of hdec (by decide)) h
    (w' := { w with accounts := Fe.EVM.storeWord s.executionEnv.codeOwner w.accounts k v })
    (by simp [evRun, Fe.EVM.sstore, h3]) rfl (by simp) rfl hw.memory ?_ ?_ hw.returnData rfl
    rfl)))
  · simp only [Fe.EVM.storeWord, hw.accounts]
  · show Substate.logSeries (Option.option _ _ _) = _
    cases Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner <;> exact hw.logs

open Ethereum.EVM.Invariant in
/-- `CALL` is the model's `call`: out of gas or stack, the static failure, or the message call
    made or not, as the feed's entry and the bytes' step agree. -/
theorem call_evMoves {s : State} {g a v ap al rp rl : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.CALL, none))
    (hs : s.machineState.stack = g :: a :: v :: ap :: al :: rp :: rl :: t) :
    EvMoves s .CALL [g, a, v, ap, al, rp, rl] t := by
  rcases s with ⟨σ, σ₀, tg, tr, A, I, ⟨pc, stk, el, ga, aw, mem, rd, hr⟩⟩
  simp only at hs
  subst hs
  intro M w hw
  have h := step_call _ hdec
  simp only at h
  set S : State := ⟨σ, σ₀, tg, tr, A, I, ⟨pc, g :: a :: v :: ap :: al :: rp :: rl :: t, el, ga, aw,
    mem, rd, hr⟩⟩ with hSd
  have hI : S.executionEnv = I := rfl
  have hq : supplyOf S = [⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 a) v g σ
      (callState S .CALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate, σ₀⟩] := by
    unfold supplyOf; rw [hdec]
  have hmd : ∀ r, Xstep (D_J S.executionEnv.code 0) S = .ok r →
      madeOf S = callMade g (.ofNat I.codeOwner) a a v v ap al I.perm (callState S .CALL) := by
    intro r hx
    obtain ⟨c, hz⟩ := Z_of_Xstep hx
    unfold madeOf
    rw [hdec] at hz ⊢
    simp only [Option.getD_some] at hz ⊢
    rw [hz]
    rfl
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · exact .inl h
  · exact .inl h
  · exact .inr (.inl h)
  · have h4' : I.perm = false ∧ v ≠ ⟨0⟩ := by simpa using h4
    exact .inr (.inr (.inl ⟨.static, _, by simp [evRun, Fe.EVM.call, hI, h4'], h, rfl⟩))
  all_goals
    have hperm : I.perm = true ∨ v = ⟨0⟩ := by
      cases hp : I.perm
      · exact .inr (Classical.byContradiction fun hv => h4 ⟨by simp [hp], hv⟩)
      · exact .inl rfl
    obtain ⟨m, hF, hM⟩ := hw.fut
    obtain ⟨f', m', hf, hm', hF'⟩ := hF.next h
    rw [hq, List.singleton_append] at hf
  -- Made: `Θ` on the inputs the feed's entry completes, its success word on top.
  rotate_left 2
  -- Not made: no call, the word zero.
  · rw [hmd _ h, callMade, if_neg (by exact h5 : ¬ (v ≤ ((callState S .CALL).accountMap.get? (callState S .CALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .CALL).executionEnv.depth < 1024)),
      List.nil_append] at hm'
    have hex := call_notMade (addr := a) (value := v) (retPtr := rp) (retLen := rl) (argsPtr := ap) (argsLen := al)
      (gasArg := g) hf hperm (by rw [← hw.accounts]; exact h5)
    have hex' : (evRun .CALL [g, a, v, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some ⟨0⟩, { w with
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate
            (S.addAccessedAccount (.ofUInt256 a)).substate
          memory := ByteArray.empty.write 0 w.memory rp.toNat
            (min rl (.ofNat ByteArray.empty.size)).toNat
          returnData := ByteArray.empty
          feed := f' })) := by
      simp only [evRun, Fe.M.exec_map, hI, hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, rfl, rfl, ?_, hw.accounts, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]
    · rw [appended_self, Array.append_empty, ← hw.logs]; rfl
    · rw [← hM, hm']
  · rename_i hx
    exact absurd (by simp) hx
  all_goals
    have hcall : messageCall I w ⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 a) v g σ
        (callState S .CALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate, σ₀⟩
        g I.codeOwner (.ofUInt256 a) (.ofUInt256 a) v v ap al I.perm =
        callArgs g (.ofNat I.codeOwner) a a v v ap al I.perm (callState S .CALL) := by
      unfold messageCall callArgs
      rw [← hw.accounts, ← hw.memory, AccountAddress.ofUInt256_ofNat, forwardedGas_Cgascap]
      rfl
    set T := callArgs g (.ofNat I.codeOwner) a a v v ap al I.perm (callState S .CALL) with hT
    rw [hmd _ h, callMade, if_pos (by exact h5 : (v ≤ ((callState S .CALL).accountMap.get? (callState S .CALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .CALL).executionEnv.depth < 1024)),
      List.singleton_append] at hm'
    have hex := call_made (σ' := T.run.1) (g' := T.run.2.1) (A' := T.run.2.2.1)
      (z := T.run.2.2.2.1) (o := T.run.2.2.2.2) (retPtr := rp) (retLen := rl) hf hperm
      (by rw [← hw.accounts]; exact h5) (by rw [hcall])
    rw [hcall] at hex
    have hb : ¬ (v > (σ.get? I.codeOwner).elim ⟨0⟩ (·.balance)) := by
      have := h5.1
      cases hc : σ.get? I.codeOwner <;> simp only [hc, Option.option, Option.elim] at this ⊢ <;>
        exact fun hlt => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this hlt)
    have hdep : (I.depth == 1024) = false := beq_eq_false_iff_ne.mpr (ne_of_lt h5.2)
    simp only [hb, hdep, decide_false, Bool.or_false, Bool.not_eq_true', Bool.not_eq_false] at h6
    have hz : T.run.2.2.2.1 = _ := h6
    have hex' : (evRun .CALL [g, a, v, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some (if T.run.2.2.2.1 then ⟨1⟩ else ⟨0⟩), { w with
          accounts := T.run.1
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
          memory := T.run.2.2.2.2.write 0 w.memory rp.toNat (min rl (.ofNat T.run.2.2.2.2.size)).toNat
          returnData := T.run.2.2.2.2
          feed := f'
          calls := w.calls ++ [.theta T] })) := by
      simp only [evRun, Fe.M.exec_map, hI, hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, by rw [hz]; rfl, rfl, ?_, rfl, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]; rfl
    · show T.run.2.2.1.logSeries =
        w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
      rw [← hw.logs]
      exact Ethereum.EVM.Substates.theta_logs_extract ..
    · rw [← hM, hm']
      simp only [List.append_assoc, List.singleton_append]
      rfl

open Ethereum.EVM.Invariant in
/-- `STATICCALL` is the model's `staticcall`: out of gas or stack, or the message call without
    write permission made or not, on the feed's entry. -/
theorem staticcall_evMoves {s : State} {g a ap al rp rl : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, none))
    (hs : s.machineState.stack = g :: a :: ap :: al :: rp :: rl :: t) :
    EvMoves s .STATICCALL [g, a, ap, al, rp, rl] t := by
  rcases s with ⟨σ, σ₀, tg, tr, A, I, ⟨pc, stk, el, ga, aw, mem, rd, hr⟩⟩
  simp only at hs
  subst hs
  intro M w hw
  have h := step_staticcall _ hdec
  simp only at h
  set S : State := ⟨σ, σ₀, tg, tr, A, I, ⟨pc, g :: a :: ap :: al :: rp :: rl :: t, el, ga, aw,
    mem, rd, hr⟩⟩ with hSd
  have hI : S.executionEnv = I := rfl
  have hq : supplyOf S = [⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 a) ⟨0⟩ g σ
      (callState S .STATICCALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
      σ₀⟩] := by
    unfold supplyOf; rw [hdec]
  have hmd : ∀ r, Xstep (D_J S.executionEnv.code 0) S = .ok r →
      madeOf S = callMade g (.ofNat I.codeOwner) a a ⟨0⟩ ⟨0⟩ ap al false
        (callState S .STATICCALL) := by
    intro r hx
    obtain ⟨c, hz⟩ := Z_of_Xstep hx
    unfold madeOf
    rw [hdec] at hz ⊢
    simp only [Option.getD_some] at hz ⊢
    rw [hz]
    rfl
  split_ifs at h with h1 h2 h3 h5 h6
  · exact .inl h
  · exact .inl h
  · exact .inr (.inl h)
  all_goals
    obtain ⟨m, hF, hM⟩ := hw.fut
    obtain ⟨f', m', hf, hm', hF'⟩ := hF.next h
    rw [hq, List.singleton_append] at hf
  rotate_left 2
  · rw [hmd _ h, callMade, if_neg (by exact h5 : ¬ ((⟨0⟩ : UInt256) ≤
      ((callState S .STATICCALL).accountMap.get? (callState S .STATICCALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .STATICCALL).executionEnv.depth < 1024)),
      List.nil_append] at hm'
    have hex := message_notMade (I := I) (source := I.codeOwner) (recipient := .ofUInt256 a)
      (t := .ofUInt256 a) (value := ⟨0⟩) (value' := ⟨0⟩) (perm := false) (retPtr := rp)
      (retLen := rl) (argsPtr := ap) (argsLen := al) (gasArg := g) hf
      (by rw [← hw.accounts]; exact h5)
    have hex' : (evRun .STATICCALL [g, a, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some ⟨0⟩, { w with
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate
            (S.addAccessedAccount (.ofUInt256 a)).substate
          memory := ByteArray.empty.write 0 w.memory rp.toNat
            (min rl (.ofNat ByteArray.empty.size)).toNat
          returnData := ByteArray.empty
          feed := f' })) := by
      simp only [evRun, Fe.M.exec_map, Fe.EVM.staticcall, Fe.M.exec_bind, Fe.M.exec_read, hI]
      rw [hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, rfl, rfl, ?_, hw.accounts, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]
    · rw [appended_self, Array.append_empty, ← hw.logs]; rfl
    · rw [← hM, hm']
  · rename_i hx
    exact absurd (by simp) hx
  all_goals
    have hcall : messageCall I w ⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 a) ⟨0⟩ g σ
        (callState S .STATICCALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
        σ₀⟩ g I.codeOwner (.ofUInt256 a) (.ofUInt256 a) ⟨0⟩ ⟨0⟩ ap al false =
        callArgs g (.ofNat I.codeOwner) a a ⟨0⟩ ⟨0⟩ ap al false (callState S .STATICCALL) := by
      unfold messageCall callArgs
      rw [← hw.accounts, ← hw.memory, AccountAddress.ofUInt256_ofNat, forwardedGas_Cgascap]
      rfl
    set T := callArgs g (.ofNat I.codeOwner) a a ⟨0⟩ ⟨0⟩ ap al false (callState S .STATICCALL)
      with hT
    rw [hmd _ h, callMade, if_pos (by exact h5 : (⟨0⟩ : UInt256) ≤
      ((callState S .STATICCALL).accountMap.get? (callState S .STATICCALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .STATICCALL).executionEnv.depth < 1024),
      List.singleton_append] at hm'
    have hΘ : (T.run.1, T.run.2.1, T.run.2.2.1, T.run.2.2.2.1, T.run.2.2.2.2) =
        (messageCall I w ⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 a) ⟨0⟩ g σ
          (callState S .STATICCALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
          σ₀⟩ g I.codeOwner (.ofUInt256 a) (.ofUInt256 a) ⟨0⟩ ⟨0⟩ ap al false).run := by
      rw [hcall]
    have hex := message_made (I := I) (source := I.codeOwner) (recipient := .ofUInt256 a)
      (t := .ofUInt256 a) (value := ⟨0⟩) (value' := ⟨0⟩) (perm := false) (gasArg := g)
      (argsPtr := ap) (argsLen := al) (retPtr := rp) (retLen := rl) hf
      (by rw [← hw.accounts]; exact h5) hΘ
    rw [hcall] at hex
    have hb : ¬ ((⟨0⟩ : UInt256) > (σ.get? I.codeOwner).elim ⟨0⟩ (·.balance)) := by
      have := h5.1
      cases hc : σ.get? I.codeOwner <;> simp only [hc, Option.option, Option.elim] at this ⊢ <;>
        exact fun hlt => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this hlt)
    have hdep : (I.depth == 1024) = false := beq_eq_false_iff_ne.mpr (ne_of_lt h5.2)
    simp only [hb, hdep, decide_false, Bool.or_false, Bool.not_eq_true', Bool.not_eq_false] at h6
    have hz : T.run.2.2.2.1 = _ := h6
    have hex' : (evRun .STATICCALL [g, a, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some (if T.run.2.2.2.1 then ⟨1⟩ else ⟨0⟩), { w with
          accounts := T.run.1
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
          memory := T.run.2.2.2.2.write 0 w.memory rp.toNat (min rl (.ofNat T.run.2.2.2.2.size)).toNat
          returnData := T.run.2.2.2.2
          feed := f'
          calls := w.calls ++ [.theta T] })) := by
      simp only [evRun, Fe.M.exec_map, Fe.EVM.staticcall, Fe.M.exec_bind, Fe.M.exec_read, hI]
      rw [hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, by rw [hz]; rfl, rfl, ?_, rfl, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]; rfl
    · show T.run.2.2.1.logSeries =
        w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
      rw [← hw.logs]
      exact Ethereum.EVM.Substates.theta_logs_extract ..
    · rw [← hM, hm']
      simp only [List.append_assoc, List.singleton_append]
      rfl

open Ethereum.EVM.Invariant in
/-- `DELEGATECALL` is the model's `delegatecall`: out of gas or stack, or the message call that
    runs the callee's code as this contract, for its caller and value, made or not. -/
theorem delegatecall_evMoves {s : State} {g a ap al rp rl : UInt256} {t : List UInt256}
    (hdec : decode s.executionEnv.code s.machineState.pc = some (.DELEGATECALL, none))
    (hs : s.machineState.stack = g :: a :: ap :: al :: rp :: rl :: t) :
    EvMoves s .DELEGATECALL [g, a, ap, al, rp, rl] t := by
  rcases s with ⟨σ, σ₀, tg, tr, A, I, ⟨pc, stk, el, ga, aw, mem, rd, hr⟩⟩
  simp only at hs
  subst hs
  intro M w hw
  have h := step_delegatecall _ hdec
  simp only at h
  set S : State := ⟨σ, σ₀, tg, tr, A, I, ⟨pc, g :: a :: ap :: al :: rp :: rl :: t, el, ga, aw,
    mem, rd, hr⟩⟩ with hSd
  have hI : S.executionEnv = I := rfl
  have hq : supplyOf S = [⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 (.ofNat I.codeOwner)) ⟨0⟩ g σ
      (callState S .DELEGATECALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
      σ₀⟩] := by
    unfold supplyOf; rw [hdec]
  have hmd : ∀ r, Xstep (D_J S.executionEnv.code 0) S = .ok r →
      madeOf S = callMade g (.ofNat I.source) (.ofNat I.codeOwner) a ⟨0⟩ I.weiValue ap al I.perm
        (callState S .DELEGATECALL) := by
    intro r hx
    obtain ⟨c, hz⟩ := Z_of_Xstep hx
    unfold madeOf
    rw [hdec] at hz ⊢
    simp only [Option.getD_some] at hz ⊢
    rw [hz]
    rfl
  split_ifs at h with h1 h2 h3 h5 h6
  · exact .inl h
  · exact .inl h
  · exact .inr (.inl h)
  all_goals
    obtain ⟨m, hF, hM⟩ := hw.fut
    obtain ⟨f', m', hf, hm', hF'⟩ := hF.next h
    rw [hq, List.singleton_append] at hf
  rotate_left 2
  · rw [hmd _ h, callMade, if_neg (by exact h5 : ¬ ((⟨0⟩ : UInt256) ≤
      ((callState S .DELEGATECALL).accountMap.get? (callState S .DELEGATECALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .DELEGATECALL).executionEnv.depth < 1024)),
      List.nil_append] at hm'
    have hex := message_notMade (I := I) (source := I.source) (recipient := I.codeOwner)
      (t := .ofUInt256 a) (value := ⟨0⟩) (value' := I.weiValue) (perm := I.perm) (retPtr := rp)
      (retLen := rl) (argsPtr := ap) (argsLen := al) (gasArg := g) hf
      (by rw [← hw.accounts]; exact h5)
    have hex' : (evRun .DELEGATECALL [g, a, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some ⟨0⟩, { w with
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate
            (S.addAccessedAccount (.ofUInt256 a)).substate
          memory := ByteArray.empty.write 0 w.memory rp.toNat
            (min rl (.ofNat ByteArray.empty.size)).toNat
          returnData := ByteArray.empty
          feed := f' })) := by
      simp only [evRun, Fe.M.exec_map, Fe.EVM.delegatecall, Fe.M.exec_bind, Fe.M.exec_read, hI]
      rw [hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, rfl, rfl, ?_, hw.accounts, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]
    · rw [appended_self, Array.append_empty, ← hw.logs]; rfl
    · rw [← hM, hm']
  · rename_i hx
    exact absurd (by simp) hx
  all_goals
    have hcall : messageCall I w ⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 (.ofNat I.codeOwner)) ⟨0⟩ g σ
        (callState S .DELEGATECALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
        σ₀⟩ g I.source I.codeOwner (.ofUInt256 a) ⟨0⟩ I.weiValue ap al I.perm =
        callArgs g (.ofNat I.source) (.ofNat I.codeOwner) a ⟨0⟩ I.weiValue ap al I.perm (callState S .DELEGATECALL) := by
      unfold messageCall callArgs
      rw [← hw.accounts, ← hw.memory, AccountAddress.ofUInt256_ofNat I.source,
        AccountAddress.ofUInt256_ofNat I.codeOwner, forwardedGas_Cgascap]
      rfl
    set T := callArgs g (.ofNat I.source) (.ofNat I.codeOwner) a ⟨0⟩ I.weiValue ap al I.perm (callState S .DELEGATECALL)
      with hT
    rw [hmd _ h, callMade, if_pos (by exact h5 : (⟨0⟩ : UInt256) ≤
      ((callState S .DELEGATECALL).accountMap.get? (callState S .DELEGATECALL).executionEnv.codeOwner
        |>.option ⟨0⟩ (·.balance)) ∧ (callState S .DELEGATECALL).executionEnv.depth < 1024),
      List.singleton_append] at hm'
    have hΘ : (T.run.1, T.run.2.1, T.run.2.2.1, T.run.2.2.2.1, T.run.2.2.2.2) =
        (messageCall I w ⟨.ofNat (Cgascap (.ofUInt256 a) (.ofUInt256 (.ofNat I.codeOwner)) ⟨0⟩ g σ
          (callState S .DELEGATECALL).machineState A), (S.addAccessedAccount (.ofUInt256 a)).substate,
          σ₀⟩ g I.source I.codeOwner (.ofUInt256 a) ⟨0⟩ I.weiValue ap al I.perm).run := by
      rw [hcall]
    have hex := message_made (I := I) (source := I.source) (recipient := I.codeOwner)
      (t := .ofUInt256 a) (value := ⟨0⟩) (value' := I.weiValue) (perm := I.perm) (gasArg := g)
      (argsPtr := ap) (argsLen := al) (retPtr := rp) (retLen := rl) hf
      (by rw [← hw.accounts]; exact h5) hΘ
    rw [hcall] at hex
    have hb : ¬ ((⟨0⟩ : UInt256) > (σ.get? I.codeOwner).elim ⟨0⟩ (·.balance)) := by
      have := h5.1
      cases hc : σ.get? I.codeOwner <;> simp only [hc, Option.option, Option.elim] at this ⊢ <;>
        exact fun hlt => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this hlt)
    have hdep : (I.depth == 1024) = false := beq_eq_false_iff_ne.mpr (ne_of_lt h5.2)
    simp only [hb, hdep, decide_false, Bool.or_false, Bool.not_eq_true', Bool.not_eq_false] at h6
    have hz : T.run.2.2.2.1 = _ := h6
    have hex' : (evRun .DELEGATECALL [g, a, ap, al, rp, rl]).exec S.executionEnv w =
        some (.ok (some (if T.run.2.2.2.1 then ⟨1⟩ else ⟨0⟩), { w with
          accounts := T.run.1
          logs := w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
          memory := T.run.2.2.2.2.write 0 w.memory rp.toNat (min rl (.ofNat T.run.2.2.2.2.size)).toNat
          returnData := T.run.2.2.2.2
          feed := f'
          calls := w.calls ++ [.theta T] })) := by
      simp only [evRun, Fe.M.exec_map, Fe.EVM.delegatecall, Fe.M.exec_bind, Fe.M.exec_read, hI]
      rw [hex]
    refine .inr (.inr (.inr ⟨_, _, _, hex', h, rfl, by rw [hz]; rfl, rfl, ?_, rfl, ?_, rfl,
      ⟨m', hF', ?_⟩⟩))
    · rw [← hw.memory]; rfl
    · show T.run.2.2.1.logSeries =
        w.logs ++ appended (S.addAccessedAccount (.ofUInt256 a)).substate T.run.2.2.1
      rw [← hw.logs]
      exact Ethereum.EVM.Substates.theta_logs_extract ..
    · rw [← hM, hm']
      simp only [List.append_assoc, List.singleton_append]
      rfl

/-- An event's opcode, its operands on top, steps as `EvMoves` says. -/
theorem event_evMoves {s : State} {op : Operation} {args t : List UInt256}
    (hp : (readOps.contains op || writeOps.contains op) = true)
    (hdec : decode s.executionEnv.code s.machineState.pc = some (op, none))
    (hs : s.machineState.stack = args ++ t) (hk : δ op = some args.length) :
    EvMoves s op args t := by
  simp only [readOps, writeOps, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨g, _ | ⟨i, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩
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
  · exact call_evMoves hdec hs
  · exact staticcall_evMoves hdec hs
  · exact delegatecall_evMoves hdec hs
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
