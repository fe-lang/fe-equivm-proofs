import Ethereum.Semantics

/-!
# The calls a frame makes

Over EVMLean alone (no other `Fe` module).  `ThetaCall` and `LambdaCall` are the inputs of a
message call `Θ` and of a creation `Lambda`.  `XiOk Q σ σ₀ g A I` says that every message call
and creation the frame `Ξ σ σ₀ g A I` makes directly satisfies the condition `Q`: it reads them
off the instructions the frame executes, with the arguments `call` and `create` compute.

`Fe.EVM.Invariant` uses these to say which executions an invariant is shown for.
-/

namespace Ethereum.EVM.Invariant

/-- The inputs of a message call `Θ`. -/
structure ThetaCall where
  σ : AccountMap
  σ₀ : AccountMap
  A : Substate
  s : AccountAddress
  o : AccountAddress
  r : AccountAddress
  c : ToExecute
  g : UInt256
  p : UInt256
  v : UInt256
  v' : UInt256
  d : ByteArray
  e : Fin 1025
  H : BlockHeader
  bvh : List ByteArray
  blocks : ProcessedBlocks
  w : Bool

/-- The message call. -/
def ThetaCall.run (T : ThetaCall) : AccountMap × UInt256 × Substate × Bool × ByteArray :=
  Θ T.σ T.σ₀ T.A T.s T.o T.r T.c T.g T.p T.v T.v' T.d T.e T.H T.bvh T.blocks T.w

/-- The inputs of a creation `Lambda`. -/
structure LambdaCall where
  σ : AccountMap
  σ₀ : AccountMap
  A : Substate
  s : AccountAddress
  o : AccountAddress
  g : UInt256
  p : UInt256
  v : UInt256
  i : ByteArray
  e : Fin 1025
  ζ : Option ByteArray
  H : BlockHeader
  bvh : List ByteArray
  blocks : ProcessedBlocks
  w : Bool

/-- The creation. -/
def LambdaCall.run (L : LambdaCall) :
    AccountAddress × AccountMap × UInt256 × Substate × Bool × ByteArray :=
  Lambda L.σ L.σ₀ L.A L.s L.o L.g L.p L.v L.i L.e L.ζ L.H L.bvh L.blocks L.w

/-- A condition on the message calls and on the creations a frame makes. -/
structure CallPreds where
  theta : ThetaCall → Prop
  lambda : LambdaCall → Prop

/-- No condition. -/
def CallPreds.all : CallPreds := ⟨fun _ => True, fun _ => True⟩

/-- The message call that `call` makes, when it makes one. -/
def callArgs (gas source recipient t value value' inOffset inSize : UInt256) (permission : Bool)
    (evmState : State) : ThetaCall where
  σ := evmState.accountMap
  σ₀ := evmState.σ₀
  A := (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
  s := AccountAddress.ofUInt256 source
  o := evmState.executionEnv.sender
  r := AccountAddress.ofUInt256 recipient
  c := toExecute evmState.accountMap (AccountAddress.ofUInt256 t)
  g := .ofNat (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value
    gas evmState.accountMap evmState.machineState evmState.substate)
  p := .ofNat evmState.executionEnv.gasPrice
  v := value
  v' := value'
  d := evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
  e := evmState.executionEnv.depth + 1
  H := evmState.executionEnv.header
  bvh := evmState.executionEnv.blobVersionedHashes
  blocks := evmState.executionEnv.blocks
  w := permission

/-- The message call `call` makes, if it makes one, satisfies `Q`. -/
def callOk (Q : CallPreds) (gas source recipient t value value' inOffset inSize : UInt256)
    (permission : Bool) (evmState : State) : Prop :=
  value ≤ (evmState.accountMap.get? evmState.executionEnv.codeOwner
      |>.option ⟨0⟩ (·.balance)) ∧ evmState.executionEnv.depth < 1024 →
    Q.theta (callArgs gas source recipient t value value' inOffset inSize permission evmState)

/-- The creation `create` makes, if it makes one, satisfies `Q`. -/
def createOk (Q : CallPreds) (value offset size : UInt256) (salt : Option ByteArray)
    (evmState : State) : Prop :=
  let i := evmState.machineState.memory.readWithPadding offset.toNat size.toNat
  let I := evmState.executionEnv
  let σ := evmState.accountMap
  let self : Account := σ.get? I.codeOwner |>.getD default
  ¬ self.nonce.toNat ≥ 2 ^ 64 - 1 →
  ∀ h : value ≤ (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
    ∧ i.size ≤ 49152,
    Q.lambda
      { σ := σ.insert I.codeOwner {self with nonce := self.nonce + ⟨1⟩}
        σ₀ := evmState.σ₀, A := evmState.substate, s := I.codeOwner, o := I.sender
        g := .ofNat (L evmState.machineState.gasAvailable.toNat), p := .ofNat I.gasPrice
        v := value, i := i, e := ⟨I.depth.val + 1, Nat.succ_lt_succ h.2.1⟩, ζ := salt
        H := I.header, bvh := I.blobVersionedHashes, blocks := I.blocks, w := I.perm }

/-- The message call or creation one instruction makes, if any, satisfies `Q`. -/
def stepOk (Q : CallPreds) (gasCost : ℕ) (instr : Operation × Option (UInt256 × Nat))
    (state : State) : Prop :=
  let st : State := { state with machineState.execLength := state.machineState.execLength + 1 }
  let charged : State :=
    { st with machineState.gasAvailable := st.machineState.gasAvailable.subNat gasCost }
  match instr.1 with
  | .CREATE => ∀ stack value offset size,
      st.machineState.stack.pop3 = some (stack, value, offset, size) →
      createOk Q value offset size none charged
  | .CREATE2 => ∀ stack value offset size salt,
      st.machineState.stack.pop4 = some (stack, value, offset, size, salt) →
      createOk Q value offset size (some salt.toByteArray) charged
  | .CALL => ∀ stack μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆,
      st.machineState.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) →
      callOk Q μ₀ (.ofNat state.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄
        state.executionEnv.perm st
  | .CALLCODE => ∀ stack μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆,
      st.machineState.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) →
      callOk Q μ₀ (.ofNat state.executionEnv.codeOwner) (.ofNat state.executionEnv.codeOwner)
        μ₁ μ₂ μ₂ μ₃ μ₄ state.executionEnv.perm st
  | .DELEGATECALL => ∀ stack μ₀ μ₁ μ₃ μ₄ μ₅ μ₆,
      st.machineState.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) →
      callOk Q μ₀ (.ofNat state.executionEnv.source) (.ofNat state.executionEnv.codeOwner) μ₁
        ⟨0⟩ state.executionEnv.weiValue μ₃ μ₄ state.executionEnv.perm st
  | .STATICCALL => ∀ stack μ₀ μ₁ μ₃ μ₄ μ₅ μ₆,
      st.machineState.stack.pop6 = some (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) →
      callOk Q μ₀ (.ofNat state.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ false st
  | _ => True

/-- The next instruction's call or creation, if any, satisfies `Q`. -/
def XstepOk (Q : CallPreds) (validJumps : Array UInt256) (state : State) : Prop :=
  ∀ stateZ cost, Z validJumps (decode state.executionEnv.code state.machineState.pc |>.getD
      (.STOP, .none)).1 state = .ok (stateZ, cost) →
    stepOk Q cost (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none))
      { stateZ with executionEnv.depth := state.executionEnv.depth }

/-- Every call and creation the loop `X` makes from `state` satisfies `Q`. -/
def XOk (Q : CallPreds) : ℕ → Array UInt256 → State → Prop
  | 0, _, _ => True
  | f + 1, validJumps, state => XstepOk Q validJumps state ∧
      ∀ state', Xstep validJumps state = .ok (state', none) →
        XOk Q f validJumps { state' with executionEnv.depth := state.executionEnv.depth }

/-- The state `Ξ` starts from. -/
def xiState (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) : State :=
  { (default : State) with
    accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
    machineState.gasAvailable := .ofUInt256 g }

/-- Every message call and creation the frame `Ξ σ σ₀ g A I` makes directly satisfies `Q`. -/
def XiOk (Q : CallPreds) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Prop :=
  XOk Q (g.toNat + 1) (D_J I.code 0) (xiState σ σ₀ g A I)

theorem stepOk_of_all {Q : CallPreds} (hθ : ∀ T, Q.theta T) (hl : ∀ L, Q.lambda L)
    (gasCost : ℕ) (instr : Operation × Option (UInt256 × Nat)) (state : State) :
    stepOk Q gasCost instr state := by
  unfold stepOk
  split <;> simp [callOk, createOk, hθ, hl]

theorem XiOk_of_all {Q : CallPreds} (hθ : ∀ T, Q.theta T) (hl : ∀ L, Q.lambda L)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    XiOk Q σ σ₀ g A I := by
  unfold XiOk
  generalize g.toNat + 1 = f
  generalize xiState σ σ₀ g A I = state
  induction f generalizing state with
  | zero => trivial
  | succ f ih => exact ⟨fun _ _ _ => stepOk_of_all hθ hl _ _ _, fun _ _ => ih _⟩

end Ethereum.EVM.Invariant
