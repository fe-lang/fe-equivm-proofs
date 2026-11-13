import Ethereum.Theory.StaticStorage
import Ethereum.Theory.ReturnDataBound

namespace Ethereum.EVM.Invariant

variable (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)

/-- `a`'s account exists and satisfies `P`. -/
def Holds (σ : AccountMap) : Prop := ∃ acc, σ[a]? = some acc ∧ P acc

/-- The code a message call runs is one `Trusted` admits, or a precompile. -/
def CodeOk : ToExecute → Prop
  | .Precompiled _ => True
  | .Code d => Trusted d

/-- The balance `s` pays before a creation runs, as `Lambda` takes it. -/
def debit (σ : AccountMap) (s : AccountAddress) (v : UInt256) : AccountMap :=
  match σ.get? s with
  | none => σ
  | some ac => σ.insert s {ac with balance := ac.balance - v}

/-- Every message call at depth `e` keeps `Holds`, if it starts from a state where it holds both
    before and after the value moves, has calldata that fits a word, and runs `Trusted` code when
    its recipient is `a`. -/
def ThetaGood (e : Fin 1025) : Prop :=
  ∀ σ σ₀ A s o r c g p v v' d H bvh blocks w,
    d.size < UInt256.size → (r = a → CodeOk Trusted c) →
    Holds a P σ → Holds a P (sendEth r s v true σ) →
    Holds a P (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).1

/-- Every creation at depth `e` keeps `Holds`, if it holds before and after the creator pays. -/
def LambdaGood (e : Fin 1025) : Prop :=
  ∀ σ σ₀ A s o g p v i ζ H bvh blocks w,
    Holds a P σ → Holds a P (debit σ s v) →
    Holds a P (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.1

/-- Every message call and creation deeper than `d` keeps `Holds`. -/
def Deeper (d : Fin 1025) : Prop :=
  ∀ e : Fin 1025, d < e → ThetaGood a P Trusted e ∧ LambdaGood a P e

/-- The per-frame hypothesis: a frame at `a` running code that `Trusted` admits keeps `Holds`,
    provided the message calls and creations it makes do. -/
def FrameHyp : Prop :=
  ∀ σ σ₀ g A (I : ExecutionEnv) σ' g' A' o, I.codeOwner = a → Trusted I.code →
    I.calldata.size < UInt256.size → Deeper a P Trusted I.depth →
    Holds a P σ → Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o) → Holds a P σ'

/-- What `P` must allow. -/
structure Admissible : Prop where
  /-- Value can arrive without a call: by a transfer, a `SELFDESTRUCT`, a block reward. -/
  balance : ∀ acc v, P acc → P {acc with balance := acc.balance + v}
  /-- `a` has code, so no creation can land on it. -/
  code : ∀ acc, P acc → acc.code.size ≠ 0
  /-- A message call to `a` runs code that `Trusted` admits. -/
  trusted : ∀ acc, P acc → Trusted acc.code

variable {a P Trusted}

theorem Holds.insert_ne {σ : AccountMap} {k : AccountAddress} {x : Account} (hk : k ≠ a)
    (h : Holds a P σ) : Holds a P (σ.insert k x) := by
  obtain ⟨acc, hacc, hP⟩ := h
  refine ⟨acc, ?_, hP⟩
  rw [Std.ExtTreeMap.getElem?_insert]
  simp [Std.LawfulEqCmp.compare_eq_iff_eq, hk, hacc]

theorem Holds.insert_self {σ : AccountMap} {x : Account} (hx : P x) :
    Holds a P (σ.insert a x) :=
  ⟨x, by simp, hx⟩

theorem Holds.get {σ : AccountMap} (h : Holds a P σ) : ∃ acc, σ.get? a = some acc ∧ P acc := by
  simpa [Std.ExtTreeMap.get?_eq_getElem?] using h

theorem UInt256.sub_zero' (x : UInt256) : x - ⟨0⟩ = x := by
  cases x
  show UInt256.mk _ = _
  simp

theorem Holds.sendEth (hadm : Admissible P Trusted) {σ : AccountMap} {r s : AccountAddress}
    {v : UInt256} (hs : s ≠ a ∨ v = ⟨0⟩) (h : Holds a P σ) :
    Holds a P (sendEth r s v true σ) := by
  have h1 : Holds a P (match σ.get? r with
      | none =>
        if (v != UInt256.ofNat 0) = true then
          σ.insert r
            { nonce := (default : Account).nonce, balance := v,
              storage := (default : Account).storage, code := (default : Account).code,
              tstorage := (default : Account).tstorage }
        else σ
      | some acc =>
        σ.insert r
          { nonce := acc.nonce, balance := acc.balance + v, storage := acc.storage,
            code := acc.code, tstorage := acc.tstorage }) := by
    obtain ⟨acc, hacc, hP⟩ := h
    split
    · rename_i hr
      have hra : r ≠ a := by
        rintro rfl
        simp [Std.ExtTreeMap.get?_eq_getElem?, hacc] at hr
      split
      · exact Holds.insert_ne hra ⟨acc, hacc, hP⟩
      · exact ⟨acc, hacc, hP⟩
    · rename_i accr hr
      by_cases hra : r = a
      · subst hra
        have : accr = acc := by
          simpa [Std.ExtTreeMap.get?_eq_getElem?, hacc] using hr.symm
        subst this
        exact Holds.insert_self (hadm.balance _ v hP)
      · exact Holds.insert_ne hra ⟨acc, hacc, hP⟩
  have h2 : ∀ τ : AccountMap, Holds a P τ → Holds a P (match τ.get? s with
      | none => τ
      | some acc =>
        τ.insert s
          { nonce := acc.nonce, balance := acc.balance - v, storage := acc.storage,
            code := acc.code, tstorage := acc.tstorage }) := by
    intro τ hτ
    split
    · exact hτ
    · rename_i accs hs'
      by_cases hsa : s = a
      · subst hsa
        have hv : v = ⟨0⟩ := hs.resolve_left (fun h => h rfl)
        subst hv
        obtain ⟨acc, hacc, hP⟩ := hτ
        have : accs = acc := by
          simpa [Std.ExtTreeMap.get?_eq_getElem?, hacc] using hs'.symm
        subst this
        refine Holds.insert_self ?_
        simpa [UInt256.sub_zero'] using hP
      · exact Holds.insert_ne hsa hτ
  exact h2 _ h1

theorem Holds.of_eq {σ τ : AccountMap} (h : Holds a P σ) (he : τ = σ) : Holds a P τ := he ▸ h

theorem sstore_accountMap (state : State) (k v : UInt256) :
    (state.sstore k v).accountMap = state.accountMap ∨
      ∃ x, (state.sstore k v).accountMap = state.accountMap.insert state.executionEnv.codeOwner x := by
  unfold Ethereum.State.sstore
  simp only [Ethereum.State.lookupAccount]
  generalize state.accountMap.get? state.executionEnv.codeOwner = o
  cases o with
  | none => exact Or.inl rfl
  | some acc => exact Or.inr ⟨acc.updateStorage k v, rfl⟩

theorem tstore_accountMap (state : State) (k v : UInt256) :
    (state.tstore k v).accountMap = state.accountMap ∨
      ∃ x, (state.tstore k v).accountMap = state.accountMap.insert state.executionEnv.codeOwner x := by
  unfold Ethereum.State.tstore
  simp only [Ethereum.State.lookupAccount]
  generalize state.accountMap.get? state.executionEnv.codeOwner = o
  cases o with
  | none => exact Or.inl rfl
  | some acc => exact Or.inr ⟨acc.updateTransientStorage k v, rfl⟩

/-- A stack, memory, storage or control-flow instruction of a frame at another address keeps
    `Holds`: only `SSTORE` and `TSTORE` touch the account map, and only at the frame's owner. -/
theorem step_stackMemFlow {op : Operation.SMSFOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (howner : state.executionEnv.codeOwner ≠ a) (hH : Holds a P state.accountMap)
    (h : step gasCost (.StackMemFlow op, arg) state = .ok state') :
    Holds a P state'.accountMap := by
  have hstore : ∀ {f : State → UInt256 → UInt256 → State},
      (∀ st k v, (f st k v).accountMap = st.accountMap ∨
        ∃ x, (f st k v).accountMap = st.accountMap.insert st.executionEnv.codeOwner x) →
      ∀ {st st' : State}, st.accountMap = state.accountMap →
        st.executionEnv.codeOwner = state.executionEnv.codeOwner →
        binaryStateOp f st = .ok st' → Holds a P st'.accountMap := by
    intro f hf st st' hσ hown hop
    unfold binaryStateOp at hop
    split at hop <;> try contradiction
    rename_i k v _
    injection hop with hst
    subst hst
    simp only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    rcases hf st k v with he | ⟨x, he⟩
    · exact hH.of_eq (he.trans hσ)
    · rw [he, hσ, hown]
      exact hH.insert_ne howner
  cases op <;> simp [step] at h
  all_goals first
    | exact hH.of_eq (by simpa using static_binaryMachineStateOp_accountMap_eq h)
    | exact hH.of_eq (by simpa using static_machineStateOp_accountMap_eq h)
    | exact hH.of_eq (by simpa using static_ternaryMachineStateOp_accountMap_eq h)
    | (have he := static_unaryStateOp_accountMap_eq (f := Ethereum.State.sload)
          (by intro s v; simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
            Ethereum.State.lookupAccount]) h
       exact hH.of_eq (by simpa using he))
    | (have he := static_unaryStateOp_accountMap_eq (f := Ethereum.State.tload)
          (by intro s v; simp [Ethereum.State.tload]) h
       exact hH.of_eq (by simpa using he))
    | exact hstore sstore_accountMap (by simp) (by simp) h
    | exact hstore tstore_accountMap (by simp) (by simp) h
    | (rw [← h]; exact hH)
    | (split at h <;> try contradiction
       injection h with hst
       rw [← hst]
       exact hH)

theorem readWithPadding_size_lt (mem : ByteArray) (o l : UInt256) :
    (mem.readWithPadding o.toNat l.toNat).size < UInt256.size :=
  Nat.lt_of_le_of_lt (ByteArray.readWithPadding_size_le mem o.toNat l.toNat) l.val.isLt

theorem lt_succ_depth {e : Fin 1025} (h : e < 1024) : e < e + 1 := by
  have hv : e.val < 1024 := by simpa using h
  rw [Fin.lt_def, Fin.val_add_eq_of_add_lt] <;> simp; omega

/-- A `CALL`-family instruction keeps `Holds` when the message call it makes is one
    `ThetaGood` covers. -/
theorem call_holds {gasCost : Nat}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdeep : Deeper a P Trusted evmState.executionEnv.depth)
    (hH : Holds a P evmState.accountMap)
    (hcode : AccountAddress.ofUInt256 recipient = a →
      CodeOk Trusted (toExecute evmState.accountMap (AccountAddress.ofUInt256 t)))
    (hpre : Holds a P (sendEth (AccountAddress.ofUInt256 recipient)
      (AccountAddress.ofUInt256 source) value true evmState.accountMap))
    (h : call gasCost gas source recipient t value value' inOffset inSize outOffset outSize
      permission evmState = .ok (x, state')) :
    Holds a P state'.accountMap := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp only
    exact (hdeep _ (lt_succ_depth hcall.2)).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (readWithPadding_size_lt _ _ _) hcode hH hpre
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    exact hH

theorem Holds.debit_ne {σ : AccountMap} {s : AccountAddress} {v : UInt256} (hs : s ≠ a)
    (h : Holds a P σ) : Holds a P (debit σ s v) := by
  unfold debit
  split
  · exact h
  · exact h.insert_ne hs

/-- A `CREATE` or `CREATE2` of a frame at another address keeps `Holds` when the creation it makes
    is one `LambdaGood` covers. -/
theorem create_holds {value offset size x : UInt256} {salt : Option ByteArray}
    {evmState state' : State}
    (howner : evmState.executionEnv.codeOwner ≠ a)
    (hdeep : Deeper a P Trusted evmState.executionEnv.depth)
    (hH : Holds a P evmState.accountMap)
    (h : create value offset size salt evmState = .ok (x, state')) :
    Holds a P state'.accountMap := by
  let owner := (evmState.accountMap.get? evmState.executionEnv.codeOwner).getD default
  let σStar := evmState.accountMap.insert evmState.executionEnv.codeOwner
    {owner with nonce := owner.nonce + ⟨1⟩}
  have hStar : Holds a P σStar := hH.insert_ne howner
  unfold create at h
  by_cases hnonce : owner.nonce.toNat ≥ 2^64 - 1
  · simp [bind, Except.bind, pure, Except.pure] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      first
      | contradiction
      | rcases h with ⟨_, hstate⟩
        rw [← hstate]
        exact hH
  · by_cases hCreate :
        value ≤ (evmState.accountMap.get? evmState.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)) ∧ evmState.executionEnv.depth < 1024 ∧
          (evmState.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152
    · let e : Fin 1025 := ⟨evmState.executionEnv.depth.val + 1, Nat.succ_lt_succ hCreate.2.1⟩
      have hlt : evmState.executionEnv.depth < e := by
        rw [Fin.lt_def]
        exact Nat.lt_succ_self _
      have hrec := (hdeep e hlt).2 σStar evmState.σ₀ evmState.substate
          evmState.executionEnv.codeOwner evmState.executionEnv.sender
          (UInt256.ofNat (L evmState.machineState.gasAvailable.toNat))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value
          (evmState.machineState.memory.readWithPadding offset.toNat size.toNat)
          salt evmState.executionEnv.header
          evmState.executionEnv.blobVersionedHashes evmState.executionEnv.blocks
          evmState.executionEnv.perm hStar (hStar.debit_ne howner)
      simp [bind, Except.bind, pure, Except.pure] at h
      repeat' (split at h <;> try simp at h)
      all_goals
        first
        | contradiction
        | rcases h with ⟨_, hstate⟩
          rw [← hstate]
          first
          | exact hH
          | simpa [σStar, owner, e] using hrec
    · simp [bind, Except.bind, pure, Except.pure] at h
      repeat' (split at h <;> try simp at h)
      all_goals
        first
        | contradiction
        | rcases h with ⟨_, hstate⟩
          rw [← hstate]
          exact hH

theorem codeOk_toExecute (hadm : Admissible P Trusted) {σ : AccountMap} (h : Holds a P σ) :
    CodeOk Trusted (toExecute σ a) := by
  obtain ⟨acc, hacc, hP⟩ := h.get
  unfold toExecute
  split
  · trivial
  · simp only [Id.run, hacc]
    exact hadm.trusted acc hP

/-- What `SELFDESTRUCT` of a frame at another address does to the account map keeps `Holds`. -/
theorem Holds.selfdestruct (hadm : Admissible P Trusted) {σ : AccountMap}
    {r owner : AccountAddress} {tacc : Account} {b : UInt256} {y : Account} (howner : owner ≠ a)
    (hr : σ[r]? = some tacc) (h : Holds a P σ) :
    Holds a P ((σ.insert r {tacc with balance := tacc.balance + b}).insert owner y) := by
  refine Holds.insert_ne howner ?_
  by_cases hra : r = a
  · subst hra
    obtain ⟨acc, hacc, hP⟩ := h
    rw [hr] at hacc
    cases hacc
    exact Holds.insert_self (hadm.balance _ b hP)
  · exact h.insert_ne hra

/-- A system instruction of a frame at another address keeps `Holds` when the calls and creations
    it makes are ones `Deeper` covers. -/
theorem step_system (hadm : Admissible P Trusted) {op : Operation.SOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (howner : state.executionEnv.codeOwner ≠ a)
    (hdeep : Deeper a P Trusted state.executionEnv.depth)
    (hH : Holds a P state.accountMap)
    (h : step gasCost (.System op, arg) state = .ok state') :
    Holds a P state'.accountMap := by
  have hself : AccountAddress.ofUInt256 (UInt256.ofNat ↑state.executionEnv.codeOwner) ≠ a := by
    rw [AccountAddress.ofUInt256_ofNat]
    exact howner
  cases op
  · -- CREATE
    simp [step, bind, Except.bind] at h
    repeat (first | simp at h | split at h)
    rename_i _ _ _ _ vCreate hCreate
    rcases vCreate with ⟨_, createdState⟩
    rw [← h]
    show Holds a P createdState.accountMap
    exact (create_holds (h := hCreate)) howner hdeep hH
  · -- CALL
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P callState.accountMap
    refine (call_holds (h := hcall)) hdeep hH ?_ ?_
    · intro hr
      rw [hr]
      exact codeOk_toExecute hadm hH
    · rw [AccountAddress.ofUInt256_ofNat]
      exact hH.sendEth hadm (Or.inl howner)
  · -- CALLCODE
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P callState.accountMap
    refine (call_holds (h := hcall)) hdeep hH (fun hr => absurd hr hself) ?_
    rw [AccountAddress.ofUInt256_ofNat]
    exact hH.sendEth hadm (Or.inl howner)
  · -- RETURN
    simp [step] at h
    exact hH.of_eq (by simpa using static_binaryMachineStateOp_accountMap_eq h)
  · -- DELEGATECALL
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P callState.accountMap
    exact (call_holds (h := hcall)) hdeep hH (fun hr => absurd hr hself) (hH.sendEth hadm (Or.inr rfl))
  · -- CREATE2
    simp [step, bind, Except.bind] at h
    repeat (first | simp at h | split at h)
    rename_i _ _ _ _ vCreate hCreate
    rcases vCreate with ⟨_, createdState⟩
    rw [← h]
    show Holds a P createdState.accountMap
    exact (create_holds (h := hCreate)) howner hdeep hH
  · -- STATICCALL
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P callState.accountMap
    refine (call_holds (h := hcall)) hdeep hH ?_ (hH.sendEth hadm (Or.inr rfl))
    intro hr
    rw [hr]
    exact codeOk_toExecute hadm hH
  · -- REVERT
    simp [step] at h
    exact hH.of_eq (by simpa using static_binaryMachineStateOp_accountMap_eq h)
  · -- INVALID
    simp [step] at h
  · -- SELFDESTRUCT
    simp [step, Ethereum.State.lookupAccount] at h
    cases hpop : state.machineState.stack.pop with
    | none =>
        simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, targetWord⟩
        by_cases hcreated : state.executionEnv.codeOwner ∈ state.substate.createdAccounts
        all_goals
          cases howner' : state.accountMap[state.executionEnv.codeOwner]? with
          | none =>
              simp [hpop, hcreated, howner'] at h
              rw [← h]
              exact hH
          | some ownerAcc =>
              cases htarget : state.accountMap[AccountAddress.ofUInt256 targetWord]? with
              | none =>
                  have hta : AccountAddress.ofUInt256 targetWord ≠ a := by
                    rintro rfl
                    obtain ⟨_, hacc, _⟩ := hH
                    rw [htarget] at hacc
                    cases hacc
                  by_cases hzero : ownerAcc.balance = ({ val := 0 } : UInt256)
                  · simp [hpop, hcreated, howner', htarget, hzero] at h
                    rw [← h]
                    exact hH
                  · simp [hpop, hcreated, howner', htarget, hzero] at h
                    rw [← h]
                    exact (hH.insert_ne hta).insert_ne howner
              | some targetAcc =>
                  by_cases hsame : AccountAddress.ofUInt256 targetWord = state.executionEnv.codeOwner
                  · simp [hpop, hcreated, howner', hsame] at h
                    rw [← h]
                    first
                    | exact hH
                    | exact (hH.insert_ne howner).insert_ne howner
                  · simp [hpop, hcreated, howner', htarget, hsame] at h
                    rw [← h]
                    exact hH.selfdestruct hadm howner htarget

/-- One instruction of a frame at another address keeps `Holds` when the calls and creations it
    makes are ones `Deeper` covers. -/
theorem step_holds (hadm : Admissible P Trusted) {gasCost : Nat}
    {instr : Operation × Option (UInt256 × Nat)} {state state' : State}
    (howner : state.executionEnv.codeOwner ≠ a)
    (hdeep : Deeper a P Trusted state.executionEnv.depth)
    (hH : Holds a P state.accountMap)
    (h : step gasCost instr state = .ok state') :
    Holds a P state'.accountMap := by
  rcases instr with ⟨op, arg⟩
  cases op with
  | StopArith op => exact hH.of_eq (static_step_stoparith_accountMap_eq h)
  | CompBit op => exact hH.of_eq (static_step_compbit_accountMap_eq h)
  | Keccak op => exact hH.of_eq (static_step_keccak_accountMap_eq h)
  | Env op => exact hH.of_eq (static_step_env_accountMap_eq h)
  | Block op => exact hH.of_eq (static_step_block_accountMap_eq h)
  | StackMemFlow op => exact step_stackMemFlow howner hH h
  | Push op => exact hH.of_eq (static_step_push_accountMap_eq h)
  | Dup op => exact hH.of_eq (static_step_dup_accountMap_eq h)
  | Exchange op => exact hH.of_eq (static_step_exchange_accountMap_eq h)
  | Log op => exact hH.of_eq (static_step_log_accountMap_eq h)
  | System op => exact step_system hadm howner hdeep hH h

theorem Xstep_executionEnv_eq {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hstep : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv = state.executionEnv := by
  have h := hstep
  simp [Xstep] at h
  split at h
  · contradiction
  · split at h
    · simp [bind, Except.bind] at h
      split at h
      · contradiction
      · split at h <;>
          (simp at h
           simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm)
    · simp [bind, Except.bind] at h
      split at h
      · contradiction
      · split at h
        · simp at h
          simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm
        · split at h <;>
            (simp at h
             simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm)

theorem Xstep_holds (hadm : Admissible P Trusted) {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (howner : state.executionEnv.codeOwner ≠ a)
    (hdeep : Deeper a P Trusted state.executionEnv.depth)
    (hH : Holds a P state.accountMap)
    (hXstep : Xstep validJumps state = .ok (state', ret)) :
    Holds a P state'.accountMap := by
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at hXstep
  split at hXstep
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at hXstep
    split at hXstep
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      obtain ⟨hstateZ, -⟩ := Z_ok_eq_charged_cost hZ'
      subst hstateZ
      have hprefix : Holds a P stepped.accountMap :=
        (step_holds hadm (h := hStep')) howner hdeep hH
      repeat split at hXstep
      all_goals
        try contradiction
        try
          injection hXstep with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          exact hprefix
        try
          split at hXstep
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            exact hprefix
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            exact hprefix

theorem X_holds (hadm : Admissible P Trusted) {f : Nat} {validJumps : Array UInt256}
    {state state' : State} {o : ByteArray}
    (howner : state.executionEnv.codeOwner ≠ a)
    (hdeep : Deeper a P Trusted state.executionEnv.depth)
    (hH : Holds a P state.accountMap)
    (hX : X f validJumps state = .ok (.success state' o)) :
    Holds a P state'.accountMap := by
  induction f generalizing state state' o with
  | zero => simp [X] at hX
  | succ f ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error err =>
          rw [hstep] at hX
          change Except.error err = Except.ok (ExecutionResult.success state' o) at hX
          contradiction
      | ok stepRes =>
          rcases stepRes with ⟨state₁, ret⟩
          have h₁ := Xstep_holds hadm howner hdeep hH hstep
          rw [hstep] at hX
          cases ret with
          | none =>
              change
                X f validJumps
                    { state₁ with executionEnv.depth := state.executionEnv.depth } =
                  Except.ok (ExecutionResult.success state' o) at hX
              have henv := Xstep_executionEnv_eq hstep
              exact (ih (state := { state₁ with executionEnv.depth := state.executionEnv.depth })
                (hX := hX)) (by simpa [henv] using howner) hdeep h₁
          | some retVal =>
              rcases retVal with ⟨cause, out⟩
              cases cause with
              | success =>
                change
                  Except.ok (ExecutionResult.success state₁ out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                injection hres with hstate _hout
                rw [← hstate]
                exact h₁
              | revert =>
                change
                  Except.ok (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                cases hres

/-- **The frame property.**  A frame whose code owner is not `a` changes `a`'s account only
    through the message calls and creations it makes and through value it sends to `a`: if those
    keep `Holds`, so does the frame. -/
theorem Xi_holds (hadm : Admissible P Trusted) {σ σ₀ σ' : AccountMap} {g g' : UInt256}
    {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (howner : I.codeOwner ≠ a) (hdeep : Deeper a P Trusted I.depth) (hH : Holds a P σ)
    (hXi : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Holds a P σ' := by
  simp [Ξ] at hXi
  set freshState : State :=
    { (default : State) with
      accountMap := σ,
      σ₀ := σ₀,
      executionEnv := I,
      substate := A,
      machineState := { (default : State).machineState with gasAvailable := Sat256.ofUInt256 g } }
    with hfresh
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) freshState)
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (σ', g', A') o) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) freshState with
  | error err => simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas out => simp [hX, Except.bind] at hXi
      | success evmState' out =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hσ, -, -⟩, -⟩
          rw [← hσ]
          exact X_holds hadm (state := freshState) howner hdeep hH hX

/-! ## Creations and message calls -/

theorem Holds.lambdaStar {σ : AccountMap} {s a' : AccountAddress} {v : UInt256} {x : Account}
    (ha' : a' ≠ a) (hdebit : Holds a P (debit σ s v)) :
    Holds a P (match σ.get? s with
      | none => σ
      | some ac => (σ.insert s {ac with balance := ac.balance - v}).insert a' x) := by
  unfold debit at hdebit
  split
  · rename_i hs
    rw [hs] at hdebit
    exact hdebit
  · rename_i ac hs
    rw [hs] at hdebit
    exact hdebit.insert_ne ha'

theorem Holds.ite {σ τ : AccountMap} {c : Prop} [Decidable c] (hσ : Holds a P σ)
    (hτ : Holds a P τ) : Holds a P (if c then σ else τ) := by
  split
  · exact hσ
  · exact hτ

/-- A creation keeps `Holds` if the calls and creations below it do.  One that lands on `a`
    fails, since `a` has code, and leaves the account map as it was. -/
theorem lambda_good (hadm : Admissible P Trusted) {e : Fin 1025}
    (hdeep : Deeper a P Trusted e) : LambdaGood a P e := by
  intro σ σ₀ A s o g p v i ζ H bvh blocks w hH hdebit
  unfold Lambda
  simp only
  generalize Fin.ofNat AccountAddress.size (fromByteArrayBigEndian ((KEC (Lambda.L_A s
    (Option.option ⟨0⟩ (fun x => x.nonce) (σ.get? s) - ⟨1⟩) ζ i)).extract 12 32)) = a'
  split
  · exact hH
  · exact hH
  · rename_i σSS gSS ASS out hXi
    by_cases ha' : a' = a
    · subst ha'
      obtain ⟨acc, hacc, hP⟩ := id hH
      have hne : acc.code ≠ ByteArray.empty := by
        intro h
        have := hadm.code acc hP
        simp [h] at this
      simp [hacc, hne]
      exact hH
    · exact Holds.ite hH ((Xi_holds hadm ha' hdeep (Holds.lambdaStar ha' hdebit) hXi).insert_ne ha')

/-- `Θ` on code: its account map is `thetaXiAccountMap` of the code's run, for any write
    permission.  EVMLean's `code_Theta_accountMap_eq` is the case without it. -/
theorem code_Theta_accountMap_eq' (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code : ByteArray) (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (bvh : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    (Θ σ σ₀ A s o r (.Code code) g p v v' d e H bvh blocks w).1 =
      thetaXiAccountMap σ A (Ξ (sendEth r s v true σ) σ₀ g A
        { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d, source := s,
          weiValue := v', depth := e, perm := w, code := code, header := H,
          blobVersionedHashes := bvh, blocks := blocks }) := by
  unfold Θ sendEth thetaXiAccountMap thetaXiResult
  simp
  rfl

theorem Holds.thetaXi {σ : AccountMap} {A : Substate}
    {xi : Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))}
    (hH : Holds a P σ)
    (hxi : ∀ {σ' g' A' out}, xi = .ok (.success (σ', g', A') out) → Holds a P σ') :
    Holds a P (thetaXiAccountMap σ A xi) := by
  unfold thetaXiAccountMap thetaXiResult
  split
  · simpa using hH
  · simpa using hH
  · exact Holds.ite hH (hxi rfl)

/-- A message call keeps `Holds` if the calls and creations below it do: by the per-frame
    hypothesis when it runs code at `a`, by the frame property otherwise. -/
theorem theta_good (hadm : Admissible P Trusted) (hframe : FrameHyp a P Trusted)
    {e : Fin 1025} (hdeep : Deeper a P Trusted e) : ThetaGood a P Trusted e := by
  intro σ σ₀ A s o r c g p v v' d H bvh blocks w hd hcode hH hpre
  cases c with
  | Precompiled pc =>
    rw [precompiled_Theta_accountMap_eq]
    rcases precompiled_result_accountMap_empty_or_self pc (sendEth r s v true σ) g A
      { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
        code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
        blobVersionedHashes := bvh, blocks := blocks } with h | h
    · simp only [h]
      simpa using hH
    · simp only [h]
      exact Holds.ite hH hpre
  | Code code =>
    rw [code_Theta_accountMap_eq']
    refine hH.thetaXi fun hxi => ?_
    by_cases hr : r = a
    · refine hframe _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ hpre hxi
      · exact hr
      · exact hcode hr
      · exact hd
      · exact hdeep
    · exact Xi_holds hadm hr hdeep hpre hxi

/-! ## The theorem -/

/-- **Every message call and creation keeps the invariant.**  If `P` is admissible and every
    frame at `a` running trusted code keeps `Holds` whenever the calls and creations it makes
    do, then at every depth every message call and creation does, by induction on the depth
    still available below it. -/
theorem good (hadm : Admissible P Trusted) (hframe : FrameHyp a P Trusted) (e : Fin 1025) :
    ThetaGood a P Trusted e ∧ LambdaGood a P e := by
  suffices key : ∀ n, ∀ e : Fin 1025, 1024 - e.val ≤ n →
      ThetaGood a P Trusted e ∧ LambdaGood a P e from key _ e le_rfl
  intro n
  induction n with
  | zero =>
    intro e he
    have hdeep : Deeper a P Trusted e := fun e' he' => by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega
    exact ⟨theta_good hadm hframe hdeep, lambda_good hadm hdeep⟩
  | succ n ih =>
    intro e he
    have hdeep : Deeper a P Trusted e := fun e' he' => ih e' (by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega)
    exact ⟨theta_good hadm hframe hdeep, lambda_good hadm hdeep⟩

end Ethereum.EVM.Invariant
