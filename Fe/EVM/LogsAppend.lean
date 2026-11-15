import Ethereum.Theory.StaticStorage
import Ethereum.Theory.ProgressLemmas

/-!
# What message calls and creations keep of the substate

Over EVMLean alone (no `Fe` module).  `Grows R`: a relation `R` between a substate and a later
one that is reflexive and transitive, that every instruction other than a system one keeps, and
that the system instructions' own changes keep (adding an accessed account; a creation's
starting substate; `SELFDESTRUCT`).  Then `R` holds between the substate a message call `Θ` or a
creation `Lambda` is given and the one it returns (`Grows.theta`, `Grows.lambda`), and between a
frame's substate and the one `Ξ` ends with (`Grows.xi`), whatever the callee's code does.

The proof is one walk over EVMLean's machine, by induction on the depth left below a call: a
frame at depth `e` runs `X` step by step (`Grows.x`, by induction on the fuel), its system steps
call `Θ` and `Lambda` at depth `e + 1` (`Grows.call`, `Grows.create`), and at depth 1024 make no
call.  A frame that fails returns the substate it was given, as a precompile does.

`logs_grows` is the first instance: the log series only grows, `Θ` and `Lambda` append to it
(`theta_logs`, `lambda_logs`).  A callee that reverts or fails appends nothing.
-/

namespace Ethereum.EVM.Substates

open Ethereum Ethereum.EVM

/-- A relation between a substate and a later one that EVMLean's machine keeps. -/
structure Grows (R : Substate → Substate → Prop) : Prop where
  refl : ∀ A, R A A
  trans : ∀ {A B C}, R A B → R B C → R A C
  /-- Every instruction other than a system one keeps `R`. -/
  step : ∀ {op : Operation} {gasCost : ℕ} {arg : Option (UInt256 × Nat)} {state state' : State},
    (∀ s, op ≠ .System s) → EVM.step gasCost (op, arg) state = .ok state' →
      R state.substate state'.substate
  /-- A message call's substate: the callee's address accessed. -/
  access : ∀ A a, R A (A.addAccessedAccount a)
  /-- A creation's substate: the new address accessed, its created accounts any. -/
  created : ∀ A a c, R A { A.addAccessedAccount a with createdAccounts := c }
  /-- `SELFDESTRUCT`: the beneficiary accessed, the self-destruct set any. -/
  selfdestruct : ∀ (A : Substate) d r,
    R A { A with selfDestructSet := d, accessedAccounts := A.accessedAccounts.insert r }

variable {R : Substate → Substate → Prop}

/-- Every message call and creation at depth `e` keeps `R` of the substate it is given. -/
def AtDepth (R : Substate → Substate → Prop) (e : Fin 1025) : Prop :=
  (∀ σ σ₀ A s o r c g p v v' d H bvh blocks w,
    R A (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1) ∧
  (∀ σ σ₀ A s o g p v i ζ H bvh blocks w,
    R A (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1)

/-- Every message call and creation below depth `d` keeps `R`. -/
def Deeper (R : Substate → Substate → Prop) (d : Fin 1025) : Prop :=
  ∀ e : Fin 1025, d < e → AtDepth R e

theorem succ_depth_lt {e : Fin 1025} (h : e < 1024) : e < e + 1 := by
  have hv : e.val < 1024 := by simpa using! h
  rw [Fin.lt_def, Fin.val_add_eq_of_add_lt] <;> simp; omega

/-- A message call keeps `R` when every message call one level deeper does. -/
theorem Grows.ofCall (hR : Grows R) {gasCost : ℕ}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (h : EVM.call gasCost gas source recipient t value value' inOffset inSize outOffset outSize
      permission evmState = .ok (x, state')) (hdeep : Deeper R evmState.executionEnv.depth) :
    R evmState.substate state'.substate := by
  unfold EVM.call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    exact hR.trans (hR.access _ _) ((hdeep _ (succ_depth_lt hcall.2)).1 ..)
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    exact hR.access _ _

/-- A creation keeps `R` when every creation one level deeper does. -/
theorem Grows.ofCreate (hR : Grows R) {value offset size x : UInt256} {salt : Option ByteArray}
    {evmState state' : State} (h : EVM.create value offset size salt evmState = .ok (x, state'))
    (hdeep : Deeper R evmState.executionEnv.depth) :
    R evmState.substate state'.substate := by
  unfold EVM.create at h
  simp [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    first
    | exact hR.refl _
    | exact (hdeep _ (by rw [Fin.lt_def]; simp)).2 ..


/-- A system instruction keeps `R` when every message call and creation one level deeper does. -/
theorem Grows.ofSystem (hR : Grows R) {op : Operation.SOp} {gasCost : ℕ}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : EVM.step gasCost (.System op, arg) state = .ok state')
    (hdeep : Deeper R state.executionEnv.depth) :
    R state.substate state'.substate := by
  have hdeep' : ∀ st : State, st.executionEnv.depth = state.executionEnv.depth →
      Deeper R st.executionEnv.depth := fun st hst => hst ▸ hdeep
  cases op
  case RETURN | REVERT =>
    simp [EVM.step] at h
    unfold binaryMachineStateOp at h
    split at h <;> try contradiction
    injection h with h
    rw [← h]
    exact hR.refl _
  case INVALID => simp [EVM.step] at h
  case SELFDESTRUCT =>
    simp [EVM.step, Ethereum.State.lookupAccount] at h
    cases hpop : state.machineState.stack.pop with
    | none => simp [hpop] at h
    | some popped =>
      rcases popped with ⟨stack, targetWord⟩
      by_cases hcreated : state.executionEnv.codeOwner ∈ state.substate.createdAccounts
      · simp [hpop, hcreated] at h
        rw [← h]
        exact hR.selfdestruct _ _ _
      · simp [hpop, hcreated] at h
        rw [← h]
        exact hR.selfdestruct state.substate state.substate.selfDestructSet _
  all_goals
    simp [EVM.step, bind, Except.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i res hres
    rcases res with ⟨x, st⟩
    injection h with hstate
    rw [← hstate]
    first
    | (have key := hR.ofCall hres (hdeep' _ rfl); exact key)
    | (have key := hR.ofCreate hres (hdeep' _ rfl); exact key)

/-- One instruction keeps `R` when every message call and creation one level deeper does. -/
theorem Grows.ofStep (hR : Grows R) {gasCost : ℕ} {instr : Operation × Option (UInt256 × Nat)}
    {state state' : State} (h : EVM.step gasCost instr state = .ok state')
    (hdeep : Deeper R state.executionEnv.depth) : R state.substate state'.substate := by
  rcases instr with ⟨op, arg⟩
  cases op
  case System op => exact hR.ofSystem h hdeep
  all_goals exact hR.step (fun _ h => by cases h) h


/-- A step of the iterator keeps `R` when every message call and creation one level deeper
    does. -/
theorem Grows.ofXstep (hR : Grows R) {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} (h : Xstep validJumps state = .ok (state', ret))
    (hdeep : Deeper R state.executionEnv.depth) : R state.substate state'.substate := by
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at h
  split at h
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          EVM.step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      obtain ⟨hstateZ, -⟩ := Z_ok_eq_charged_cost hZ'
      subst hstateZ
      have hprefix := hR.ofStep hStep' hdeep
      repeat split at h
      all_goals
        try contradiction
        try
          injection h with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          exact hprefix
        try
          split at h
          · injection h with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            exact hprefix
          · injection h with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            exact hprefix

/-- A run of the iterator that succeeds keeps `R` when every message call and creation one level
    deeper does. -/
theorem Grows.ofX (hR : Grows R) {f : ℕ} {validJumps : Array UInt256} {state state' : State}
    {o : ByteArray} (hX : X f validJumps state = .ok (.success state' o))
    (hdeep : Deeper R state.executionEnv.depth) : R state.substate state'.substate := by
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
      have h₁ := hR.ofXstep hstep hdeep
      rw [hstep] at hX
      cases ret with
      | none =>
        change X f validJumps { state₁ with executionEnv.depth := state.executionEnv.depth } =
          Except.ok (ExecutionResult.success state' o) at hX
        exact hR.trans h₁ (ih (state := { state₁ with executionEnv.depth :=
          state.executionEnv.depth }) hX hdeep)
      | some retVal =>
        rcases retVal with ⟨cause, out⟩
        cases cause with
        | success =>
          change Except.ok (ExecutionResult.success state₁ out) =
            Except.ok (ExecutionResult.success state' o) at hX
          injection hX with hres
          injection hres with hstate _
          rw [← hstate]
          exact h₁
        | revert =>
          change Except.ok (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 out) =
            Except.ok (ExecutionResult.success state' o) at hX
          injection hX with hres
          cases hres

/-- A frame that succeeds keeps `R` of its substate when every message call and creation one level
    deeper does. -/
theorem Grows.ofXi (hR : Grows R) {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} (hXi : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o))
    (hdeep : Deeper R I.depth) : R A A' := by
  simp [Ξ, bind, Except.bind] at hXi
  split at hXi
  · contradiction
  · rename_i res hX
    split at hXi
    · injection hXi with hres
      injection hres with hp
      injection hp with _ hp
      injection hp with _ hA
      rw [← hA]
      exact hR.ofX hX hdeep
    · injection hXi with hres
      cases hres


/-! ## `Θ` and `Lambda`

The precompiles' lemmas and `code_Theta_substate_eq` are those of `Fe/EVM/Invariant.lean`,
restated here so that this file depends on EVMLean alone. -/

/-- `Θ`'s substate: the callee's when it succeeds, the one it was given otherwise. -/
def thetaXiSubstate (A : Substate)
    (xi : Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))) :
    Substate :=
  let result := thetaXiResult A xi
  if result.1 == (∅ : AccountMap) then A else result.2.2.1

theorem code_Theta_substate_eq (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code : ByteArray) (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (bvh : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    (Θ σ σ₀ A s o r (.Code code) g p v v' d e H bvh blocks w).2.2.1 =
      thetaXiSubstate A (Ξ (sendEth r s v true σ) σ₀ g A
        { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d, source := s,
          weiValue := v', depth := e, perm := w, code := code, header := H,
          blobVersionedHashes := bvh, blocks := blocks }) := by
  unfold Θ sendEth thetaXiSubstate thetaXiResult
  simp
  rfl

/-! ## Precompiles leave the substate alone -/

theorem precompile_substate_ECREC (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).2.2.1 = A := by
  simp only [Ξ_ECREC]
  repeat' split
  all_goals rfl

theorem precompile_substate_SHA256 (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).2.2.1 = A := by
  simp only [Ξ_SHA256]
  repeat' split
  all_goals rfl

theorem precompile_substate_RIP160 (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).2.2.1 = A := by
  simp only [Ξ_RIP160]
  repeat' split
  all_goals rfl

theorem precompile_substate_ID (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_ID σ g A I).2.2.1 = A := by
  simp only [Ξ_ID]
  repeat' split
  all_goals rfl

theorem precompile_substate_EXPMOD (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_EXPMOD σ g A I).2.2.1 = A := by
  unfold Ξ_EXPMOD
  dsimp only
  split_ifs <;> rfl

theorem precompile_substate_BN_ADD (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).2.2.1 = A := by
  simp only [Ξ_BN_ADD]
  repeat' split
  all_goals rfl

theorem precompile_substate_BN_MUL (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).2.2.1 = A := by
  simp only [Ξ_BN_MUL]
  repeat' split
  all_goals rfl

theorem precompile_substate_SNARKV (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).2.2.1 = A := by
  simp only [Ξ_SNARKV]
  repeat' split
  all_goals rfl

theorem precompile_substate_BLAKE2_F (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).2.2.1 = A := by
  simp only [Ξ_BLAKE2_F]
  repeat' split
  all_goals rfl

theorem precompile_substate_PointEval (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).2.2.1 = A := by
  simp only [Ξ_PointEval]
  repeat' split
  all_goals rfl

/-- What a precompile returns. -/
abbrev PreResult := AccountMap × UInt256 × Substate × ByteArray

/-- A property of each precompile's result holds of the one `Θ` picks.  `Θ.match_3` is the
    matcher of `Θ`'s choice among the precompiles; going through its `dite` chain avoids
    generating a splitter for the literal patterns. -/
theorem match3_prop {P : PreResult → Prop} (pc : AccountAddress)
    (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Unit → PreResult) (a11 : AccountAddress → PreResult)
    (h1 : P (a1 ())) (h2 : P (a2 ())) (h3 : P (a3 ())) (h4 : P (a4 ())) (h5 : P (a5 ()))
    (h6 : P (a6 ())) (h7 : P (a7 ())) (h8 : P (a8 ())) (h9 : P (a9 ())) (h10 : P (a10 ()))
    (h11 : ∀ x, P (a11 x)) :
    P (Θ.match_3 (fun _ => PreResult) pc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) := by
  delta Θ.match_3
  split
  · rename_i h; subst h; exact h1
  split
  · rename_i h; subst h; exact h2
  split
  · rename_i h; subst h; exact h3
  split
  · rename_i h; subst h; exact h4
  split
  · rename_i h; subst h; exact h5
  split
  · rename_i h; subst h; exact h6
  split
  · rename_i h; subst h; exact h7
  split
  · rename_i h; subst h; exact h8
  split
  · rename_i h; subst h; exact h9
  split
  · rename_i h; subst h; exact h10
  exact h11 _

/-- Stated over the results as variables: with the precompiles' results in place of the variables,
    the kernel check of the same proof recurses too deep. -/
theorem precompiled_choice_substate (pc : AccountAddress) (A : Substate)
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : PreResult) (h1 : r1.2.2.1 = A) (h2 : r2.2.2.1 = A)
    (h3 : r3.2.2.1 = A) (h4 : r4.2.2.1 = A) (h5 : r5.2.2.1 = A) (h6 : r6.2.2.1 = A)
    (h7 : r7.2.2.1 = A) (h8 : r8.2.2.1 = A) (h9 : r9.2.2.1 = A) (h10 : r10.2.2.1 = A) :
    (let R := Θ.match_3 (fun _ => PreResult) pc (fun _ => r1) (fun _ => r2) (fun _ => r3)
      (fun _ => r4) (fun _ => r5) (fun _ => r6) (fun _ => r7) (fun _ => r8) (fun _ => r9)
      (fun _ => r10) (fun _ => default)
     if R.1 == ∅ then A else R.2.2.1) = A := by
  have key : ∀ R : PreResult, R.2.2.1 = A ∨ R.1 = ∅ →
      (if R.1 == ∅ then A else R.2.2.1) = A := by
    intro R h
    rcases h with h | h
    · split <;> [rfl; exact h]
    · rw [ite_eq_left (by rw [h]; exact accountMap_empty_beq_empty)]
  exact key _ <| match3_prop (P := fun R => R.2.2.1 = A ∨ R.1 = ∅) pc _ _ _ _ _ _ _ _ _ _ _
    (Or.inl h1) (Or.inl h2) (Or.inl h3) (Or.inl h4) (Or.inl h5) (Or.inl h6) (Or.inl h7)
    (Or.inl h8) (Or.inl h9) (Or.inl h10) (fun _ => Or.inr rfl)

/-- A precompile returns the substate it was given. -/
theorem precompiled_Theta_substate (σ σ₀ : AccountMap) (A : Substate) (s o r pc : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader) (bvh : List ByteArray)
    (blocks : ProcessedBlocks) (w : Bool) :
    (Θ σ σ₀ A s o r (.Precompiled pc) g p v v' d e H bvh blocks w).2.2.1 = A := by
  unfold Θ
  exact precompiled_choice_substate pc A _ _ _ _ _ _ _ _ _ _
    (precompile_substate_ECREC _ _ _ _) (precompile_substate_SHA256 _ _ _ _)
    (precompile_substate_RIP160 _ _ _ _) (precompile_substate_ID _ _ _ _)
    (precompile_substate_EXPMOD _ _ _ _) (precompile_substate_BN_ADD _ _ _ _)
    (precompile_substate_BN_MUL _ _ _ _) (precompile_substate_SNARKV _ _ _ _)
    (precompile_substate_BLAKE2_F _ _ _ _) (precompile_substate_PointEval _ _ _ _)


/-- A message call at depth `e` keeps `R` when every message call and creation below `e` does. -/
theorem Grows.theta (hR : Grows R) {e : Fin 1025} (hdeep : Deeper R e)
    (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (H : BlockHeader) (bvh : List ByteArray)
    (blocks : ProcessedBlocks) (w : Bool) :
    R A (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1 := by
  cases c with
  | Precompiled pc => rw [precompiled_Theta_substate]; exact hR.refl _
  | Code code =>
    rw [code_Theta_substate_eq]
    unfold thetaXiSubstate thetaXiResult
    split
    · exact hR.refl _
    · exact hR.refl _
    · rename_i σSS gSS ASS out hxi
      dsimp only
      split
      · exact hR.refl _
      · exact hR.ofXi hxi hdeep

theorem rel_ite {A B C : Substate} {c : Prop} [Decidable c] (hB : R A B) (hC : R A C) :
    R A (if c then B else C) := by
  split <;> assumption

/-- A creation at depth `e` keeps `R` when every message call and creation below `e` does. -/
theorem Grows.lambda (hR : Grows R) {e : Fin 1025} (hdeep : Deeper R e)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
    (ζ : Option ByteArray) (H : BlockHeader) (bvh : List ByteArray) (blocks : ProcessedBlocks)
    (w : Bool) : R A (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1 := by
  generalize hr : Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w = res
  unfold Lambda at hr
  simp only at hr
  split at hr
  · subst hr; exact hR.created _ _ _
  · subst hr; exact hR.created _ _ _
  · rename_i σSS gSS ASS out hXi
    subst hr
    dsimp only
    have hS := hR.trans (hR.created _ _ _) (hR.ofXi hXi hdeep)
    exact rel_ite (hR.created _ _ _) hS

/-- **Every message call and creation keeps `R`** of the substate it is given, at every depth. -/
theorem Grows.atDepth (hR : Grows R) (e : Fin 1025) : AtDepth R e := by
  suffices key : ∀ n, ∀ e : Fin 1025, 1024 - e.val ≤ n → AtDepth R e from key _ e le_rfl
  intro n
  induction n with
  | zero =>
    intro e he
    have hdeep : Deeper R e := fun e' he' => by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega
    exact ⟨hR.theta hdeep, hR.lambda hdeep⟩
  | succ n ih =>
    intro e he
    have hdeep : Deeper R e := fun e' he' => ih e' (by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega)
    exact ⟨hR.theta hdeep, hR.lambda hdeep⟩

/-- A frame that succeeds keeps `R` of its substate. -/
theorem Grows.xi (hR : Grows R) {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} (hXi : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    R A A' :=
  hR.ofXi hXi fun e _ => hR.atDepth e


/-! ## The log series only grows -/

/-- The log series of `B` extends that of `A`. -/
def LogsExtend (A B : Substate) : Prop := ∃ l, B.logSeries = A.logSeries ++ l

section Logs

variable {state state' : State}


variable {state state' : State}

theorem logs_execUnOp {f : Primop.Unary} (h : execUnOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold execUnOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_execBinOp {f : Primop.Binary} (h : execBinOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold execBinOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_execTriOp {f : Primop.Ternary} (h : execTriOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold execTriOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_machineStateOp {f : MachineState → UInt256} (h : machineStateOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold machineStateOp at h
  injection h with h; rw [← h]; rfl

theorem logs_executionEnvOp {f : ExecutionEnv → UInt256} (h : executionEnvOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold executionEnvOp at h
  injection h with h; rw [← h]; rfl

theorem logs_unaryStateOp {f : State → UInt256 → State × UInt256}
    (hf : ∀ s v, (f s v).1.substate.logSeries = s.substate.logSeries) (h : unaryStateOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold unaryStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _

theorem logs_stateOp {f : State → UInt256} (h : stateOp f state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold stateOp at h
  injection h with h; rw [← h]; rfl

theorem logs_binaryMachineStateOp {f : MachineState → UInt256 → UInt256 → MachineState}
    (h : binaryMachineStateOp f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold binaryMachineStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_binaryMachineStateOp' {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState}
    (h : binaryMachineStateOp' f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold binaryMachineStateOp' at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_ternaryMachineStateOp
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    (h : ternaryMachineStateOp f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold ternaryMachineStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; rfl

theorem logs_ternaryCopyOp {f : State → UInt256 → UInt256 → UInt256 → State}
    (hf : ∀ s a b c, (f s a b c).substate.logSeries = s.substate.logSeries)
    (h : ternaryCopyOp f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold ternaryCopyOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _ _

theorem logs_quaternaryCopyOp {f : State → UInt256 → UInt256 → UInt256 → UInt256 → State}
    (hf : ∀ s a b c d, (f s a b c d).substate.logSeries = s.substate.logSeries)
    (h : quaternaryCopyOp f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold quaternaryCopyOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _ _ _

theorem logs_binaryStateOp {f : State → UInt256 → UInt256 → State}
    (hf : ∀ s a b, (f s a b).substate.logSeries = s.substate.logSeries)
    (h : binaryStateOp f state = .ok state') : state'.substate.logSeries = state.substate.logSeries := by
  unfold binaryStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _

theorem logs_dup {n : ℕ} (h : dup n state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold dup at h
  by_cases hlen : (List.take n state.machineState.stack).length = n
  · rw [ite_eq_left hlen] at h
    injection h with h; rw [← h]; rfl
  · rw [ite_eq_right hlen] at h
    contradiction

theorem logs_swap {n : ℕ} (h : swap n state = .ok state') :
    state'.substate.logSeries = state.substate.logSeries := by
  unfold swap at h
  by_cases hlen : (List.take (n + 1) state.machineState.stack).length = n + 1
  · rw [ite_eq_left hlen] at h
    injection h with h; rw [← h]; rfl
  · rw [ite_eq_right hlen] at h
    contradiction

theorem logs_sstore (s : State) (k v : UInt256) : (s.sstore k v).substate.logSeries = s.substate.logSeries := by
  unfold Ethereum.State.sstore
  simp only [Ethereum.State.lookupAccount]
  rcases s.accountMap.get? s.executionEnv.codeOwner with _ | acc <;> rfl

theorem logs_tstore (s : State) (k v : UInt256) : (s.tstore k v).substate.logSeries = s.substate.logSeries := by
  unfold Ethereum.State.tstore
  simp only [Ethereum.State.lookupAccount]
  rcases s.accountMap.get? s.executionEnv.codeOwner with _ | acc <;> rfl

theorem logs_extCodeHash (s : State) (v : UInt256) :
    (s.extCodeHash v).1.substate.logSeries = s.substate.logSeries := by
  unfold Ethereum.State.extCodeHash
  dsimp only
  split <;> rfl

/-- An instruction other than a system one appends to the log series at most the entry of a
    `LOG`. -/
theorem logs_step {op : Operation} {gasCost : ℕ} {arg : Option (UInt256 × Nat)}
    (hop : ∀ s, op ≠ .System s) (h : EVM.step gasCost (op, arg) state = .ok state') :
    LogsExtend state.substate state'.substate := by
  have same : state'.substate.logSeries = state.substate.logSeries →
      LogsExtend state.substate state'.substate := fun hs => ⟨#[], by rw [hs]; simp⟩
  rcases op with op | op | op | op | op | op | op | op | op | op | op
  rotate_right
  · exact absurd rfl (hop op)
  all_goals cases op <;> simp [EVM.step] at h
  all_goals first
    | (have hs := logs_execUnOp h; exact same hs)
    | (split at h <;> first | contradiction | (have hs := logs_execUnOp h; exact same hs))
    | (have hs := logs_execBinOp h; exact same hs)
    | (have hs := logs_execTriOp h; exact same hs)
    | (have hs := logs_machineStateOp h; exact same hs)
    | (have hs := logs_executionEnvOp h; exact same hs)
    | (have hs := logs_stateOp h; exact same hs)
    | (have hs := logs_binaryMachineStateOp h; exact same hs)
    | (have hs := logs_binaryMachineStateOp' h; exact same hs)
    | (have hs := logs_ternaryMachineStateOp h; exact same hs)
    | (have hs := logs_dup h; exact same hs)
    | (have hs := logs_swap h; exact same hs)
    | (have hs := logs_binaryStateOp logs_sstore h; exact same hs)
    | (have hs := logs_binaryStateOp logs_tstore h; exact same hs)
    | (have hs := logs_unaryStateOp (by intros; first | rfl | exact logs_extCodeHash _ _) h; exact same hs)
    | (have hs := logs_ternaryCopyOp (by intros; rfl) h; exact same hs)
    | (have hs := logs_quaternaryCopyOp (by intros; rfl) h; exact same hs)
    | (apply same; rw [← h]; try rfl)
    | (simp only [log0Op, log1Op, log2Op, log3Op, log4Op, evmLogOp] at h
       split at h <;> try contradiction
       injection h with hst
       rw [← hst]
       exact ⟨_, Array.push_eq_append⟩)
    | (apply same
       split at h <;> try contradiction
       injection h with hst
       rw [← hst]
       try rfl)

end Logs

/-- The log series only grows: every instruction appends to it at most a `LOG`'s entry, and the
    system instructions' own changes of the substate leave it alone. -/
theorem logs_grows : Grows LogsExtend where
  refl A := ⟨#[], by simp⟩
  trans := fun ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by rw [h₂, h₁, Array.append_assoc]⟩
  step hop h := logs_step hop h
  access _ _ := ⟨#[], by simp [Substate.addAccessedAccount]⟩
  created _ _ _ := ⟨#[], by simp [Substate.addAccessedAccount]⟩
  selfdestruct _ _ _ := ⟨#[], by simp⟩

/-- **A message call appends to the log series it is given**: `Θ`'s substate has the log series
    of the one it was given followed by what the callee logged, none if it reverted or failed. -/
theorem theta_logs (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (c : ToExecute)
    (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader) (bvh : List ByteArray)
    (blocks : ProcessedBlocks) (w : Bool) :
    ∃ l, (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1.logSeries = A.logSeries ++ l :=
  (logs_grows.atDepth e).1 ..

/-- **A creation appends to the log series it is given.** -/
theorem lambda_logs (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress) (g p v : UInt256)
    (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray) (H : BlockHeader)
    (bvh : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    ∃ l, (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1.logSeries = A.logSeries ++ l :=
  (logs_grows.atDepth e).2 ..

/-- A log series that extends another is it followed by the entries past its end. -/
theorem LogsExtend.extract {A B : Substate} (h : LogsExtend A B) :
    B.logSeries = A.logSeries ++ B.logSeries.extract A.logSeries.size := by
  obtain ⟨l, hl⟩ := h
  rw [hl]
  simp

/-- `theta_logs` with the appended entries as those past the end of the given log series. -/
theorem theta_logs_extract (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (c : ToExecute) (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (bvh : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1.logSeries =
      A.logSeries ++ (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1.logSeries.extract
        A.logSeries.size :=
  LogsExtend.extract (theta_logs ..)

/-- `lambda_logs` with the appended entries as those past the end of the given log series. -/
theorem lambda_logs_extract (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray) (H : BlockHeader)
    (bvh : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1.logSeries =
      A.logSeries ++ (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1.logSeries.extract
        A.logSeries.size :=
  LogsExtend.extract (lambda_logs ..)

end Ethereum.EVM.Substates
