import Ethereum.Theory.StaticStorage
import Ethereum.Theory.ReturnDataBound

/-!
# A contract invariant through reentrant message calls

Over EVMLean alone (no `Fe` module): a contract at address `a` keeps an invariant on its account
through every message call and creation, at every depth, if each frame that runs its code keeps
the invariant whenever the calls and creations below that frame do.  This is the theorem the
standard method rests on: assume the invariant on entry to every public function, re-establish it
at every normal return and before every external call, since the callee may call back in.  The
theorem is relative to an admission condition on the frames at `a`, for invariants whose
per-frame proof needs something of the call (a calldata bound, keys that do not collide).

## The statement

`Holds a P σ`: `a`'s account exists in `σ` and satisfies `P : Account → Prop`.  The invariant sees
`a`'s account only.

`admits : AccountMap → ExecutionEnv → Prop` is the admission condition, on the account map a frame
at `a` starts from and its environment.

`Admitted a admits T`, for the inputs `T` of a message call: in the execution of `T`, every
successful frame at `a` is admitted.  It is defined by recursion on the depth left below the call
(`Adm`), and follows the frame step by step (`XiOk`, `XOk`, `XstepOk`, `stepOk`): if `T` runs code
and its frame succeeds, then the frame is admitted when it runs at `a`, and every message call and
creation the frame makes is admitted in turn, at the next depth.  So it covers the frames at `a`
reached through any number of other contracts, and the frames below a frame at `a`, re-entry
included.  `AdmittedL` is the same for a creation, whose frame never runs at `a` with effect: a
creation that lands on `a`, which has code, leaves the account map as it was whatever its frame
does, so its frame is not asked to be admitted.

What it does not constrain:
- A frame that fails.  Its changes are undone, so neither it nor the frames below it need be
  admitted.  A successful frame's nested call that fails is such a frame.
- A call that is not made (without the funds, at depth 1024) or a creation that is not made
  (also with the creator's nonce at its limit): there is no frame.
- A precompile: it runs no frame.

`ThetaGood a P Trusted admits e`: every admitted message call at depth `e` ends where `Holds`
holds, if it starts where `Holds` holds both before and after its value moves (`sendEth`, as `Θ`
moves it), its calldata size fits a word, and it runs code `Trusted` admits (or a precompile) when
its recipient is `a` (`GoodTheta`).  It also keeps `a` out of the created accounts and the
self-destruct set of the substate (`SubOk`), if the substate it starts with does.  `LambdaGood a P
admits e` is the same for `Lambda`, with the creator's payment (`debit`, `GoodLambda`).  `Deeper`
is both, at every depth below a given one.  The substate part does not depend on `P`: a model that
makes calls under a feed of arbitrary substates uses only the account part.

`FrameHyp a P Trusted admits`, the per-frame hypothesis: every successful `Ξ` with code owner `a`,
running code `Trusted` admits, with calldata that fits a word, admitted, and starting where
`Holds` holds, ends with `a`'s account satisfying `P`, if its code is still what it was.  The frame
may assume `Deeper` (the admitted calls and creations below it are good) and that the calls and
creations it makes directly are admitted (`XiOk`); it must show `Holds` before each call it makes,
with any value already taken from `a`.  That the code is kept, and the substate part, need not be
shown: `Xi_code` proves them of every frame, whatever it runs.

A frame at `a` that executes `SELFDESTRUCT` moves `a`'s balance out.  That is not a balance
increase, so it is the frame's own effect, which `FrameHyp` speaks about: the frame's result must
satisfy `P`.  It does not remove `a`: EVMLean adds the running account to the self-destruct set
only when the substate lists it among the accounts this transaction created, and `a` is never
listed (`SubOk`).

`good`: from `Admissible P Trusted` and `FrameHyp a P Trusted admits`, `ThetaGood` and `LambdaGood`
hold at every depth.  With `admits := fun _ _ => True` every execution is admitted
(`admitted_of_all`), and the theorem is about every message call and creation.
`Fe.EVM.RefineInvariant` derives `FrameHyp` from a certificate of the bytecode.

`tx_holds`, the transaction: `Υ` keeps `Holds` if the outermost call or creation, as `Υ` makes it
(`txCall`), is admitted (`TxAdmitted`), and two more conditions hold:
- The sender has no code.  `Υ` does not check this; EIP-3607 makes such a transaction invalid,
  and EVMLean's conformance runner rejects it (`SENDER_NOT_EOA`) before calling `Υ`.  Since `a`
  has code, the sender is not `a`, so the upfront payment and the gas refund do not touch `a`.
- The transaction's data size fits a word, as a frame's calldata must.
`Υ` erases the accounts in the self-destruct set its message call or creation returns; `a` is not
among them.  The transaction's call starts with no created accounts and an empty self-destruct set,
and every call and creation keeps `SubOk`: a creation lists only an address without code, which
`a` is not, and `SELFDESTRUCT` adds the running account only when it is listed.  A call or creation
that fails returns the substate it was given (a creation with its created accounts restored), and a
precompile returns it unchanged (`precompiled_Theta_substate`).
`P` must also tolerate clearing the transient storage, which `Υ` does at the end; this is a
hypothesis of `tx_holds` only, since nothing inside a transaction clears it.  The priority fee
and refund are balance increases, and `a`, having code, is never a dead account.

`deploy_holds`, the base case: a creation that succeeds ends with `Holds` at the address it
created, if the account its init code leaves there, with the code the init code returns, satisfies
`P`.  `lambda_success` says what a successful creation did: the target had no nonce, code or
storage (EIP-7610; otherwise the init code is `INVALID` and fails), so the init code ran from an
account with empty storage, and `Lambda` installed the returned code over the account the init
code left.  During the creation `a` has no code yet, so the theorems above apply only from then
on.

## The proof

Induction on the depth left below a call (`1024 - e`, `good_core`); fuel plays no part in it.
EVMLean's `Ξ` runs `X` with fuel `g + 1`, and `X` runs out of fuel only with an `.error`, after
which `Θ` keeps the account map it started from, so only successful runs need an argument, and
those are followed step by step (`X_holds`, by induction on the fuel of that one run).  A frame
calls `Θ` and `Lambda` one level deeper; at depth 1024 it makes no call.

- `Xi_holds`, the frame property, the one walk over EVMLean's instructions: a frame whose code
  owner is not `a` changes `a`'s account only through the calls and creations it makes and by
  sending value to `a` (a `CALL` with value, a `SELFDESTRUCT` naming `a`).  The same walk carries
  `SubOk` for every frame: an instruction other than a call, creation or `SELFDESTRUCT` leaves
  the created accounts and the self-destruct set as they were (`step_sets`, by instruction group,
  since EVMLean has no lemmas on the substate).  It takes the condition
  on the calls the frame makes as a parameter `Q`, which the step functions `stepOk` and so on
  read off the same instructions.  `SSTORE` and `TSTORE` write the frame's own account.  The
  instructions that leave the account map alone are EVMLean's `static_step_*_accountMap_eq`.
  It also covers a frame at `a` when `P` sees only the code (`OwnerOk`): no instruction changes
  the code of an account.  `code_good` and `Xi_code` are that case.
- `theta_good`: an admitted call to `a` runs `a`'s code, which `Trusted` admits, and the
  per-frame hypothesis applies; any other call runs at another address and `Xi_holds` applies; a
  precompile leaves the account map as it was or as the value transfer made it.
- `lambda_good`: a creation at an address other than `a` runs there and `Xi_holds` applies; one
  at `a` fails, because `a` has code, and leaves the account map as it was.

## The conditions, and why each is needed

`Admissible P Trusted`:

- `balance`: `P` tolerates any increase of the balance, as EVMLean adds (modulo `2 ^ 256`).
  Value reaches `a` without running its code.  EVMLean adds balances without a bound on their
  sum, so an invariant such as "the balance covers the supply" is not closed under this
  addition, though on the real chain the addition cannot wrap.  Such invariants need a bound on
  the sum of all balances that EVMLean's semantics preserves; that is not proved here.
- `code`: `a` has code, so no creation can land on `a` (`Lambda` keeps the account map when the
  target has code or a nonce).
- `trusted`: a `CALL` or `STATICCALL` to `a` runs the code `a` has, which must be code the
  per-frame hypothesis covers.

`Trusted` is the condition on `DELEGATECALL`: a frame at `a` may assume `Deeper` only of calls
that run trusted code when their recipient is `a`.  A `DELEGATECALL` or `CALLCODE` from `a` runs
other code at `a`, which writes `a`'s storage directly, so the per-frame hypothesis cannot be shown
for a contract that delegates to code it has no contract for.  `Trusted` may admit such code
alongside the contract's own, with the per-frame hypothesis shown for it too.

`SELFDESTRUCT` and code replacement follow EVMLean's rules (Cancun and later): `SELFDESTRUCT`
moves the balance, and removes the account only at the end of a transaction that created it.  No
instruction replaces code; a creation sets code only at an address without code or nonce.

## What remains

- Balance-monotone invariants, as above.
- A sequence of transactions, or a block, is the iteration of `tx_holds`; it is not stated.
-/

namespace Ethereum.EVM.Invariant

/-! ## The invariant -/

section Defs

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

/-- `P` sees an account only through its code. -/
def CodeOnly : Prop := ∀ acc acc', acc.code = acc'.code → P acc → P acc'

/-- What `P` must allow. -/
structure Admissible : Prop where
  /-- Value can arrive without a call: by a transfer, a `SELFDESTRUCT`, a block reward. -/
  balance : ∀ acc v, P acc → P {acc with balance := acc.balance + v}
  /-- `a` has code, so no creation can land on it. -/
  code : ∀ acc, P acc → acc.code.size ≠ 0
  /-- A message call to `a` runs code that `Trusted` admits. -/
  trusted : ∀ acc, P acc → Trusted acc.code

end Defs

section HoldsLemmas

variable {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}

theorem Holds.insert_ne {σ : AccountMap} {k : AccountAddress} {x : Account} (hk : k ≠ a)
    (h : Holds a P σ) : Holds a P (σ.insert k x) := by
  obtain ⟨acc, hacc, hP⟩ := h
  refine ⟨acc, ?_, hP⟩
  rw [Std.ExtTreeMap.getElem?_insert]
  simp [Std.LawfulEqCmp.compare_eq_iff_eq, hk, hacc]

theorem Holds.insert_self {σ : AccountMap} {x : Account} (hx : P x) :
    Holds a P (σ.insert a x) :=
  ⟨x, by simp, hx⟩

theorem Holds.get {σ : AccountMap} (h : Holds a P σ) :
    ∃ acc, σ.get? a = some acc ∧ P acc := by
  simpa [Std.ExtTreeMap.get?_eq_getElem?] using h

theorem Holds.of_eq {σ τ : AccountMap} (h : Holds a P σ) (he : τ = σ) : Holds a P τ :=
  he ▸ h

/-- A write to the account of a frame's owner keeps `Holds` when the owner is not `a`, or when
    `P` sees only the code and the write keeps it. -/
theorem Holds.insert_owner {σ : AccountMap} {k : AccountAddress} {x : Account}
    (hk : k ≠ a ∨ CodeOnly P) (hx : ∀ old, σ[k]? = some old → old.code = x.code)
    (h : Holds a P σ) : Holds a P (σ.insert k x) := by
  by_cases hka : k = a
  · subst hka
    obtain ⟨acc, hacc, hP⟩ := h
    exact Holds.insert_self (hk.resolve_left (fun h => h rfl) acc x (hx acc hacc) hP)
  · exact h.insert_ne hka

theorem UInt256.sub_zero' (x : UInt256) : x - ⟨0⟩ = x := by
  cases x
  show UInt256.mk _ = _
  simp

theorem Holds.transfer (hadm : Admissible P Trusted) {σ : AccountMap} {r s : AccountAddress}
    {v : UInt256} (hs : s ≠ a ∨ v = ⟨0⟩ ∨ CodeOnly P) (h : Holds a P σ) :
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
        obtain ⟨acc, hacc, hP⟩ := hτ
        have : accs = acc := by
          simpa [Std.ExtTreeMap.get?_eq_getElem?, hacc] using hs'.symm
        subst this
        refine Holds.insert_self ?_
        rcases hs with hs | hv | hco
        · exact absurd rfl hs
        · subst hv
          simpa [UInt256.sub_zero'] using hP
        · exact hco accs _ rfl hP
      · exact Holds.insert_ne hsa hτ
  exact h2 _ h1

theorem Holds.pay {σ : AccountMap} {s : AccountAddress} {v : UInt256}
    (hs : s ≠ a ∨ CodeOnly P) (h : Holds a P σ) : Holds a P (debit σ s v) := by
  unfold debit
  split
  · exact h
  · rename_i ac hac
    refine h.insert_owner hs fun old hold => ?_
    have : old = ac := by simpa [Std.ExtTreeMap.get?_eq_getElem?, hold] using hac
    subst this
    rfl

theorem Holds.ite {σ τ : AccountMap} {c : Prop} [Decidable c] (hσ : Holds a P σ)
    (hτ : Holds a P τ) : Holds a P (if c then σ else τ) := by
  split
  · exact hσ
  · exact hτ

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

theorem codeOk_toExecute (hadm : Admissible P Trusted) {σ : AccountMap} (h : Holds a P σ) :
    CodeOk Trusted (toExecute σ a) := by
  obtain ⟨acc, hacc, hP⟩ := h.get
  unfold toExecute
  split
  · trivial
  · simp only [Id.run, hacc]
    exact hadm.trusted acc hP

theorem codeOk_of_all {Trusted : ByteArray → Prop} (h : ∀ d, Trusted d) (c : ToExecute) :
    CodeOk Trusted c := by
  cases c
  · exact h _
  · trivial

end HoldsLemmas

/-! ## The calls a frame makes -/

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

/-! ## The substate -/

/-- `a` is neither among the accounts created in this transaction nor in the self-destruct set.
    `Υ` erases the accounts in that set at the end of the transaction. -/
def SubOk (a : AccountAddress) (A : Substate) : Prop :=
  a ∉ A.createdAccounts.toList ∧ a ∉ A.selfDestructSet.toList

/-- The created accounts and the self-destruct set are as they were. -/
def SameSets (A A' : Substate) : Prop :=
  A'.createdAccounts = A.createdAccounts ∧ A'.selfDestructSet = A.selfDestructSet

section Sets

variable {state state' : State}

theorem sets_execUnOp {f : Primop.Unary} (h : execUnOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold execUnOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_execBinOp {f : Primop.Binary} (h : execBinOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold execBinOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_execTriOp {f : Primop.Ternary} (h : execTriOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold execTriOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_machineStateOp {f : MachineState → UInt256} (h : machineStateOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold machineStateOp at h
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_executionEnvOp {f : ExecutionEnv → UInt256} (h : executionEnvOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold executionEnvOp at h
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_unaryStateOp {f : State → UInt256 → State × UInt256}
    (hf : ∀ s v, SameSets s.substate (f s v).1.substate) (h : unaryStateOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold unaryStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _

theorem sets_stateOp {f : State → UInt256} (h : stateOp f state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold stateOp at h
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_binaryMachineStateOp {f : MachineState → UInt256 → UInt256 → MachineState}
    (h : binaryMachineStateOp f state = .ok state') : SameSets state.substate state'.substate := by
  unfold binaryMachineStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_binaryMachineStateOp' {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState}
    (h : binaryMachineStateOp' f state = .ok state') : SameSets state.substate state'.substate := by
  unfold binaryMachineStateOp' at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_ternaryMachineStateOp
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    (h : ternaryMachineStateOp f state = .ok state') : SameSets state.substate state'.substate := by
  unfold ternaryMachineStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact ⟨rfl, rfl⟩

theorem sets_ternaryCopyOp {f : State → UInt256 → UInt256 → UInt256 → State}
    (hf : ∀ s a b c, SameSets s.substate (f s a b c).substate)
    (h : ternaryCopyOp f state = .ok state') : SameSets state.substate state'.substate := by
  unfold ternaryCopyOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _ _

theorem sets_quaternaryCopyOp {f : State → UInt256 → UInt256 → UInt256 → UInt256 → State}
    (hf : ∀ s a b c d, SameSets s.substate (f s a b c d).substate)
    (h : quaternaryCopyOp f state = .ok state') : SameSets state.substate state'.substate := by
  unfold quaternaryCopyOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _ _ _

theorem sets_binaryStateOp {f : State → UInt256 → UInt256 → State}
    (hf : ∀ s a b, SameSets s.substate (f s a b).substate)
    (h : binaryStateOp f state = .ok state') : SameSets state.substate state'.substate := by
  unfold binaryStateOp at h; split at h <;> try contradiction
  injection h with h; rw [← h]; exact hf _ _ _

theorem sets_dup {n : ℕ} (h : dup n state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold dup at h
  by_cases hlen : (List.take n state.machineState.stack).length = n
  · rw [if_pos hlen] at h
    injection h with h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg hlen] at h
    contradiction

theorem sets_swap {n : ℕ} (h : swap n state = .ok state') :
    SameSets state.substate state'.substate := by
  unfold swap at h
  by_cases hlen : (List.take (n + 1) state.machineState.stack).length = n + 1
  · rw [if_pos hlen] at h
    injection h with h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg hlen] at h
    contradiction

theorem sets_sstore (s : State) (k v : UInt256) : SameSets s.substate (s.sstore k v).substate := by
  unfold Ethereum.State.sstore
  simp only [Ethereum.State.lookupAccount]
  rcases s.accountMap.get? s.executionEnv.codeOwner with _ | acc <;> exact ⟨rfl, rfl⟩

theorem sets_tstore (s : State) (k v : UInt256) : SameSets s.substate (s.tstore k v).substate := by
  unfold Ethereum.State.tstore
  simp only [Ethereum.State.lookupAccount]
  rcases s.accountMap.get? s.executionEnv.codeOwner with _ | acc <;> exact ⟨rfl, rfl⟩

theorem sets_extCodeHash (s : State) (v : UInt256) :
    SameSets s.substate (s.extCodeHash v).1.substate := by
  unfold Ethereum.State.extCodeHash
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- An instruction other than a system one leaves the created accounts and the self-destruct set
    as they were. -/
theorem step_sets {op : Operation} {gasCost : ℕ} {arg : Option (UInt256 × Nat)}
    (hop : ∀ s, op ≠ .System s) (h : step gasCost (op, arg) state = .ok state') :
    SameSets state.substate state'.substate := by
  rcases op with op | op | op | op | op | op | op | op | op | op | op
  rotate_right
  · exact absurd rfl (hop op)
  all_goals cases op <;> simp [step] at h
  all_goals first
    | (have hs := sets_execUnOp h; exact hs)
    | (have hs := sets_execBinOp h; exact hs)
    | (have hs := sets_execTriOp h; exact hs)
    | (have hs := sets_machineStateOp h; exact hs)
    | (have hs := sets_executionEnvOp h; exact hs)
    | (have hs := sets_stateOp h; exact hs)
    | (have hs := sets_binaryMachineStateOp h; exact hs)
    | (have hs := sets_binaryMachineStateOp' h; exact hs)
    | (have hs := sets_ternaryMachineStateOp h; exact hs)
    | (have hs := sets_dup h; exact hs)
    | (have hs := sets_swap h; exact hs)
    | (have hs := sets_binaryStateOp sets_sstore h; exact hs)
    | (have hs := sets_binaryStateOp sets_tstore h; exact hs)
    | (have hs := sets_unaryStateOp
          (by intros; first | exact ⟨rfl, rfl⟩ | exact sets_extCodeHash _ _) h
       exact hs)
    | (have hs := sets_ternaryCopyOp (by intros; exact ⟨rfl, rfl⟩) h; exact hs)
    | (have hs := sets_quaternaryCopyOp (by intros; exact ⟨rfl, rfl⟩) h; exact hs)
    | (rw [← h]; exact ⟨rfl, rfl⟩)
    | (simp only [log0Op, log1Op, log2Op, log3Op, log4Op, evmLogOp] at h
       split at h <;> try contradiction
       injection h with hst
       rw [← hst]
       exact ⟨rfl, rfl⟩)
    | (split at h <;> try contradiction
       injection h with hst
       rw [← hst]
       exact ⟨rfl, rfl⟩)

end Sets

theorem SubOk.ite {a : AccountAddress} {A B : Substate} {c : Prop} [Decidable c]
    (hA : SubOk a A) (hB : SubOk a B) : SubOk a (if c then A else B) := by
  split
  · exact hA
  · exact hB

theorem SubOk.of_sets {a : AccountAddress} {A A' : Substate} (h : SubOk a A)
    (hs : SameSets A A') : SubOk a A' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨hs.1 ▸ h1, hs.2 ▸ h2⟩

/-- `SELFDESTRUCT` adds the running account to the self-destruct set only when it is among the
    accounts this transaction created, which `a` is not. -/
theorem SubOk.selfdestruct {a o r : AccountAddress} {A : Substate} (h : SubOk a A)
    (ho : o ∈ A.createdAccounts) :
    SubOk a { A with selfDestructSet := A.selfDestructSet.insert o,
                     accessedAccounts := A.accessedAccounts.insert r } := by
  refine ⟨h.1, fun hmem => ?_⟩
  rcases Batteries.RBSet.mem_toList_insert.mp hmem with ⟨hmem, -⟩ | rfl
  · exact h.2 hmem
  · obtain ⟨y, hy, hcmp⟩ := Batteries.RBSet.mem_iff_mem_toList.mp ho
    rw [Std.LawfulEqCmp.eq_of_compare hcmp] at h
    exact h.1 hy

/-! ## What the calls must do -/

section Good

variable (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)

/-- A message call keeps `Holds`, if it starts from a state where it holds both before and after
    the value moves, has calldata that fits a word, and runs `Trusted` code when its recipient is
    `a`; and it keeps `SubOk` of the substate. -/
def GoodTheta (T : ThetaCall) : Prop :=
  T.d.size < UInt256.size → (T.r = a → CodeOk Trusted T.c) → Holds a P T.σ →
    Holds a P (sendEth T.r T.s T.v true T.σ) →
      Holds a P T.run.1 ∧ (SubOk a T.A → SubOk a T.run.2.2.1)

/-- A creation keeps `Holds`, if it holds before and after the creator pays; and it keeps `SubOk`
    of the substate. -/
def GoodLambda (L : LambdaCall) : Prop :=
  Holds a P L.σ → Holds a P (debit L.σ L.s L.v) →
    Holds a P L.run.2.1 ∧ (SubOk a L.A → SubOk a L.run.2.2.2.1)

end Good


/-! ## The frame property -/

section Frame

variable {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}

variable (a P Trusted) in
/-- A frame owned by `o` writes `a`'s account only through what it calls, or `P` sees only code
    and any code may run at `a`. -/
def OwnerOk (o : AccountAddress) : Prop := o ≠ a ∨ (CodeOnly P ∧ ∀ d, Trusted d)

theorem OwnerOk.ne_or_codeOnly {o : AccountAddress} (h : OwnerOk a P Trusted o) :
    o ≠ a ∨ CodeOnly P :=
  h.imp id (·.1)

theorem sstore_accountMap (state : State) (k v : UInt256) :
    (state.sstore k v).accountMap = state.accountMap ∨
      ∃ acc x, state.accountMap[state.executionEnv.codeOwner]? = some acc ∧
        acc.code = x.code ∧
        (state.sstore k v).accountMap = state.accountMap.insert state.executionEnv.codeOwner x := by
  unfold Ethereum.State.sstore
  simp only [Ethereum.State.lookupAccount]
  rcases h : state.accountMap.get? state.executionEnv.codeOwner with _ | acc
  · exact Or.inl (by simp [Option.option])
  · refine Or.inr ⟨acc, acc.updateStorage k v, ?_, ?_, ?_⟩
    · simpa [Std.ExtTreeMap.get?_eq_getElem?] using h
    · unfold Account.updateStorage; split <;> rfl
    · simp [Option.option, Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey]

theorem tstore_accountMap (state : State) (k v : UInt256) :
    (state.tstore k v).accountMap = state.accountMap ∨
      ∃ acc x, state.accountMap[state.executionEnv.codeOwner]? = some acc ∧
        acc.code = x.code ∧
        (state.tstore k v).accountMap = state.accountMap.insert state.executionEnv.codeOwner x := by
  unfold Ethereum.State.tstore
  simp only [Ethereum.State.lookupAccount]
  rcases h : state.accountMap.get? state.executionEnv.codeOwner with _ | acc
  · exact Or.inl (by simp [Option.option])
  · refine Or.inr ⟨acc, acc.updateTransientStorage k v, ?_, ?_, ?_⟩
    · simpa [Std.ExtTreeMap.get?_eq_getElem?] using h
    · unfold Account.updateTransientStorage; split <;> rfl
    · simp [Option.option, Ethereum.State.updateAccount]

/-- A stack, memory, storage or control-flow instruction keeps `Holds`: only `SSTORE` and
    `TSTORE` touch the account map, and only the frame owner's account. -/
theorem step_stackMemFlow {op : Operation.SMSFOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state state' : State}
    (hown : OwnerOk a P Trusted state.executionEnv.codeOwner) (hH : Holds a P state.accountMap)
    (h : step gasCost (.StackMemFlow op, arg) state = .ok state') :
    Holds a P state'.accountMap := by
  have hstore : ∀ {f : State → UInt256 → UInt256 → State},
      (∀ st k v, (f st k v).accountMap = st.accountMap ∨
        ∃ acc x, st.accountMap[st.executionEnv.codeOwner]? = some acc ∧ acc.code = x.code ∧
          (f st k v).accountMap = st.accountMap.insert st.executionEnv.codeOwner x) →
      ∀ {st st' : State}, st.accountMap = state.accountMap →
        st.executionEnv.codeOwner = state.executionEnv.codeOwner →
        binaryStateOp f st = .ok st' → Holds a P st'.accountMap := by
    intro f hf st st' hσ hown' hop
    unfold binaryStateOp at hop
    split at hop <;> try contradiction
    rename_i k v _
    injection hop with hst
    subst hst
    simp only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    rcases hf st k v with he | ⟨acc, x, hacc, hcode, he⟩
    · exact hH.of_eq (he.trans hσ)
    · rw [he]
      rw [hσ, hown'] at hacc ⊢
      refine hH.insert_owner hown.ne_or_codeOnly fun old hold => ?_
      rw [hacc] at hold
      cases hold
      exact hcode
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

theorem succ_depth_val {e : Fin 1025} (h : e < 1024) : (e + 1).val = e.val + 1 := by
  have hv : e.val < 1024 := by simpa using h
  rw [Fin.val_add_eq_of_add_lt] <;> simp; omega

/-- A `CALL`-family instruction keeps `Holds` when the message call it makes is good. -/
theorem call_holds {Q : CallPreds} {gasCost : Nat}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hQ : ∀ T : ThetaCall, T.e.val = evmState.executionEnv.depth.val + 1 → Q.theta T →
      GoodTheta a P Trusted T)
    (hok : callOk Q gas source recipient t value value' inOffset inSize permission evmState)
    (hH : Holds a P evmState.accountMap)
    (hcode : AccountAddress.ofUInt256 recipient = a →
      CodeOk Trusted (toExecute evmState.accountMap (AccountAddress.ofUInt256 t)))
    (hpre : Holds a P (sendEth (AccountAddress.ofUInt256 recipient)
      (AccountAddress.ofUInt256 source) value true evmState.accountMap))
    (h : call gasCost gas source recipient t value value' inOffset inSize outOffset outSize
      permission evmState = .ok (x, state')) :
    Holds a P state'.accountMap ∧ (SubOk a evmState.substate → SubOk a state'.substate) := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    have hg := hQ _ (succ_depth_val hcall.2)
      (hok (by simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcall))
      (readWithPadding_size_lt _ _ _) hcode hH hpre
    exact ⟨hg.1, fun hS => hg.2 (hS.of_sets ⟨rfl, rfl⟩)⟩
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩

/-- A `CREATE` or `CREATE2` keeps `Holds` when the creation it makes is good. -/
theorem create_holds {Q : CallPreds} {value offset size x : UInt256} {salt : Option ByteArray}
    {evmState state' : State}
    (hown : OwnerOk a P Trusted evmState.executionEnv.codeOwner)
    (hQl : ∀ L : LambdaCall, L.e.val = evmState.executionEnv.depth.val + 1 → Q.lambda L →
      GoodLambda a P L)
    (hok : createOk Q value offset size salt evmState)
    (hH : Holds a P evmState.accountMap)
    (h : create value offset size salt evmState = .ok (x, state')) :
    Holds a P state'.accountMap ∧ (SubOk a evmState.substate → SubOk a state'.substate) := by
  let owner := (evmState.accountMap.get? evmState.executionEnv.codeOwner).getD default
  let σStar := evmState.accountMap.insert evmState.executionEnv.codeOwner
    {owner with nonce := owner.nonce + ⟨1⟩}
  have hStar : Holds a P σStar := by
    refine hH.insert_owner hown.ne_or_codeOnly fun old hold => ?_
    have : owner = old := by
      simp [owner, Std.ExtTreeMap.get?_eq_getElem?, hold]
    rw [this]
  unfold create at h
  by_cases hnonce : owner.nonce.toNat ≥ 2^64 - 1
  · simp [bind, Except.bind, pure, Except.pure] at h
    repeat' (split at h <;> try simp at h)
    all_goals
      first
      | contradiction
      | rcases h with ⟨_, hstate⟩
        rw [← hstate]
        exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩
  · by_cases hCreate :
        value ≤ (evmState.accountMap.get? evmState.executionEnv.codeOwner |>.option ⟨0⟩
          (·.balance)) ∧ evmState.executionEnv.depth < 1024 ∧
          (evmState.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152
    · have hrec := hQl _ rfl (hok hnonce hCreate) hStar (hStar.pay hown.ne_or_codeOnly)
      simp [bind, Except.bind, pure, Except.pure] at h
      repeat' (split at h <;> try simp at h)
      all_goals
        first
        | contradiction
        | rcases h with ⟨_, hstate⟩
          rw [← hstate]
          first
          | exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩
          | exact hrec
    · simp [bind, Except.bind, pure, Except.pure] at h
      repeat' (split at h <;> try simp at h)
      all_goals
        first
        | contradiction
        | rcases h with ⟨_, hstate⟩
          rw [← hstate]
          exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩

theorem getElem?_insert_of_ne {σ : AccountMap} {k k' : AccountAddress} {x : Account}
    (h : k ≠ k') : (σ.insert k x)[k']? = σ[k']? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp [Std.LawfulEqCmp.compare_eq_iff_eq, h]

theorem eq_some_of_liftM {α : Type} {o : Option α} {x : α}
    (h : (liftM o : Except ExecutionException α) = .ok x) : o = some x := by
  cases o with
  | none => cases h
  | some y => cases h; rfl

/-- What `SELFDESTRUCT` does when it names another existing account keeps `Holds`. -/
theorem Holds.selfdestruct (hadm : Admissible P Trusted) {σ : AccountMap}
    {r owner : AccountAddress} {tacc oacc : Account} {b : UInt256}
    (hown : owner ≠ a ∨ CodeOnly P) (hro : r ≠ owner) (hr : σ[r]? = some tacc)
    (ho : σ[owner]? = some oacc) (h : Holds a P σ) :
    Holds a P ((σ.insert r {tacc with balance := tacc.balance + b}).insert owner
      {oacc with balance := ⟨0⟩}) := by
  refine Holds.insert_owner hown (fun old hold => ?_) ?_
  · rw [getElem?_insert_of_ne hro, ho] at hold
    cases hold
    rfl
  by_cases hra : r = a
  · subst hra
    obtain ⟨acc, hacc, hP⟩ := h
    rw [hr] at hacc
    cases hacc
    exact Holds.insert_self (hadm.balance _ b hP)
  · exact h.insert_ne hra

/-- A system instruction keeps `Holds` when the message calls and creations it makes are
    good. -/
theorem step_system (hadm : Admissible P Trusted) {Q : CallPreds} {op : Operation.SOp}
    {gasCost : Nat} {arg : Option (UInt256 × Nat)} {state state' : State}
    (hown : OwnerOk a P Trusted state.executionEnv.codeOwner)
    (hQ : ∀ T : ThetaCall, T.e.val = state.executionEnv.depth.val + 1 → Q.theta T →
      GoodTheta a P Trusted T)
    (hQl : ∀ L : LambdaCall, L.e.val = state.executionEnv.depth.val + 1 → Q.lambda L →
      GoodLambda a P L)
    (hok : stepOk Q gasCost (.System op, arg) state)
    (hH : Holds a P state.accountMap)
    (h : step gasCost (.System op, arg) state = .ok state') :
    Holds a P state'.accountMap ∧ (SubOk a state.substate → SubOk a state'.substate) := by
  have hself : ∀ c,
      AccountAddress.ofUInt256 (UInt256.ofNat ↑state.executionEnv.codeOwner) = a →
        CodeOk Trusted c := by
    intro c hr
    rw [AccountAddress.ofUInt256_ofNat] at hr
    rcases hown with hne | ⟨_, hall⟩
    · exact absurd hr hne
    · exact codeOk_of_all hall c
  have hpay : ∀ v : UInt256,
      Holds a P (sendEth (AccountAddress.ofUInt256 (UInt256.ofNat ↑state.executionEnv.codeOwner))
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑state.executionEnv.codeOwner)) v true
        state.accountMap) := by
    intro v
    rw [AccountAddress.ofUInt256_ofNat]
    exact hH.transfer hadm (hown.elim Or.inl fun h => Or.inr (Or.inr h.1))
  have hsend : ∀ (r : AccountAddress) (v : UInt256),
      Holds a P (sendEth r
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑state.executionEnv.codeOwner)) v true
        state.accountMap) := by
    intro r v
    rw [AccountAddress.ofUInt256_ofNat]
    exact hH.transfer hadm (hown.elim Or.inl fun h => Or.inr (Or.inr h.1))
  cases op
  · -- CREATE
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, value, offset, size⟩
    split at h <;> try contradiction
    rename_i res hcreate
    rcases res with ⟨x, createdState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P createdState.accountMap ∧
      (SubOk a state.substate → SubOk a createdState.substate)
    exact (create_holds (h := hcreate)) hown hQl (hok _ _ _ _ (eq_some_of_liftM hpop)) hH
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
    show Holds a P callState.accountMap ∧
      (SubOk a state.substate → SubOk a callState.substate)
    refine (call_holds (h := hcall)) hQ (hok _ _ _ _ _ _ _ _ (eq_some_of_liftM hpop)) hH ?_
      (hsend _ _)
    intro hr
    rw [hr]
    exact codeOk_toExecute hadm hH
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
    show Holds a P callState.accountMap ∧
      (SubOk a state.substate → SubOk a callState.substate)
    exact (call_holds (h := hcall)) hQ (hok _ _ _ _ _ _ _ _ (eq_some_of_liftM hpop)) hH
      (hself _) (hpay _)
  · -- RETURN
    simp [step] at h
    have hs := sets_binaryMachineStateOp h
    exact ⟨hH.of_eq (by simpa using static_binaryMachineStateOp_accountMap_eq h),
      fun hS => hS.of_sets hs⟩
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
    show Holds a P callState.accountMap ∧
      (SubOk a state.substate → SubOk a callState.substate)
    exact (call_holds (h := hcall)) hQ (hok _ _ _ _ _ _ _ (eq_some_of_liftM hpop)) hH (hself _)
      (hH.transfer hadm (Or.inr (Or.inl rfl)))
  · -- CREATE2
    simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, value, offset, size, salt⟩
    split at h <;> try contradiction
    rename_i res hcreate
    rcases res with ⟨x, createdState⟩
    injection h with hstate
    rw [← hstate]
    show Holds a P createdState.accountMap ∧
      (SubOk a state.substate → SubOk a createdState.substate)
    exact (create_holds (h := hcreate)) hown hQl (hok _ _ _ _ _ (eq_some_of_liftM hpop)) hH
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
    show Holds a P callState.accountMap ∧
      (SubOk a state.substate → SubOk a callState.substate)
    refine (call_holds (h := hcall)) hQ (hok _ _ _ _ _ _ _ (eq_some_of_liftM hpop)) hH ?_
      (hsend _ _)
    intro hr
    rw [hr]
    exact codeOk_toExecute hadm hH
  · -- REVERT
    simp [step] at h
    have hs := sets_binaryMachineStateOp h
    exact ⟨hH.of_eq (by simpa using static_binaryMachineStateOp_accountMap_eq h),
      fun hS => hS.of_sets hs⟩
  · -- INVALID
    simp [step] at h
  · -- SELFDESTRUCT
    refine ⟨?_, fun hS => ?_⟩
    · have hown' := hown.ne_or_codeOnly
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
                    have hto : AccountAddress.ofUInt256 targetWord ≠
                        state.executionEnv.codeOwner := by
                      intro he
                      rw [he, howner'] at htarget
                      cases htarget
                    by_cases hzero : ownerAcc.balance = ({ val := 0 } : UInt256)
                    · simp [hpop, hcreated, howner', htarget, hzero] at h
                      rw [← h]
                      exact hH
                    · simp [hpop, hcreated, howner', htarget, hzero] at h
                      rw [← h]
                      refine (hH.insert_ne hta).insert_owner hown' fun old hold => ?_
                      rw [getElem?_insert_of_ne hto, howner'] at hold
                      cases hold
                      rfl
                | some targetAcc =>
                    by_cases hsame :
                      AccountAddress.ofUInt256 targetWord = state.executionEnv.codeOwner
                    · simp [hpop, hcreated, howner', hsame] at h
                      rw [← h]
                      first
                      | exact hH
                      | refine (hH.insert_owner hown' fun old hold => ?_).insert_owner hown'
                          fun old hold => ?_
                        · rw [howner'] at hold
                          cases hold
                          rfl
                        · simp at hold
                          rw [← hold]
                    · simp [hpop, hcreated, howner', htarget, hsame] at h
                      rw [← h]
                      exact hH.selfdestruct hadm hown' hsame htarget howner'
    · simp [step, Ethereum.State.lookupAccount] at h
      cases hpop : state.machineState.stack.pop with
      | none => simp [hpop] at h
      | some popped =>
        rcases popped with ⟨stack, targetWord⟩
        by_cases hcreated : state.executionEnv.codeOwner ∈ state.substate.createdAccounts
        · simp [hpop, hcreated] at h
          rw [← h]
          exact hS.selfdestruct hcreated
        · simp [hpop, hcreated] at h
          rw [← h]
          exact hS.of_sets ⟨rfl, rfl⟩

/-- One instruction keeps `Holds` when the message calls and creations it makes are good. -/
theorem step_holds (hadm : Admissible P Trusted) {Q : CallPreds} {gasCost : Nat}
    {instr : Operation × Option (UInt256 × Nat)} {state state' : State}
    (hown : OwnerOk a P Trusted state.executionEnv.codeOwner)
    (hQ : ∀ T : ThetaCall, T.e.val = state.executionEnv.depth.val + 1 → Q.theta T →
      GoodTheta a P Trusted T)
    (hQl : ∀ L : LambdaCall, L.e.val = state.executionEnv.depth.val + 1 → Q.lambda L →
      GoodLambda a P L)
    (hok : stepOk Q gasCost instr state)
    (hH : Holds a P state.accountMap)
    (h : step gasCost instr state = .ok state') :
    Holds a P state'.accountMap ∧ (SubOk a state.substate → SubOk a state'.substate) := by
  rcases instr with ⟨op, arg⟩
  have hsets : (∀ s, op ≠ .System s) → SubOk a state.substate → SubOk a state'.substate :=
    fun hop hS => hS.of_sets (step_sets hop h)
  cases op with
  | StopArith op =>
    exact ⟨hH.of_eq (static_step_stoparith_accountMap_eq h), hsets nofun⟩
  | CompBit op => exact ⟨hH.of_eq (static_step_compbit_accountMap_eq h), hsets nofun⟩
  | Keccak op => exact ⟨hH.of_eq (static_step_keccak_accountMap_eq h), hsets nofun⟩
  | Env op => exact ⟨hH.of_eq (static_step_env_accountMap_eq h), hsets nofun⟩
  | Block op => exact ⟨hH.of_eq (static_step_block_accountMap_eq h), hsets nofun⟩
  | StackMemFlow op => exact ⟨step_stackMemFlow hown hH h, hsets nofun⟩
  | Push op => exact ⟨hH.of_eq (static_step_push_accountMap_eq h), hsets nofun⟩
  | Dup op => exact ⟨hH.of_eq (static_step_dup_accountMap_eq h), hsets nofun⟩
  | Exchange op => exact ⟨hH.of_eq (static_step_exchange_accountMap_eq h), hsets nofun⟩
  | Log op => exact ⟨hH.of_eq (static_step_log_accountMap_eq h), hsets nofun⟩
  | System op => exact step_system hadm hown hQ hQl hok hH h

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

theorem Xstep_holds (hadm : Admissible P Trusted) {Q : CallPreds} {validJumps : Array UInt256}
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (hown : OwnerOk a P Trusted state.executionEnv.codeOwner)
    (hQ : ∀ T : ThetaCall, T.e.val = state.executionEnv.depth.val + 1 → Q.theta T →
      GoodTheta a P Trusted T)
    (hQl : ∀ L : LambdaCall, L.e.val = state.executionEnv.depth.val + 1 → Q.lambda L →
      GoodLambda a P L)
    (hok : XstepOk Q validJumps state)
    (hH : Holds a P state.accountMap)
    (hXstep : Xstep validJumps state = .ok (state', ret)) :
    Holds a P state'.accountMap ∧ (SubOk a state.substate → SubOk a state'.substate) := by
  unfold XstepOk at hok
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
      have hokZ := hok stateZ cost hZ'
      obtain ⟨hstateZ, -⟩ := Z_ok_eq_charged_cost hZ'
      subst hstateZ
      have hprefix : Holds a P stepped.accountMap ∧
          (SubOk a state.substate → SubOk a stepped.substate) :=
        (step_holds hadm (h := hStep')) hown hQ hQl hokZ hH
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

theorem X_holds (hadm : Admissible P Trusted) {Q : CallPreds} {f : Nat}
    {validJumps : Array UInt256} {state state' : State} {o : ByteArray}
    (hown : OwnerOk a P Trusted state.executionEnv.codeOwner)
    (hQ : ∀ T : ThetaCall, T.e.val = state.executionEnv.depth.val + 1 → Q.theta T →
      GoodTheta a P Trusted T)
    (hQl : ∀ L : LambdaCall, L.e.val = state.executionEnv.depth.val + 1 → Q.lambda L →
      GoodLambda a P L)
    (hok : XOk Q f validJumps state)
    (hH : Holds a P state.accountMap)
    (hX : X f validJumps state = .ok (.success state' o)) :
    Holds a P state'.accountMap ∧ (SubOk a state.substate → SubOk a state'.substate) := by
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
          have h₁ := Xstep_holds hadm hown hQ hQl hok.1 hH hstep
          rw [hstep] at hX
          cases ret with
          | none =>
              change
                X f validJumps
                    { state₁ with executionEnv.depth := state.executionEnv.depth } =
                  Except.ok (ExecutionResult.success state' o) at hX
              have henv := Xstep_executionEnv_eq hstep
              have htail :=
                (ih (state := { state₁ with executionEnv.depth := state.executionEnv.depth })
                  (hX := hX)) (by simpa [henv] using hown) hQ hQl (hok.2 state₁ hstep) h₁.1
              exact ⟨htail.1, fun hS => htail.2 (h₁.2 hS)⟩
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
                  Except.ok
                      (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                cases hres

/-- **The frame property.**  A frame changes `a`'s account only through the message calls and
    creations it makes and by sending value to `a`, unless it runs at `a`: if those calls keep
    `Holds`, so does the frame.  A frame at `a` is covered too when `P` sees only the code, since
    no instruction changes the code of the running account. -/
theorem Xi_holds (hadm : Admissible P Trusted) {Q : CallPreds} {σ σ₀ σ' : AccountMap}
    {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hown : OwnerOk a P Trusted I.codeOwner)
    (hQ : ∀ T : ThetaCall, T.e.val = I.depth.val + 1 → Q.theta T → GoodTheta a P Trusted T)
    (hQl : ∀ L : LambdaCall, L.e.val = I.depth.val + 1 → Q.lambda L → GoodLambda a P L)
    (hok : XiOk Q σ σ₀ g A I) (hH : Holds a P σ)
    (hXi : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Holds a P σ' ∧ (SubOk a A → SubOk a A') := by
  simp [Ξ] at hXi
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) (xiState σ σ₀ g A I))
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (σ', g', A') o) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) (xiState σ σ₀ g A I) with
  | error err => simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas out => simp [hX, Except.bind] at hXi
      | success evmState' out =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hσ, -, hA⟩, -⟩
          rw [← hσ, ← hA]
          exact X_holds hadm (state := xiState σ σ₀ g A I) hown hQ hQl hok hH hX

end Frame

/-! ## Admission -/

/-- The environment `Θ` runs code `code` in. -/
def ThetaCall.env (T : ThetaCall) (code : ByteArray) : ExecutionEnv :=
  { codeOwner := T.r, sender := T.o, gasPrice := T.p.toNat, calldata := T.d, source := T.s,
    weiValue := T.v', depth := T.e, perm := T.w, code := code, header := T.H,
    blobVersionedHashes := T.bvh, blocks := T.blocks }

/-- The account map `Θ` runs code on, after the value moves. -/
def ThetaCall.σ₁ (T : ThetaCall) : AccountMap := sendEth T.r T.s T.v true T.σ

/-- The address a creation creates at. -/
def LambdaCall.addr (L : LambdaCall) : AccountAddress :=
  Fin.ofNat AccountAddress.size (fromByteArrayBigEndian ((KEC (Lambda.L_A L.s
    (Option.option ⟨0⟩ (fun x => x.nonce) (L.σ.get? L.s) - ⟨1⟩) L.ζ L.i)).extract 12 32))

/-- The account map, substate and environment the init code of a creation runs with, as
    `Lambda` computes them. -/
def LambdaCall.frame (L : LambdaCall) : AccountMap × Substate × ExecutionEnv :=
  let a' := L.addr
  let existentAccount := L.σ.getD a' default
  let (i, createdAccounts) :=
    if existentAccount.nonce ≠ ⟨0⟩ || existentAccount.code.size ≠ 0
        || existentAccount.storage != default then
      (⟨#[0xfe]⟩, L.A.createdAccounts)
    else (L.i, L.A.createdAccounts.insert a')
  let AStar := { L.A.addAccessedAccount a' with createdAccounts := createdAccounts }
  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := L.v + existentAccount.balance }
  let σStar :=
    match L.σ.get? L.s with
    | none => L.σ
    | some ac => L.σ.insert L.s {ac with balance := ac.balance - L.v} |>.insert a' newAccount
  (σStar, AStar,
    { codeOwner := a', sender := L.o, source := L.s, weiValue := L.v, calldata := default,
      code := i, gasPrice := L.p.toNat, header := L.H, depth := L.e, perm := L.w,
      blobVersionedHashes := L.bvh, blocks := L.blocks })

section Admission

variable (a : AccountAddress) (admits : AccountMap → ExecutionEnv → Prop)

/-- A message call's frame, if it runs code and succeeds, is admitted when it runs at `a`, and
    the calls and creations it makes directly satisfy `Q`. -/
def thetaAdm (Q : CallPreds) (T : ThetaCall) : Prop :=
  ∀ code, T.c = .Code code → ∀ σ' g' A' o,
    Ξ T.σ₁ T.σ₀ T.g T.A (T.env code) = .ok (.success (σ', g', A') o) →
    (T.r = a → admits T.σ₁ (T.env code)) ∧ XiOk Q T.σ₁ T.σ₀ T.g T.A (T.env code)

/-- A creation's frame, if it succeeds, makes calls and creations that satisfy `Q`. -/
def lambdaAdm (Q : CallPreds) (L : LambdaCall) : Prop :=
  ∀ σ' g' A' o,
    Ξ L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2 = .ok (.success (σ', g', A') o) →
    XiOk Q L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2

/-- Admission of the calls and creations with `n` levels of depth below them: their frames and,
    recursively, the frames of the calls and creations those make. -/
def Adm : ℕ → CallPreds
  | 0 => ⟨thetaAdm a admits CallPreds.all, lambdaAdm CallPreds.all⟩
  | n + 1 => ⟨thetaAdm a admits (Adm n), lambdaAdm (Adm n)⟩

/-- What the calls and creations made at depth `1024 - n` must satisfy. -/
def admBelow : ℕ → CallPreds
  | 0 => CallPreds.all
  | n + 1 => Adm a admits n

theorem Adm_eq (n : ℕ) :
    Adm a admits n =
      ⟨thetaAdm a admits (admBelow a admits n), lambdaAdm (admBelow a admits n)⟩ := by
  cases n <;> rfl

/-- Every successful frame at `a` in the execution of the message call `T` is admitted. -/
def Admitted (T : ThetaCall) : Prop := (Adm a admits (1024 - T.e.val)).theta T

/-- Every successful frame at `a` in the execution of the creation `L` is admitted. -/
def AdmittedL (L : LambdaCall) : Prop := (Adm a admits (1024 - L.e.val)).lambda L

theorem adm_of_all (htrue : ∀ σ I, admits σ I) (n : ℕ) :
    (∀ T, (Adm a admits n).theta T) ∧ ∀ L, (Adm a admits n).lambda L := by
  have hbelow : ∀ n,
      (∀ T, (admBelow a admits n).theta T) ∧ ∀ L, (admBelow a admits n).lambda L
  · intro n
    induction n with
    | zero => exact ⟨fun _ => trivial, fun _ => trivial⟩
    | succ n ih =>
      rw [admBelow, Adm_eq]
      exact ⟨fun T _ _ _ _ _ _ _ => ⟨fun _ => htrue _ _, XiOk_of_all ih.1 ih.2 _ _ _ _ _⟩,
        fun L _ _ _ _ _ => XiOk_of_all ih.1 ih.2 _ _ _ _ _⟩
  rw [Adm_eq]
  exact ⟨fun T _ _ _ _ _ _ _ => ⟨fun _ => htrue _ _,
      XiOk_of_all (hbelow n).1 (hbelow n).2 _ _ _ _ _⟩,
    fun L _ _ _ _ _ => XiOk_of_all (hbelow n).1 (hbelow n).2 _ _ _ _ _⟩

/-- When `admits` holds of every frame, every execution is admitted. -/
theorem admitted_of_all (htrue : ∀ σ I, admits σ I) :
    (∀ T, Admitted a admits T) ∧ ∀ L, AdmittedL a admits L :=
  ⟨fun T => (adm_of_all a admits htrue _).1 T, fun L => (adm_of_all a admits htrue _).2 L⟩

end Admission

/-! ## The statement -/

section Statement

variable (a : AccountAddress) (P : Account → Prop) (Trusted : ByteArray → Prop)
  (admits : AccountMap → ExecutionEnv → Prop)

/-- Every admitted message call at depth `e` is good. -/
def ThetaGood (e : Fin 1025) : Prop :=
  ∀ T : ThetaCall, T.e = e → Admitted a admits T → GoodTheta a P Trusted T

/-- Every admitted creation at depth `e` is good. -/
def LambdaGood (e : Fin 1025) : Prop :=
  ∀ L : LambdaCall, L.e = e → AdmittedL a admits L → GoodLambda a P L

/-- Every admitted message call and creation deeper than `d` is good. -/
def Deeper (d : Fin 1025) : Prop :=
  ∀ e : Fin 1025, d < e → ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e

/-- The per-frame hypothesis: a successful frame at `a` that is admitted, runs code `Trusted`
    admits, and starts where `Holds` holds, ends with `a`'s account satisfying `P`, if its code is
    still what it was.  The frame may assume that the admitted calls and creations below it are
    good (`Deeper`), and that the ones it makes directly are admitted (`XiOk`). -/
def FrameHyp : Prop :=
  ∀ σ σ₀ g A (I : ExecutionEnv) σ' g' A' o, I.codeOwner = a → Trusted I.code →
    I.calldata.size < UInt256.size → admits σ I → Deeper a P Trusted admits I.depth →
    XiOk (admBelow a admits (1024 - I.depth.val)) σ σ₀ g A I →
    Holds a P σ → Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o) →
    ∀ acc acc', σ[a]? = some acc → σ'[a]? = some acc' → acc'.code = acc.code → P acc'

/-- `FrameHyp`, concluding `Holds` outright, and `SubOk` of the substate. -/
def FrameHolds : Prop :=
  ∀ σ σ₀ g A (I : ExecutionEnv) σ' g' A' o, I.codeOwner = a → Trusted I.code →
    I.calldata.size < UInt256.size → admits σ I → Deeper a P Trusted admits I.depth →
    XiOk (admBelow a admits (1024 - I.depth.val)) σ σ₀ g A I →
    Holds a P σ → Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o) →
      Holds a P σ' ∧ (SubOk a A → SubOk a A')

end Statement

/-- A frame whose code is `INVALID` alone fails. -/
theorem Xi_invalid_ne_success (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hI : I.code = ⟨#[0xfe]⟩) (result : AccountMap × UInt256 × Substate) (out : ByteArray) :
    Ξ σ σ₀ g A I ≠ .ok (.success result out) := by
  intro hXi
  have hstep : Xstep (D_J I.code 0) (xiState σ σ₀ g A I) = .error .InvalidInstruction := by
    have hdec : decode (xiState σ σ₀ g A I).executionEnv.code
        (xiState σ σ₀ g A I).machineState.pc = some (.INVALID, .none) := by
      show decode I.code ({ val := 0 } : UInt256) = some (.INVALID, .none)
      rw [hI]
      decide
    simp [Xstep, Z, δ, hdec]
  have hX : X (g.toNat + 1) (D_J I.code 0) (xiState σ σ₀ g A I) = .error .InvalidInstruction := by
    simp [X, hstep]; rfl
  simp [Ξ] at hXi
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) (xiState σ σ₀ g A I)) _ = _ at hXi
  rw [hX] at hXi
  cases hXi


/-- The address a creation targets already has a nonce, code or storage, so its init code is
    replaced by `INVALID` (EIP-7610). -/
def LambdaCall.blocked (L : LambdaCall) : Bool :=
  let ex := L.σ.getD L.addr default
  ex.nonce ≠ ⟨0⟩ || ex.code.size ≠ 0 || ex.storage != default

theorem LambdaCall.frame_code (L : LambdaCall) :
    L.frame.2.2.code = if L.blocked then ⟨#[0xfe]⟩ else L.i := by
  unfold LambdaCall.frame LambdaCall.blocked
  simp only
  split_ifs <;> rfl

theorem LambdaCall.blocked_of_addr {a : AccountAddress} {P : Account → Prop}
    {Trusted : ByteArray → Prop} (hadm : Admissible P Trusted) {L : LambdaCall}
    (hH : Holds a P L.σ) (ha : L.addr = a) : L.blocked = true := by
  obtain ⟨acc, hacc, hP⟩ := hH
  have hc := hadm.code acc hP
  unfold LambdaCall.blocked
  rw [ha, Std.ExtTreeMap.getD_eq_getD_getElem?, hacc]
  simp [hc]

/-- The substate a creation's init code starts from keeps `a` out of the created accounts: it
    lists the new address only when that address had no code, which `a` has. -/
theorem LambdaCall.frame_subOk {a : AccountAddress} {P : Account → Prop}
    {Trusted : ByteArray → Prop} (hadm : Admissible P Trusted) {L : LambdaCall}
    (hH : Holds a P L.σ) (hS : SubOk a L.A) : SubOk a L.frame.2.1 := by
  by_cases ha : L.addr = a
  · have hb := L.blocked_of_addr hadm hH ha
    unfold LambdaCall.blocked at hb
    unfold LambdaCall.frame
    simp only
    rw [if_pos hb]
    exact hS
  · unfold LambdaCall.frame
    simp only
    split_ifs
    · exact hS
    · refine ⟨fun hmem => ?_, hS.2⟩
      rcases Batteries.RBSet.mem_toList_insert.mp hmem with ⟨hmem, -⟩ | heq
      · exact hS.1 hmem
      · exact ha heq.symm

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

theorem SubOk.thetaXi {a : AccountAddress} {A : Substate}
    {xi : Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))}
    (hS : SubOk a A)
    (hxi : ∀ {σ' g' A' out}, xi = .ok (.success (σ', g', A') out) → SubOk a A') :
    SubOk a (thetaXiSubstate A xi) := by
  unfold thetaXiSubstate thetaXiResult
  split
  · simpa using hS
  · simpa using hS
  · dsimp only
    split
    · exact hS
    · exact hxi rfl

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
    · rw [if_pos (by rw [h]; exact accountMap_empty_beq_empty)]
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


section Proof

variable {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
  {admits : AccountMap → ExecutionEnv → Prop}

/-- What `Deeper` gives the calls a frame at depth `d` makes. -/
theorem Deeper.theta {d : Fin 1025} (hdeep : Deeper a P Trusted admits d) (T : ThetaCall)
    (he : T.e.val = d.val + 1) (hT : (admBelow a admits (1024 - d.val)).theta T) :
    GoodTheta a P Trusted T := by
  have hlt := T.e.isLt
  have hm : 1024 - d.val = (1024 - T.e.val) + 1 := by omega
  rw [hm] at hT
  exact (hdeep T.e (by rw [Fin.lt_def]; omega)).1 T rfl hT

/-- What `Deeper` gives the creations a frame at depth `d` makes. -/
theorem Deeper.lambda {d : Fin 1025} (hdeep : Deeper a P Trusted admits d) (L : LambdaCall)
    (he : L.e.val = d.val + 1) (hL : (admBelow a admits (1024 - d.val)).lambda L) :
    GoodLambda a P L := by
  have hlt := L.e.isLt
  have hm : 1024 - d.val = (1024 - L.e.val) + 1 := by omega
  rw [hm] at hL
  exact (hdeep L.e (by rw [Fin.lt_def]; omega)).2 L rfl hL

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

/-- An admitted creation keeps `Holds` if the admitted calls and creations below it do.  One
    that lands on `a` fails, since `a` has code, and leaves the account map as it was. -/
theorem lambda_good (hadm : Admissible P Trusted) {e : Fin 1025}
    (hdeep : Deeper a P Trusted admits e) : LambdaGood a P admits e := by
  intro L he hadmL hH hdebit
  subst he
  have hAS : SubOk a L.A → SubOk a L.frame.2.1 := L.frame_subOk hadm hH
  obtain ⟨σ, σ₀, A, s, o, g, p, v, i, e, ζ, H, bvh, blocks, w⟩ := L
  unfold AdmittedL at hadmL
  rw [Adm_eq] at hadmL
  show Holds a P (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.1 ∧
    (SubOk a A → SubOk a (Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w).2.2.2.1)
  generalize hr : Lambda σ σ₀ A s o g p v i e ζ H bvh blocks w = r
  unfold Lambda at hr
  simp only at hr
  split at hr
  · subst hr
    exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩
  · subst hr
    exact ⟨hH, fun hS => hS.of_sets ⟨rfl, rfl⟩⟩
  · rename_i σSS gSS ASS out hXi
    subst hr
    have hok := hadmL _ _ _ _ hXi
    by_cases ha' : Fin.ofNat AccountAddress.size (fromByteArrayBigEndian ((KEC (Lambda.L_A s
        (Option.option ⟨0⟩ (fun x => x.nonce) (σ.get? s) - ⟨1⟩) ζ i)).extract 12 32)) = a
    · let L : LambdaCall := ⟨σ, σ₀, A, s, o, g, p, v, i, e, ζ, H, bvh, blocks, w⟩
      have hb := L.blocked_of_addr hadm hH ha'
      exact absurd hXi (Xi_invalid_ne_success L.frame.1 σ₀ g L.frame.2.1 L.frame.2.2
        (by rw [L.frame_code, hb]; rfl) _ _)
    · have hf := (Xi_holds hadm (hXi := hXi)) (Or.inl ha') (hdeep.theta) (hdeep.lambda) hok
        (Holds.lambdaStar ha' hdebit)
      exact ⟨Holds.ite hH (hf.1.insert_ne ha'),
        fun hS => SubOk.ite (hAS hS) (hf.2 (hAS hS))⟩

/-- An admitted message call keeps `Holds` if the admitted calls and creations below it do: by
    the per-frame hypothesis when it runs code at `a`, by the frame property otherwise. -/
theorem theta_good (hadm : Admissible P Trusted) (hframe : FrameHolds a P Trusted admits)
    {e : Fin 1025} (hdeep : Deeper a P Trusted admits e) : ThetaGood a P Trusted admits e := by
  intro T he hadmT hd hcode hH hpre
  subst he
  obtain ⟨σ, σ₀, A, s, o, r, c, g, p, v, v', d, e, H, bvh, blocks, w⟩ := T
  unfold Admitted at hadmT
  rw [Adm_eq] at hadmT
  show Holds a P (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).1 ∧
    (SubOk a A → SubOk a (Θ σ σ₀ A s o r c g p v v' d e H bvh blocks w).2.2.1)
  cases c with
  | Precompiled pc =>
    refine ⟨?_, fun hS => by rw [precompiled_Theta_substate]; exact hS⟩
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
    rw [code_Theta_accountMap_eq', code_Theta_substate_eq]
    have hrun : ∀ {σ' g' A' out}, Ξ (sendEth r s v true σ) σ₀ g A
        { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d, source := s,
          weiValue := v', depth := e, perm := w, code := code, header := H,
          blobVersionedHashes := bvh, blocks := blocks } = .ok (.success (σ', g', A') out) →
        Holds a P σ' ∧ (SubOk a A → SubOk a A') := by
      intro σ' g' A' out hxi
      obtain ⟨hadmits, hok⟩ := hadmT code rfl _ _ _ _ hxi
      by_cases hr : r = a
      · refine hframe _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ hpre hxi
        · exact hr
        · exact hcode hr
        · exact hd
        · exact hadmits hr
        · exact hdeep
        · exact hok
      · exact (Xi_holds hadm (hXi := hxi)) (Or.inl hr) hdeep.theta hdeep.lambda hok hpre
    exact ⟨hH.thetaXi fun hxi => (hrun hxi).1, fun hS => hS.thetaXi fun hxi => (hrun hxi).2 hS⟩

/-- The induction on the depth left below a call, from `FrameHolds`. -/
theorem good_core (hadm : Admissible P Trusted) (hframe : FrameHolds a P Trusted admits)
    (e : Fin 1025) : ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e := by
  suffices key : ∀ n, ∀ e : Fin 1025, 1024 - e.val ≤ n →
      ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e from key _ e le_rfl
  intro n
  induction n with
  | zero =>
    intro e he
    have hdeep : Deeper a P Trusted admits e := fun e' he' => by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega
    exact ⟨theta_good hadm hframe hdeep, lambda_good hadm hdeep⟩
  | succ n ih =>
    intro e he
    have hdeep : Deeper a P Trusted admits e := fun e' he' => ih e' (by
      have := e'.isLt
      rw [Fin.lt_def] at he'
      omega)
    exact ⟨theta_good hadm hframe hdeep, lambda_good hadm hdeep⟩

end Proof

/-! ## The code at `a` -/

theorem codeOnly_code (c : ByteArray) : CodeOnly (fun acc : Account => acc.code = c) :=
  fun _ _ he h => he.symm.trans h

theorem admissible_code {c : ByteArray} (hc : c.size ≠ 0) :
    Admissible (fun acc : Account => acc.code = c) (fun _ => True) :=
  ⟨fun _ _ h => h, fun _ h => h ▸ hc, fun _ _ => trivial⟩

/-- **No call changes the code at `a`.**  Every message call and creation, at every depth,
    whatever runs, keeps `a`'s account present with code `c`, if it is to begin with and `c` is
    not empty. -/
theorem code_good (a : AccountAddress) {c : ByteArray} (hc : c.size ≠ 0) (e : Fin 1025) :
    ThetaGood a (·.code = c) (fun _ => True) (fun _ _ => True) e
      ∧ LambdaGood a (·.code = c) (fun _ _ => True) e :=
  good_core (admissible_code hc)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hdeep hok hH hXi =>
      Xi_holds (admissible_code hc) (Or.inr ⟨codeOnly_code c, fun _ => trivial⟩)
        hdeep.theta hdeep.lambda hok hH hXi) e

/-- A frame keeps the code at `a`, whatever it runs, and keeps `a` out of the created accounts and
    the self-destruct set. -/
theorem Xi_code {a : AccountAddress} {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {acc : Account} (hc : acc.code.size ≠ 0)
    (hacc : σ[a]? = some acc) (hXi : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    (∃ acc', σ'[a]? = some acc' ∧ acc'.code = acc.code) ∧ (SubOk a A → SubOk a A') :=
  Xi_holds (admissible_code hc) (Q := CallPreds.all)
    (Or.inr ⟨codeOnly_code _, fun _ => trivial⟩)
    (fun T _ _ => (code_good a hc T.e).1 T rfl
      ((admitted_of_all a (fun _ _ => True) fun _ _ => trivial).1 T))
    (fun L _ _ => (code_good a hc L.e).2 L rfl
      ((admitted_of_all a (fun _ _ => True) fun _ _ => trivial).2 L))
    (XiOk_of_all (fun _ => trivial) (fun _ => trivial) _ _ _ _ _) ⟨acc, hacc, rfl⟩ hXi

/-! ## The theorem -/

/-- **Every admitted message call and creation keeps the invariant.**  If `P` is admissible and
    every admitted frame at `a` running trusted code keeps it whenever the admitted calls and
    creations below it do, then at every depth every message call and creation whose execution
    admits every successful frame at `a` does, by induction on the depth left below it. -/
theorem good {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
    {admits : AccountMap → ExecutionEnv → Prop} (hadm : Admissible P Trusted)
    (hframe : FrameHyp a P Trusted admits) (e : Fin 1025) :
    ThetaGood a P Trusted admits e ∧ LambdaGood a P admits e := by
  refine good_core hadm ?_ e
  intro σ σ₀ g A I σ' g' A' o howner htr hcd hadmits hdeep hok hH hXi
  obtain ⟨acc, hacc, hP⟩ := id hH
  obtain ⟨⟨acc', hacc', hcode⟩, hsub⟩ := Xi_code (hadm.code acc hP) hacc hXi
  exact ⟨⟨acc', hacc', hframe σ σ₀ g A I σ' g' A' o howner htr hcd hadmits hdeep hok hH hXi
    acc acc' hacc hacc' hcode⟩, hsub⟩

/-! ## Deployment -/

theorem lambda_addr (L : LambdaCall) : L.run.1 = L.addr := by
  obtain ⟨σ, σ₀, A, s, o, g, p, v, i, e, ζ, H, bvh, blocks, w⟩ := L
  simp only [LambdaCall.run, LambdaCall.addr]
  unfold Lambda
  simp only
  split <;> rfl


theorem LambdaCall.frame_storage (L : LambdaCall) (h : L.blocked = false) :
    (L.frame.1.getD L.addr default).storage = default := by
  unfold LambdaCall.blocked at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not,
    bne_eq_false_iff_eq] at h
  unfold LambdaCall.frame
  simp only
  split
  · exact h.2
  · rw [Std.ExtTreeMap.getD_insert_self]
    exact h.2

/-- A creation that succeeds ran its init code, from an account with empty storage at the new
    address, and installed the code the init code returned. -/
theorem lambda_success {L : LambdaCall} (hz : L.run.2.2.2.2.1 = true) :
    L.frame.2.2.code = L.i ∧ (L.frame.1.getD L.addr default).storage = default ∧
    ∃ σSS gSS ASS o,
      Ξ L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2 = .ok (.success (σSS, gSS, ASS) o) ∧
      L.run.2.1 = σSS.insert L.addr {σSS.getD L.addr default with code := o} := by
  generalize hr : L.run = r at hz ⊢
  unfold LambdaCall.run Lambda at hr
  simp only at hr
  split at hr
  · subst hr
    simp at hz
  · subst hr
    simp at hz
  · rename_i σSS gSS ASS out hXi
    subst hr
    have hb : L.blocked = false := by
      cases hb : L.blocked
      · rfl
      · exact absurd hXi (Xi_invalid_ne_success L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2
          (by rw [L.frame_code, hb]; rfl) _ _)
    refine ⟨by rw [L.frame_code, hb]; rfl, L.frame_storage hb, σSS, gSS, ASS, out, hXi, ?_⟩
    simp only at hz
    show (if _ then L.σ else _) = _
    rw [if_neg (by intro hc; rw [hc] at hz; simp at hz)]
    rfl

/-- **Deployment.**  A creation that succeeds ends where `Holds` holds at the address it created, if
    the account its init code leaves there, with the code the init code returns, satisfies `P`. -/
theorem deploy_holds {P : Account → Prop} {L : LambdaCall}
    (hframe : ∀ σSS gSS ASS o,
      Ξ L.frame.1 L.σ₀ L.g L.frame.2.1 L.frame.2.2 = .ok (.success (σSS, gSS, ASS) o) →
      P {σSS.getD L.addr default with code := o})
    (hz : L.run.2.2.2.2.1 = true) : L.run.1 = L.addr ∧ Holds L.addr P L.run.2.1 := by
  obtain ⟨-, -, σSS, gSS, ASS, o, hXi, hrun⟩ := lambda_success hz
  exact ⟨lambda_addr L, hrun ▸ Holds.insert_self (hframe _ _ _ _ hXi)⟩

/-! ## The transaction -/

/-- The outermost message call or creation of a transaction, as `Υ` makes it. -/
def txCall (σ : AccountMap) (H_f : ℕ) (H : BlockHeader) (blocks : ProcessedBlocks)
    (T : Transaction) (S_T : AccountAddress) : ThetaCall ⊕ LambdaCall :=
  let g₀ : ℕ := EVM.intrinsicGas T
  let senderAccount := (σ.get? S_T).get!
  let f :=
    match T with
      | .legacy t | .access t => t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t => min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  let p :=
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)
        nonce := senderAccount.nonce + ⟨1⟩ }
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a :=
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ :=
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar :=
    { A0 with
      accessedAccounts := AStarₐ
      accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp }
  match T.base.recipient with
  | none => .inr
      { σ := σ₀, σ₀ := σ₀, A := AStar, s := S_T, o := S_T, g := g, p := p, v := T.base.value,
        i := T.base.data, e := 0, ζ := none, H := H, bvh := T.blobVersionedHashes,
        blocks := blocks, w := true }
  | some t => .inl
      { σ := σ₀, σ₀ := σ₀, A := AStar, s := S_T, o := S_T, r := t, c := toExecute σ₀ t, g := g,
        p := p, v := T.base.value, v' := T.base.value, d := T.base.data, e := 0, H := H,
        bvh := T.blobVersionedHashes, blocks := blocks, w := true }

section Tx

variable {a : AccountAddress} {P : Account → Prop} {Trusted : ByteArray → Prop}
  {admits : AccountMap → ExecutionEnv → Prop}

theorem Holds.erase_ne {σ : AccountMap} {k : AccountAddress} (hk : k ≠ a) (h : Holds a P σ) :
    Holds a P (σ.erase k) := by
  obtain ⟨acc, hacc, hP⟩ := h
  refine ⟨acc, ?_, hP⟩
  rw [Std.ExtTreeMap.getElem?_erase]
  simp [Std.LawfulEqCmp.compare_eq_iff_eq, hk, hacc]

theorem Holds.foldl_erase {l : List AccountAddress} (hl : a ∉ l) {σ : AccountMap}
    (h : Holds a P σ) : Holds a P (l.foldl Std.ExtTreeMap.erase σ) := by
  induction l generalizing σ with
  | nil => exact h
  | cons x l ih =>
    simp only [List.mem_cons, not_or] at hl
    exact ih hl.2 (h.erase_ne (Ne.symm hl.1))

theorem mem_toList_filter {t : Batteries.RBSet AccountAddress compare} {p : AccountAddress → Bool}
    {x : AccountAddress} (hx : x ∈ (t.filter p).toList) : p x = true := by
  unfold Batteries.RBSet.filter at hx
  rw [Batteries.RBSet.foldl_eq_foldl_toList] at hx
  suffices key : ∀ (l : List AccountAddress) (acc : Batteries.RBSet AccountAddress compare),
      (∀ y ∈ acc.toList, p y = true) →
      ∀ y ∈ (l.foldl (fun acc a => bif p a then acc.insert a else acc) acc).toList, p y = true
    from key _ ∅ (fun y hy => by cases hy) x hx
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons v l ih =>
    intro acc h
    apply ih
    cases hv : p v
    · simpa [hv] using h
    · intro y hy
      simp only [hv, cond_true] at hy
      rcases Batteries.RBSet.mem_toList_insert.mp hy with ⟨hy, -⟩ | rfl
      · exact h y hy
      · exact hv

theorem Holds.not_dead (hadm : Admissible P Trusted) {σ : AccountMap} (h : Holds a P σ) :
    State.dead σ a = false := by
  obtain ⟨acc, hacc, hP⟩ := h
  have hc := hadm.code acc hP
  have hne : acc.code ≠ ByteArray.empty := fun h0 => hc (by rw [h0]; rfl)
  simp [State.dead, hacc, Option.option, Account.emptyAccount, ByteArray.isEmpty, hne]

theorem Holds.increaseBalance (hadm : Admissible P Trusted) {σ : AccountMap}
    {k : AccountAddress} {v : UInt256} (h : Holds a P σ) : Holds a P (σ.increaseBalance k v) := by
  unfold AccountMap.increaseBalance
  split
  · rename_i hk
    refine h.insert_ne fun hka => ?_
    subst hka
    obtain ⟨_, hacc, _⟩ := h.get
    rw [hk] at hacc
    cases hacc
  · rename_i acc hk
    by_cases hka : k = a
    · subst hka
      obtain ⟨acc', hacc, hP⟩ := h.get
      rw [hk] at hacc
      cases hacc
      exact Holds.insert_self (hadm.balance _ v hP)
    · exact h.insert_ne hka

theorem Holds.clearTransient
    (htstore : ∀ acc, P acc → P {acc with tstorage := Std.ExtTreeMap.empty}) {σ : AccountMap}
    (h : Holds a P σ) :
    Holds a P (σ.map fun _ acc => {acc with tstorage := Std.ExtTreeMap.empty}) := by
  obtain ⟨acc, hacc, hP⟩ := h
  exact ⟨_, by rw [Std.ExtTreeMap.getElem?_map, hacc]; rfl, htstore acc hP⟩

/-- What `Υ` does after the message call or creation: refund and fee, the self-destruct set and
    dead accounts removed, transient storage cleared. -/
theorem Holds.txTail (hadm : Admissible P Trusted)
    (htstore : ∀ acc, P acc → P {acc with tstorage := Std.ExtTreeMap.empty})
    {X : AccountMap} {A : Substate} (hX : Holds a P X) (hsd : a ∉ A.selfDestructSet.toList) :
    Holds a P ((Batteries.RBSet.foldl Std.ExtTreeMap.erase
      (Batteries.RBNode.foldl Std.ExtTreeMap.erase X A.selfDestructSet.1)
      (A.touchedAccounts.filter fun x => State.dead X x)).map
        fun _ acc => {acc with tstorage := Std.ExtTreeMap.empty}) := by
  refine Holds.clearTransient htstore ?_
  rw [Batteries.RBSet.foldl_eq_foldl_toList]
  refine Holds.foldl_erase (fun hmem => ?_) ?_
  · have := mem_toList_filter hmem
    rw [hX.not_dead hadm] at this
    cases this
  · rw [Batteries.RBNode.foldl_eq_foldl_toList]
    exact Holds.foldl_erase hsd hX

/-- The outermost call or creation of the transaction is admitted. -/
def TxAdmitted (a : AccountAddress) (admits : AccountMap → ExecutionEnv → Prop)
    (σ : AccountMap) (H_f : ℕ) (H : BlockHeader) (blocks : ProcessedBlocks) (T : Transaction)
    (S_T : AccountAddress) : Prop :=
  match txCall σ H_f H blocks T S_T with
  | .inl C => Admitted a admits C
  | .inr L => AdmittedL a admits L

theorem tx_holds (hadm : Admissible P Trusted) (hframe : FrameHyp a P Trusted admits)
    (htstore : ∀ acc, P acc → P {acc with tstorage := Std.ExtTreeMap.empty})
    {σ σ' : AccountMap} {H_f : ℕ} {H : BlockHeader} {blocks : ProcessedBlocks}
    {T : Transaction} {S_T : AccountAddress} {A : Substate} {z : Bool} {gu : UInt256}
    (hH : Holds a P σ)
    (hsender : ∀ acc, σ[S_T]? = some acc → acc.code = .empty)
    (hdata : T.base.data.size < UInt256.size)
    (hadmit : TxAdmitted a admits σ H_f H blocks T S_T)
    (hΥ : Υ σ H_f H blocks T S_T = .ok (σ', A, z, gu)) :
    Holds a P σ' := by
  have hA0 : ∀ X Y, SubOk a { A0 with accessedAccounts := X, accessedStorageKeys := Y } :=
    fun _ _ => ⟨nofun, nofun⟩
  have hSa : S_T ≠ a := by
    rintro rfl
    obtain ⟨acc, hacc, hP⟩ := hH
    exact hadm.code acc hP (by rw [hsender acc hacc]; rfl)
  unfold TxAdmitted txCall at hadmit
  unfold Υ at hΥ
  simp only [bind, Except.bind, pure, Except.pure] at hΥ
  split at hΥ
  · rename_i hr
    simp only [hr] at hadmit hΥ
    injection hΥ with hΥ
    injection hΥ with h1 h2
    injection h2 with h2 _
    have hL := (good hadm hframe 0).2 _ rfl hadmit (hH.insert_ne hSa)
      ((hH.insert_ne hSa).pay (Or.inl hSa))
    rw [← h1]
    refine Holds.txTail hadm htstore (Holds.ite ?_ ?_) (hL.2 (hA0 _ _)).2
    all_goals first
      | exact hL.1.increaseBalance hadm
      | exact (hL.1.increaseBalance hadm).increaseBalance hadm
  · rename_i t hr
    simp only [hr] at hadmit hΥ
    injection hΥ with hΥ
    injection hΥ with h1 h2
    injection h2 with h2 _
    have hC := (good hadm hframe 0).1 _ rfl hadmit hdata
      (fun ht => by rw [show t = a from ht]; exact codeOk_toExecute hadm (hH.insert_ne hSa))
      (hH.insert_ne hSa) ((hH.insert_ne hSa).transfer hadm (Or.inl hSa))
    rw [← h1]
    refine Holds.txTail hadm htstore (Holds.ite ?_ ?_) (hC.2 (hA0 _ _)).2
    all_goals first
      | exact hC.1.increaseBalance hadm
      | exact (hC.1.increaseBalance hadm).increaseBalance hadm

end Tx

end Ethereum.EVM.Invariant
