import Ethereum.Theory.StaticStorage
import Fe.EVM.World

/-!
# External calls of a Fe model

The model counts no gas and keeps no substate, so it cannot compute what the EVM passes to a
callee.  The world carries a feed of those inputs, one `Supply` for each time the model consults
its context.  With them a message call is EVMLean's own `Θ` and a creation its own `Lambda`, on
the model's account map: whatever the callee does, to this contract's storage as well, is in
their result.

What stays loose: a callee gets some gas no more than the call's gas argument, plus the stipend
when value moves; `gas()` reads some word; the substate and the original account map handed to
a callee are whatever the feed holds.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM

/-! ## The feed -/

/-- Consult the context: take the next entry of the feed.  A run that asks for more than the
    feed holds does not terminate, so it agrees with no result of the bytecode. -/
def next : FeM Supply := do
  let w ← get
  match w.feed with
  | [] => Fe.M.diverge
  | s :: rest => set { w with feed := rest }; return s

/-- `gas()`: some word, the next entry's.  The model has no gas to count. -/
def gas : FeM UInt256 := do return (← next).gas

/-! ## Return data -/

/-- `returndatasize()`: the size of the last call's or creation's return data. -/
def returndatasize : FeM UInt256 := do return UInt256.ofNat (← get).returnData.size

/-- `returndatacopy(dest, offset, len)`: copy `len` bytes of the return data from `offset` into
    memory at `dest`.  A read past the end of the return data halts, as on the EVM. -/
def returndatacopy (dest offset len : UInt256) : FeM Unit := do
  let w ← get
  if offset.toNat + len.toNat > w.returnData.size then Fe.M.fail .oob
  else set { w with memory := w.returnData.write offset.toNat w.memory dest.toNat len.toNat }

/-! ## Message calls -/

/-- The gas a message call forwards: at most `cap`, at most the call's gas argument, plus the
    stipend when value moves.  The EVM's `cap` is all but one 64th of what is left; the model's
    is the feed's. -/
def forwardedGas (cap gasArg value : UInt256) : UInt256 :=
  .ofNat (min cap.toNat gasArg.toNat + if value = ⟨0⟩ then 0 else GasConstants.Gcallstipend)

/-- The log entries a callee appended to the substate it was given.  Assumes the callee's
    substate extends the one it was given, as `Θ`'s does. -/
def appended (before after : Substate) : LogSeries :=
  after.logSeries.extract before.logSeries.size

/-- The message call the EVM makes for `CALL`, `STATICCALL` and `DELEGATECALL`: `source` calls
    `recipient`, running the code at `t`, moving `value` and showing the callee `value'`.  It
    takes one entry of the feed, whether or not a call is made: without the funds, or at depth
    1024, none is, and the result is zero with empty return data.  Returns one if the callee
    succeeded and zero otherwise; the first `retLen` bytes of the return data go to memory at
    `retPtr`. -/
def message (gasArg : UInt256) (source recipient t : AccountAddress) (value value' : UInt256)
    (argsPtr argsLen retPtr retLen : UInt256) (perm : Bool) : FeM UInt256 := do
  let I ← read
  let s ← next
  let w ← get
  let σ := w.accounts
  let (σ', _, A', z, o) :=
    if value ≤ (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024 then
      Θ σ s.orig s.substate source I.sender recipient (toExecute σ t)
        (forwardedGas s.gas gasArg value) (.ofNat I.gasPrice) value value'
        (w.memory.readWithPadding argsPtr.toNat argsLen.toNat) (I.depth + 1) I.header
        I.blobVersionedHashes I.blocks perm
    else (σ, ⟨0⟩, s.substate, false, ByteArray.empty)
  set { w with
    accounts := σ'
    logs := w.logs ++ appended s.substate A'
    memory := o.write 0 w.memory retPtr.toNat (min retLen (.ofNat o.size)).toNat
    returnData := o }
  return if z then ⟨1⟩ else ⟨0⟩

/-- `call(gas, addr, value, args_offset, args_len, ret_offset, ret_len)`: call the account
    `addr` with `value` and the `args_len` bytes of memory at `args_offset`.  Under a static
    call it fails if it moves value. -/
def call (gas addr value argsPtr argsLen retPtr retLen : UInt256) : FeM UInt256 := do
  let I ← read
  if I.perm = false ∧ value ≠ ⟨0⟩ then Fe.M.fail .static
  else
    let t := AccountAddress.ofUInt256 addr
    message gas I.codeOwner t t value value argsPtr argsLen retPtr retLen I.perm

/-- `staticcall(gas, addr, args_offset, args_len, ret_offset, ret_len)`: a call with no value in
    which the callee may change nothing. -/
def staticcall (gas addr argsPtr argsLen retPtr retLen : UInt256) : FeM UInt256 := do
  let I ← read
  let t := AccountAddress.ofUInt256 addr
  message gas I.codeOwner t t ⟨0⟩ ⟨0⟩ argsPtr argsLen retPtr retLen false

/-- `staticcall_precompile(gas, addr, args_offset, args_len, ret_offset, ret_len)`: a
    `STATICCALL`.  Only Fe's borrow checker tells it from `staticcall`. -/
def staticcallPrecompile (gas addr argsPtr argsLen retPtr retLen : UInt256) : FeM UInt256 :=
  staticcall gas addr argsPtr argsLen retPtr retLen

/-- `delegatecall(gas, addr, args_offset, args_len, ret_offset, ret_len)`: the code at `addr`
    runs as this contract, for this call's caller and value. -/
def delegatecall (gas addr argsPtr argsLen retPtr retLen : UInt256) : FeM UInt256 := do
  let I ← read
  message gas I.source I.codeOwner (AccountAddress.ofUInt256 addr) ⟨0⟩ I.weiValue argsPtr argsLen
    retPtr retLen I.perm

/-! ## Creations -/

/-- `CREATE` and `CREATE2`: run the `len` bytes of memory at `ptr` as init code, with the gas of
    the feed's next entry.  Returns the new contract's address, or zero when the creation fails
    or is not made: for want of funds, at depth 1024, or with this contract's nonce at its
    limit.  Under a static call it fails.  Init code above 49152 bytes runs out of gas on the
    EVM, so the model does not terminate. -/
def createWith (salt : Option ByteArray) (value ptr len : UInt256) : FeM UInt256 := do
  let I ← read
  if I.perm = false then Fe.M.fail .static
  else if len > ⟨49152⟩ then Fe.M.diverge
  else
    let s ← next
    let w ← get
    let σ := w.accounts
    let init := w.memory.readWithPadding ptr.toNat len.toNat
    let self : Account := σ.get? I.codeOwner |>.getD default
    if h : self.nonce.toNat < 2 ^ 64 - 1
        ∧ value ≤ (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
        ∧ init.size ≤ 49152 then
      match Lambda (σ.insert I.codeOwner { self with nonce := self.nonce + ⟨1⟩ }) s.orig s.substate
          I.codeOwner I.sender s.gas (.ofNat I.gasPrice) value init
          ⟨I.depth.val + 1, Nat.succ_lt_succ h.2.2.1⟩ salt I.header I.blobVersionedHashes
          I.blocks I.perm with
      | (a, σ', _, A', z, o) =>
        set { w with
          accounts := σ'
          logs := w.logs ++ appended s.substate A'
          returnData := if z then ByteArray.empty else o }
        return if z then UInt256.ofNat a else ⟨0⟩
    else
      set { w with returnData := ByteArray.empty }
      return ⟨0⟩

/-- `create(value, offset, len)`: create a contract from the init code in memory. -/
def create (value ptr len : UInt256) : FeM UInt256 := createWith none value ptr len

/-- `create2(value, offset, len, salt)`: as `create`, at the address that is the last 20 bytes
    of `keccak256(0xff ++ self ++ salt ++ keccak256(init))`. -/
def create2 (value ptr len salt : UInt256) : FeM UInt256 :=
  createWith (some salt.toByteArray) value ptr len

/-! ## The code of other accounts -/

/-- `extcodehash(addr)`: the hash of an account's code, zero for an account that is dead. -/
def extcodehash (addr : UInt256) : FeM UInt256 := do
  let σ := (← get).accounts
  let a := AccountAddress.ofUInt256 addr
  return if State.dead σ a then ⟨0⟩ else σ.get? a |>.option ⟨0⟩ Account.codeHash

/-- `extcodecopy(addr, dest, offset, len)`: copy `len` bytes of an account's code from `offset`
    into memory at `dest`, zeros past its end. -/
def extcodecopy (addr dest offset len : UInt256) : FeM Unit := do
  let w ← get
  let code := w.accounts.get? (AccountAddress.ofUInt256 addr) |>.option ByteArray.empty (·.code)
  set { w with memory := code.write offset.toNat w.memory dest.toNat len.toNat }

/-! ## Self-destruction -/

/-- `selfdestruct(addr)`: send the balance to `addr` and end the call.  Whether a balance sent
    to oneself is burnt depends on whether this transaction created the contract, which the
    feed's substate records.

    Exported code cannot call it, so the name is protected: Fe's std never self-destructs, and
    EquiVM has no trace lemma for `SELFDESTRUCT` to certify a model that does.  The definition
    records what the instruction would mean here. -/
protected def selfdestruct (addr : UInt256) : FeM Empty := do
  let I ← read
  if I.perm = false then Fe.M.fail .static
  else
    let s ← next
    let w ← get
    let σ := w.accounts
    let r := AccountAddress.ofUInt256 addr
    let σ' :=
      match σ.get? I.codeOwner with
      | none => σ
      | some self =>
        match σ.get? r with
        | none =>
          if self.balance == ⟨0⟩ then σ
          else (σ.insert r { (default : Account) with balance := self.balance }).insert I.codeOwner
            { self with balance := ⟨0⟩ }
        | some dst =>
          if r ≠ I.codeOwner then
            (σ.insert r { dst with balance := dst.balance + self.balance }).insert I.codeOwner
              { self with balance := ⟨0⟩ }
          else if s.substate.createdAccounts.contains I.codeOwner then
            (σ.insert r { dst with balance := ⟨0⟩ }).insert I.codeOwner { self with balance := ⟨0⟩ }
          else σ
    set { w with accounts := σ' }
    Fe.M.stop ByteArray.empty

/-! ## What the definitions give -/

/-- EVMLean's gas cap of a call is at most the call's gas argument. -/
theorem Cgascap_le (t r : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState)
    (A : Substate) : Cgascap t r val g σ μ A ≤ g.toNat := by
  unfold Cgascap
  split
  · exact Nat.min_le_right _ _
  · exact Nat.le_refl _

/-- The gas EVMLean's `CALL` forwards, `Ccallgas`, is `forwardedGas` of some cap: the model's
    calls range over every amount the EVM can forward. -/
theorem forwardedGas_Ccallgas (t r : AccountAddress) (value gasArg : UInt256) (σ : AccountMap)
    (μ : MachineState) (A : Substate) :
    ∃ cap, forwardedGas cap gasArg value = .ofNat (Ccallgas t r value gasArg σ μ A) := by
  refine ⟨.ofNat (Cgascap t r value gasArg σ μ A), ?_⟩
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

/-- A callee that leaves the substate as it was appended no log. -/
theorem appended_self (A : Substate) : appended A A = #[] := by
  simp [appended]

/-- A message call that is made is `Θ` on the model's accounts.  The hypothesis is the link
    EquiVM's `RD.call`, `RD.callValueMadeOr` and `RD.solcStaticcall` conclude with. -/
theorem message_made {I : Env} {w : World} {s : Supply} {rest : List Supply}
    {gasArg value value' argsPtr argsLen retPtr retLen g' : UInt256}
    {source recipient t : AccountAddress} {perm z : Bool} {σ' : AccountMap} {A' : Substate}
    {o : ByteArray} (hfeed : w.feed = s :: rest)
    (hmade : value ≤ (w.accounts.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024)
    (hΘ : (σ', g', A', z, o) =
      Θ w.accounts s.orig s.substate source I.sender recipient (toExecute w.accounts t)
        (forwardedGas s.gas gasArg value) (.ofNat I.gasPrice) value value'
        (w.memory.readWithPadding argsPtr.toNat argsLen.toNat) (I.depth + 1) I.header
        I.blobVersionedHashes I.blocks perm) :
    (message gasArg source recipient t value value' argsPtr argsLen retPtr retLen perm).exec I w =
      some (.ok (if z then ⟨1⟩ else ⟨0⟩,
        { w with
          accounts := σ'
          logs := w.logs ++ appended s.substate A'
          memory := o.write 0 w.memory retPtr.toNat (min retLen (.ofNat o.size)).toNat
          returnData := o
          feed := rest })) := by
  simp only [message, next, hfeed, M.exec_bind, M.exec_read, M.exec_get, M.exec_set, M.exec_pure,
    if_pos hmade, ← hΘ]

/-- A message call that is not made, for want of funds or at depth 1024, fails and changes
    nothing but the return data and the feed: no log is appended, and the write to memory has
    length zero. -/
theorem message_notMade {I : Env} {w : World} {s : Supply} {rest : List Supply}
    {gasArg value value' argsPtr argsLen retPtr retLen : UInt256}
    {source recipient t : AccountAddress} {perm : Bool} (hfeed : w.feed = s :: rest)
    (hnot : ¬ (value ≤ (w.accounts.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024)) :
    (message gasArg source recipient t value value' argsPtr argsLen retPtr retLen perm).exec I w =
      some (.ok (⟨0⟩,
        { w with
          logs := w.logs ++ appended s.substate s.substate
          memory := ByteArray.empty.write 0 w.memory retPtr.toNat
            (min retLen (.ofNat ByteArray.empty.size)).toNat
          returnData := ByteArray.empty
          feed := rest })) := by
  simp only [message, next, hfeed, M.exec_bind, M.exec_read, M.exec_get, M.exec_set, M.exec_pure,
    if_neg hnot]
  rfl

/-- A message call without write permission leaves every account's storage as it was, whatever
    the callee and the feed: EVMLean's `Theta_static_accountStorageStateEq`, on the model. -/
theorem message_static_keeps_storage {I : Env} {w w' : World}
    {gasArg value value' argsPtr argsLen retPtr retLen x : UInt256}
    {source recipient t : AccountAddress}
    (h : (message gasArg source recipient t value value' argsPtr argsLen retPtr retLen false).exec
      I w = some (.ok (x, w'))) :
    accountStorageStateEq w.accounts w'.accounts := by
  cases hf : w.feed with
  | nil => simp [message, next, hf] at h
  | cons s rest =>
    by_cases hmade :
        value ≤ (w.accounts.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
    · rcases hr : Θ w.accounts s.orig s.substate source I.sender recipient (toExecute w.accounts t)
          (forwardedGas s.gas gasArg value) (.ofNat I.gasPrice) value value'
          (w.memory.readWithPadding argsPtr.toNat argsLen.toNat) (I.depth + 1) I.header
          I.blobVersionedHashes I.blocks false with ⟨σ', g', A', z, o⟩
      rw [message_made hf hmade hr.symm] at h
      injection h with h
      injection h with h
      rw [← (Prod.mk.inj h).2]
      exact Theta_static_accountStorageStateEq hr
    · rw [message_notMade hf hmade] at h
      injection h with h
      injection h with h
      rw [← (Prod.mk.inj h).2]
      exact accountStorageStateEq_refl _

/-- A `staticcall` that returns leaves every account's storage as it was, whatever the callee
    and the feed. -/
theorem staticcall_keeps_storage {I : Env} {w w' : World}
    {gasArg addr argsPtr argsLen retPtr retLen x : UInt256}
    (h : (staticcall gasArg addr argsPtr argsLen retPtr retLen).exec I w = some (.ok (x, w'))) :
    accountStorageStateEq w.accounts w'.accounts := by
  simp only [staticcall, M.exec_bind, M.exec_read] at h
  exact message_static_keeps_storage h

end Fe.EVM
