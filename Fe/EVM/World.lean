import Ethereum.Semantics
import Fe.Core

/-!
# The EVM world of a Fe model

A contract's model runs in the EVM's own state types, so a certificate needs no relation
between two representations of storage.
-/

namespace Fe.EVM

open Ethereum

/-- What the context supplies each time the model consults it: once for `gas()`, once for each
    message call or creation.  The model counts no gas and keeps no substate, so it cannot
    compute these. -/
structure Supply where
  /-- `gas()`: the value read.  A message call: the most the callee may get, before the cap of
      the call's own gas argument.  A creation: the gas the init code runs with. -/
  gas : UInt256
  /-- The accrued substate the EVM hands the callee: what is warm, what this transaction
      created, the refund counter, the log so far. -/
  substate : Substate
  /-- The account map the transaction started from, which prices the callee's `SSTORE`s. -/
  orig : AccountMap

/-- The part of the EVM state a contract's model reads and writes. -/
structure World where
  accounts : AccountMap
  logs : LogSeries
  /-- The call's memory.  Its size is the address the next allocation gets.  It is the model's
      own: a certificate compares return data, never memory. -/
  memory : ByteArray := ByteArray.empty
  /-- The return data of the last message call or creation, empty before the first. -/
  returnData : ByteArray := ByteArray.empty
  /-- What the context has yet to supply.  A model that makes no call and reads no gas never
      looks at it. -/
  feed : List Supply := []

/-- The world a message call starts in, with the feed the context will supply. -/
def World.init (σ : AccountMap) (A : Substate) (feed : List Supply := []) : World :=
  { accounts := σ, logs := A.logSeries, feed := feed }

abbrev Env := ExecutionEnv

/-- The model monad on the EVM. -/
abbrev FeM := Fe.M Env World

/-- The calldata of the current call. -/
def calldata : FeM ByteArray := do return (← read).calldata

/-- `calldataload(offset)`: the 32 bytes of calldata from `offset`, zero-padded. -/
def calldataload (offset : UInt256) : FeM UInt256 := do
  return uInt256OfByteArray ((← read).calldata.readBytes offset.toNat 32)

/-- `calldatasize()` -/
def calldatasize : FeM UInt256 := do return UInt256.ofNat (← read).calldata.size

/-- `revert_empty()`: revert with no data.  It never returns. -/
def revertEmpty : FeM Empty := Fe.M.revert ByteArray.empty

/-- `panic_code(code)`: fail with `Panic(code)`.  It never returns. -/
def panicCode (code : UInt256) : FeM Empty := Fe.M.panic code.toNat

/-- `alloc_raw(size)`: `size` fresh zero bytes at the end of memory.  Returns their address.
    Memory cannot reach `2 ^ 256` bytes: the EVM runs out of gas long before, so a run that
    would get there does not terminate. -/
def alloc (size : UInt256) : FeM UInt256 := do
  let w ← get
  if w.memory.size + size.toNat < UInt256.size then
    set { w with memory := w.memory ++ (⟨Array.replicate size.toNat 0⟩ : ByteArray) }
    return UInt256.ofNat w.memory.size
  else
    Fe.M.diverge

/-- Write `value` as the 32-byte big-endian word at `ptr`. -/
def mstore (ptr value : UInt256) : FeM Unit :=
  modify fun w => { w with memory := value.toByteArray.write 0 w.memory ptr.toNat 32 }

/-- The 32-byte big-endian word at `ptr`, reading zero past the end of memory. -/
def mload (ptr : UInt256) : FeM UInt256 := do
  return uInt256OfByteArray ((← get).memory.readWithPadding ptr.toNat 32)

/-- Write `bytes` at `ptr`: the copy of the constructor arguments, the code after the creation
    code, into memory. -/
def mstoreBytes (ptr : UInt256) (bytes : ByteArray) : FeM Unit :=
  modify fun w => { w with memory := bytes.write 0 w.memory ptr.toNat bytes.size }

/-- A string literal longer than a word: fresh memory that holds its length word, then its
    bytes, then zeros to a whole word.  Returns the address. -/
def stringLiteral (bytes : ByteArray) : FeM UInt256 := do
  let ptr ← alloc (UInt256.ofNat (32 + (bytes.size + 31) / 32 * 32))
  mstore ptr (UInt256.ofNat bytes.size)
  mstoreBytes (ptr + UInt256.ofNat 32) bytes
  return ptr

/-- `read_padded_word(ptr, len)`: the big-endian word whose first `min len 32` bytes are
    memory's at `ptr` and whose other bytes are zero. -/
def readPaddedWord (ptr len : UInt256) : FeM UInt256 := do
  let bytes := (← get).memory.readWithPadding ptr.toNat (min len.toNat 32)
  return uInt256OfByteArray (bytes.readWithPadding 0 32)

/-- `zero_mem(ptr, len)`: write `len` zero bytes at `ptr`. -/
def zeroMem (ptr len : UInt256) : FeM Unit :=
  modify fun w =>
    { w with memory :=
        (⟨Array.replicate len.toNat 0⟩ : ByteArray).write 0 w.memory ptr.toNat len.toNat }

/-- `mstore8(ptr, value)`: write the low byte of `value` at `ptr`. -/
def mstore8 (ptr value : UInt256) : FeM Unit :=
  modify fun w =>
    { w with memory := (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).write 0 w.memory ptr.toNat 1 }

/-- `copy_mem(dest, source, len)`: copy `len` bytes of memory, as `MCOPY` does. -/
def mcopy (dest source len : UInt256) : FeM Unit :=
  modify fun w =>
    { w with memory := w.memory.write source.toNat w.memory dest.toNat len.toNat }

/-- `calldatacopy(dest, offset, len)`: copy `len` bytes of calldata from `offset` into memory at
    `dest`, zeros past its end. -/
def calldatacopy (dest offset len : UInt256) : FeM Unit := do
  let cd := (← read).calldata
  modify fun w => { w with memory := cd.write offset.toNat w.memory dest.toNat len.toNat }

/-- `codecopy(dest, offset, len)`: copy `len` bytes of the running code from `offset` into memory
    at `dest`, zeros past its end. -/
def codecopy (dest offset len : UInt256) : FeM Unit := do
  let code := (← read).code
  modify fun w => { w with memory := code.write offset.toNat w.memory dest.toNat len.toNat }

/-- `codesize()` -/
def codesize : FeM UInt256 := do return UInt256.ofNat (← read).code.size

/-- `C::init_code_len()`: the size of `creation`, the creation code of a contract `C` that the
    running one deploys. -/
def initCodeLen (creation : ByteArray) : FeM UInt256 := pure (UInt256.ofNat creation.size)

/-- `C::init_code_offset()`: where `creation`, the creation code of a contract `C` that the
    running one deploys, lies in the running code.  A contract that deploys `C` holds its
    creation code, and this is where that code first occurs; code that does not hold it gives
    its own size. -/
def initCodeOffset (creation : ByteArray) : FeM UInt256 := do
  let code := (← read).code
  let found := (List.range (code.size + 1 - creation.size)).find? fun i =>
    code.get! i == creation.get! 0 && code.extract i (i + creation.size) == creation
  return UInt256.ofNat (found.getD code.size)

/-- The 32-byte big-endian word of the running code at `offset`, reading zero past its end. -/
def cload (offset : UInt256) : FeM UInt256 := do
  return uInt256OfByteArray ((← read).code.readWithPadding offset.toNat 32)

/-- Where word `slot` of a contract's immutable fields lies in the running code.  The fields
    take the last `total` words of the deployed code, so the address counts back from its end,
    wrapping as the EVM's arithmetic does. -/
def immutableAt (total slot : Nat) : FeM UInt256 := do
  return UInt256.ofNat (← read).code.size - UInt256.ofNat ((total - slot) * 32)

/-- The `len` bytes of memory at `ptr`, zeros past its end: what a constructor returns for the
    words of the immutable fields. -/
def memoryBytes (ptr len : UInt256) : FeM ByteArray := do
  return (← get).memory.readWithPadding ptr.toNat len.toNat

/-- `keccak256(ptr, len)`: the hash of the `len` bytes of memory at `ptr`. -/
def keccak256 (ptr len : UInt256) : FeM UInt256 := do
  return .ofNat (fromByteArrayBigEndian (KEC ((← get).memory.readWithPadding ptr.toNat len.toNat)))

/-- `stop()`: end the call successfully with no data.  It never returns. -/
def stopCall : FeM Empty := Fe.M.stop ByteArray.empty

/-- `panic()` and `todo()`: an invalid instruction.  They never return. -/
def trap : FeM Empty := Fe.M.fail .trap

/-- `revert(ptr, len)`: revert with the `len` bytes of memory at `ptr`.  It never returns. -/
def revertData (ptr len : UInt256) : FeM Empty := do
  Fe.M.revert ((← get).memory.readWithPadding ptr.toNat len.toNat)

/-- `return_data(ptr, len)`: end the call successfully with the `len` bytes of memory at `ptr`.
    It never returns. -/
def returnData (ptr len : UInt256) : FeM Empty := do
  Fe.M.stop ((← get).memory.readWithPadding ptr.toNat len.toNat)

/-- The selector of the call: the first four bytes of calldata, as the entry reads them,
    `calldataload(0) >> 224`. -/
def calldataSelector : FeM UInt256 := do
  return (← calldataload (UInt256.ofNat 0)) >>> UInt256.ofNat 224

/-- The low `bits` bits of `v`: a cast to a narrower unsigned integer type. -/
def truncate (bits : Nat) (v : UInt256) : UInt256 := UInt256.ofNat (v.toNat % 2 ^ bits)

/-- An entry point that takes no value reverts when sent some. -/
def nonPayable : FeM Unit := do
  if (← read).weiValue ≠ ⟨0⟩ then Fe.M.revert ByteArray.empty

/-- Calldata is too short to hold `words` argument words after the selector, or so long that
    Solidity's signed length check rejects it. -/
def BadHead (cd : ByteArray) (words : Nat) : Prop :=
  cd.size < 4 + 32 * words ∨ 2 ^ 255 + 4 ≤ cd.size

instance (cd : ByteArray) (words : Nat) : Decidable (BadHead cd words) := by
  unfold BadHead; infer_instance

/-- The word at `slot` of the storage of the contract `I` runs. -/
def slotWord (I : Env) (σ : AccountMap) (slot : UInt256) : UInt256 :=
  σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD slot ⟨0⟩)

/-- The word at `slot` of the current contract's storage. -/
def sload (slot : UInt256) : FeM UInt256 := do
  return slotWord (← read) (← get).accounts slot

/-- The account map after the contract at `owner` stores `val` at `slot`.  A zero erases the
    slot, as the EVM does. -/
def storeWord (owner : AccountAddress) (σ : AccountMap) (slot val : UInt256) : AccountMap :=
  σ.get? owner |>.option σ fun acc =>
    σ.insert owner
      (if val == default then { acc with storage := acc.storage.erase slot }
       else { acc with storage := acc.storage.insert slot val })

/-- Store `val` at `slot` of the current contract's storage.  Under a static call it fails. -/
def sstore (slot val : UInt256) : FeM Unit := do
  let env ← read
  if env.perm then
    modify fun w => { w with accounts := storeWord env.codeOwner w.accounts slot val }
  else
    Fe.M.fail .static

/-- Append a log entry of the current contract.  Under a static call it fails. -/
def emit (topics : Array UInt256) (data : ByteArray) : FeM Unit := do
  let env ← read
  if env.perm then
    modify fun w => { w with logs := w.logs.push ⟨env.codeOwner, topics, data⟩ }
  else
    Fe.M.fail .static

/-- `log<n>(ptr, len, topics…)`: append a log entry whose data is the `len` bytes of memory at
    `ptr`.  Under a static call it fails. -/
def logData (ptr len : UInt256) (topics : Array UInt256) : FeM Unit := do
  emit topics ((← get).memory.readWithPadding ptr.toNat len.toNat)

/-- The word at `slot` of the current contract's transient storage. -/
def tload (slot : UInt256) : FeM UInt256 := do
  let env ← read
  return ((← get).accounts.get? env.codeOwner).option ⟨0⟩ (fun acc => acc.tstorage.getD slot ⟨0⟩)

/-- Store `val` at `slot` of the current contract's transient storage.  Under a static call it
    fails. -/
def tstore (slot val : UInt256) : FeM Unit := do
  let env ← read
  if env.perm then
    modify fun w =>
      { w with accounts :=
          (w.accounts.get? env.codeOwner).option w.accounts fun acc =>
            w.accounts.insert env.codeOwner (acc.updateTransientStorage slot val) }
  else
    Fe.M.fail .static

/-! ## The call's context -/

/-- `address()`: the running contract. -/
def selfAddress : FeM UInt256 := do return UInt256.ofNat (← read).codeOwner.val

/-- `callvalue()` -/
def callvalue : FeM UInt256 := do return (← read).weiValue

/-- `origin()`: the transaction's sender. -/
def origin : FeM UInt256 := do return UInt256.ofNat (← read).sender.val

/-- `gasprice()` -/
def gasprice : FeM UInt256 := do return UInt256.ofNat (← read).gasPrice

/-- `coinbase()` -/
def coinbase : FeM UInt256 := do return UInt256.ofNat (← read).header.beneficiary.val

/-- `timestamp()` -/
def timestamp : FeM UInt256 := do return UInt256.ofNat (← read).header.timestamp

/-- `number()`: the block number. -/
def blockNumber : FeM UInt256 := do return UInt256.ofNat (← read).header.number

/-- `prevrandao()` -/
def prevrandao : FeM UInt256 := do return (← read).header.prevRandao

/-- `gaslimit()` -/
def gaslimit : FeM UInt256 := do return UInt256.ofNat (← read).header.gasLimit

/-- `chainid()` -/
def chainid : FeM UInt256 := pure (UInt256.ofNat Ethereum.chainId)

/-- `basefee()` -/
def basefee : FeM UInt256 := do return Ethereum.basefee (← read)

/-- `blobbasefee()` -/
def blobbasefee : FeM UInt256 := do return (← read).getBlobGasprice

/-- `blobhash(index)` -/
def blobhash (index : UInt256) : FeM UInt256 := do return Ethereum.blobhash (← read) index

/-- `blockhash(number)`: the hash of one of the 256 most recent blocks, and zero otherwise. -/
def blockhash (number : UInt256) : FeM UInt256 := do
  let env ← read
  let current := env.header.number
  if current ≤ number.toNat || number.toNat + 256 < current then return ⟨0⟩
  else return (env.blocks.map ProcessedBlock.hash).getD number.toNat ⟨0⟩

/-- `balance(addr)`: the balance of an account, zero if there is none. -/
def balance (addr : UInt256) : FeM UInt256 := do
  return ((← get).accounts.get? (AccountAddress.ofUInt256 addr)).elim ⟨0⟩ (·.balance)

/-- `selfbalance()` -/
def selfbalance : FeM UInt256 := do
  return ((← get).accounts.get? (← read).codeOwner).elim ⟨0⟩ (·.balance)

/-- `extcodesize(addr)` -/
def extcodesize (addr : UInt256) : FeM UInt256 := do
  return ((← get).accounts.get? (AccountAddress.ofUInt256 addr)).option ⟨0⟩
    (.ofNat ∘ ByteArray.size ∘ (·.code))

/-- The slot of entry `key` of a `StorageMap` rooted at `root`: Solidity's mapping layout. -/
def mapSlot (key root : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ root.toByteArray))

/-- A state space of a contract: its storage, or its transient storage. -/
inductive Space
  | storage
  | transient
  deriving DecidableEq, Inhabited

/-- A place a Fe access reaches in contract state: a slot of a state space.  A value of more than
    one slot starts there.  This is what a reference to state is at run time: the slot number. -/
structure Place where
  space : Space
  slot : UInt256
  deriving Inhabited

/-- The place at `slot` of storage. -/
def Place.storage (slot : UInt256) : Place := ⟨.storage, slot⟩

/-- Where each field of a struct or tuple lies below the first slot of its place. -/
structure Layout where
  /-- The slot of each field in storage, counted from the struct's own. -/
  storage : List Nat

/-- The place of field `index` of the struct at `p`. -/
def Place.field (p : Place) (layout : Layout) (index : Nat) : Place :=
  { p with slot := p.slot + UInt256.ofNat (layout.storage.getD index 0) }

/-- The place of entry `key` of the `StorageMap` at `p`.  This is `StorageMap`'s `locate`,
    written by hand until the model has the memory its Fe definition hashes in. -/
def Place.entry (p : Place) (key : UInt256) : Place :=
  { p with slot := mapSlot key p.slot }

/-- The word at `p`. -/
def load (p : Place) : FeM UInt256 :=
  match p.space with
  | .storage => sload p.slot
  | .transient => tload p.slot

/-- Store `val` at `p`. -/
def store (p : Place) (val : UInt256) : FeM Unit :=
  match p.space with
  | .storage => sstore p.slot val
  | .transient => tstore p.slot val

/-- The word of `cd` at byte offset `off`. -/
def word (cd : ByteArray) (off : Nat) : UInt256 := uInt256OfByteArray (cd.readBytes off 32)

/-- A calldata word that is not a canonical address: a bit above the low 160 is set. -/
def NotAddress (w : UInt256) : Prop := 2 ^ 160 ≤ w.toNat

instance (w : UInt256) : Decidable (NotAddress w) := by unfold NotAddress; infer_instance

/-- The caller as a word. -/
def caller : FeM UInt256 := do return UInt256.ofNat (← read).source.val

/-- The check before an array element is reached: `Panic(0x32)` unless `index` is below the
    array's length `len`. -/
def checkIndex (index : UInt256) (len : Nat) : FeM Unit :=
  if index.toNat < len then pure () else Fe.M.panic 0x32

/-- Checked `a + b`: `Panic(0x11)` on overflow. -/
def checkedAdd (a b : UInt256) : FeM UInt256 :=
  if UInt256.size ≤ a.toNat + b.toNat then Fe.M.panic 0x11 else pure (a + b)

/-- Checked `a - b`: `Panic(0x11)` on underflow. -/
def checkedSub (a b : UInt256) : FeM UInt256 :=
  if a.toNat < b.toNat then Fe.M.panic 0x11 else pure (UInt256.sub a b)

/-- Checked `a * b`: `Panic(0x11)` on overflow. -/
def checkedMul (a b : UInt256) : FeM UInt256 :=
  if UInt256.size ≤ a.toNat * b.toNat then Fe.M.panic 0x11 else pure (a * b)

/-- `a / b`: `Panic(0x12)` when `b` is zero. -/
def checkedDiv (a b : UInt256) : FeM UInt256 :=
  if b = ⟨0⟩ then Fe.M.panic 0x12 else pure (a / b)

/-- `a % b`: `Panic(0x12)` when `b` is zero. -/
def checkedRem (a b : UInt256) : FeM UInt256 :=
  if b = ⟨0⟩ then Fe.M.panic 0x12 else pure (a % b)

/-- The return data of a failed `assert!` with a message: Solidity's `Error(string)`.  Not
    observed at profile `P0`; to confirm against Fe's lowering with the first `P1` proof. -/
def assertData (msg : String) : ByteArray :=
  let bytes := msg.toUTF8
  ⟨#[0x08, 0xc3, 0x79, 0xa0]⟩ ++ (UInt256.ofNat 32).toByteArray
    ++ (UInt256.ofNat bytes.size).toByteArray ++ bytes
    ++ ⟨Array.replicate ((32 - bytes.size % 32) % 32) 0⟩

@[simp] theorem exec_sload (slot : UInt256) (I : Env) (w : World) :
    (sload slot).exec I w = some (.ok (slotWord I w.accounts slot, w)) := rfl

@[simp] theorem load_storage (slot : UInt256) : load (.storage slot) = sload slot := rfl

@[simp] theorem store_storage (slot val : UInt256) :
    store (.storage slot) val = sstore slot val := rfl

@[simp] theorem Place.field_storage (slot : UInt256) (layout : Layout) (index : Nat) :
    (Place.storage slot).field layout index =
      .storage (slot + UInt256.ofNat (layout.storage.getD index 0)) := rfl

@[simp] theorem Place.entry_storage (slot key : UInt256) :
    (Place.storage slot).entry key = .storage (mapSlot key slot) := rfl

@[simp] theorem exec_caller (I : Env) (w : World) :
    caller.exec I w = some (.ok (UInt256.ofNat I.source.val, w)) := rfl

@[simp] theorem exec_calldataload (offset : UInt256) (I : Env) (w : World) :
    (calldataload offset).exec I w =
      some (.ok (uInt256OfByteArray (I.calldata.readBytes offset.toNat 32), w)) := rfl

@[simp] theorem exec_calldatasize (I : Env) (w : World) :
    calldatasize.exec I w = some (.ok (UInt256.ofNat I.calldata.size, w)) := rfl

@[simp] theorem exec_revertEmpty (I : Env) (w : World) :
    revertEmpty.exec I w = some (.error (.revert ByteArray.empty)) := rfl

@[simp] theorem exec_calldata (I : Env) (w : World) :
    calldata.exec I w = some (.ok (I.calldata, w)) := rfl

theorem exec_sstore (slot val : UInt256) (I : Env) (w : World) :
    (sstore slot val).exec I w =
      if I.perm then some (.ok ((), { w with accounts := storeWord I.codeOwner w.accounts slot val }))
      else some (.error .static) := by
  cases h : I.perm <;> simp [sstore, h]

theorem exec_emit (topics : Array UInt256) (data : ByteArray) (I : Env) (w : World) :
    (emit topics data).exec I w =
      if I.perm then some (.ok ((), { w with logs := w.logs.push ⟨I.codeOwner, topics, data⟩ }))
      else some (.error .static) := by
  cases h : I.perm <;> simp [emit, h]

theorem exec_nonPayable (I : Env) (w : World) :
    nonPayable.exec I w =
      if I.weiValue = ⟨0⟩ then some (.ok ((), w)) else some (.error (.revert ByteArray.empty)) := by
  by_cases h : I.weiValue = ⟨0⟩ <;> simp [nonPayable, h]

/-! ## The operations never stop the run from inside -/

open Fe.M in
/-- Prove `NoStop` for a computation built from binds, conditionals and the core operations. -/
macro "no_stop_core" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact NoStop.pure _
    | with_reducible exact NoStop.revert _
    | with_reducible exact NoStop.panic _
    | with_reducible exact NoStop.fail_static
    | with_reducible exact NoStop.read
    | with_reducible exact NoStop.get
    | with_reducible exact NoStop.modify _
    | assumption
    | with_reducible apply NoStop.ite
    | with_reducible apply NoStop.bind
    | intro (_ : _))

theorem noStop_sload (slot : UInt256) : (sload slot).NoStop := by unfold sload; no_stop_core

theorem noStop_sstore (slot val : UInt256) : (sstore slot val).NoStop := by unfold sstore; no_stop_core

theorem noStop_emit (topics : Array UInt256) (data : ByteArray) : (emit topics data).NoStop := by
  unfold emit; no_stop_core

theorem noStop_caller : caller.NoStop := by unfold caller; no_stop_core

theorem noStop_calldata : calldata.NoStop := by unfold calldata; no_stop_core

theorem noStop_nonPayable : nonPayable.NoStop := by unfold nonPayable; no_stop_core

theorem noStop_checkedAdd (a b : UInt256) : (checkedAdd a b).NoStop := by unfold checkedAdd; no_stop_core

theorem noStop_checkedSub (a b : UInt256) : (checkedSub a b).NoStop := by unfold checkedSub; no_stop_core

open Fe.M in
/-- Prove `NoStop` for a computation built from binds, conditionals and the operations of this
    file.  Unfold the definitions it should look into first. -/
macro "no_stop" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact noStop_sload _
    | with_reducible exact noStop_sstore _ _
    | with_reducible exact noStop_emit _ _
    | with_reducible exact noStop_caller
    | with_reducible exact noStop_calldata
    | with_reducible exact noStop_nonPayable
    | with_reducible exact noStop_checkedAdd _ _
    | with_reducible exact noStop_checkedSub _ _
    | with_reducible exact NoStop.pure _
    | with_reducible exact NoStop.revert _
    | with_reducible exact NoStop.panic _
    | assumption
    | with_reducible apply NoStop.ite
    | with_reducible apply NoStop.bind
    | intro (_ : _))

/-! ## The operations leave memory alone -/

/-- The computation leaves memory as it found it whenever it returns.  Storage, logs and the
    environment's reads do; allocation and writes through pointers do not. -/
def KeepsMemory {α : Type} (m : FeM α) : Prop :=
  ∀ I w a w', m.exec I w = some (.ok (a, w')) → w'.memory = w.memory

theorem KeepsMemory.pure {α : Type} (a : α) : KeepsMemory (pure a : FeM α) := by
  intro I w a' w' h; simp at h; rw [h.2]

theorem KeepsMemory.revert {α : Type} (data : ByteArray) :
    KeepsMemory (Fe.M.revert data : FeM α) := by
  intro I w a w' h; simp at h

theorem KeepsMemory.panic {α : Type} (code : Nat) : KeepsMemory (Fe.M.panic code : FeM α) := by
  intro I w a w' h; simp at h

theorem KeepsMemory.bind {α β : Type} {m : FeM α} {k : α → FeM β} (hm : KeepsMemory m)
    (hk : ∀ a, KeepsMemory (k a)) : KeepsMemory (m >>= k) := by
  intro I w b w' h
  rw [M.exec_bind] at h
  cases hr : m.exec I w with
  | none => rw [hr] at h; cases h
  | some r =>
    cases r with
    | error f => rw [hr] at h; cases h
    | ok p => rw [hr] at h; rw [hk p.1 I p.2 b w' h, hm I w p.1 p.2 hr]

theorem KeepsMemory.ite {α : Type} (c : Prop) [Decidable c] {a b : FeM α} (ha : KeepsMemory a)
    (hb : KeepsMemory b) : KeepsMemory (if c then a else b) := by
  split <;> assumption

theorem keepsMemory_sload (slot : UInt256) : KeepsMemory (sload slot) := by
  intro I w a w' h; simp at h; rw [h.2]

theorem keepsMemory_sstore (slot val : UInt256) : KeepsMemory (sstore slot val) := by
  intro I w a w' h
  rw [exec_sstore] at h
  split at h <;> simp at h
  rw [← h]

theorem keepsMemory_emit (topics : Array UInt256) (data : ByteArray) :
    KeepsMemory (emit topics data) := by
  intro I w a w' h
  rw [exec_emit] at h
  split at h <;> simp at h
  rw [← h]

theorem keepsMemory_caller : KeepsMemory caller := by
  intro I w a w' h; simp at h; rw [h.2]

theorem keepsMemory_checkedAdd (a b : UInt256) : KeepsMemory (checkedAdd a b) := by
  unfold checkedAdd; exact KeepsMemory.ite _ (KeepsMemory.panic _) (KeepsMemory.pure _)

theorem keepsMemory_checkedSub (a b : UInt256) : KeepsMemory (checkedSub a b) := by
  unfold checkedSub; exact KeepsMemory.ite _ (KeepsMemory.panic _) (KeepsMemory.pure _)

/-- Prove `KeepsMemory` for a computation built from binds, conditionals and the storage, log
    and arithmetic operations.  Unfold the definitions it should look into first. -/
macro "keeps_memory" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact keepsMemory_sload _
    | with_reducible exact keepsMemory_sstore _ _
    | with_reducible exact keepsMemory_emit _ _
    | with_reducible exact keepsMemory_caller
    | with_reducible exact keepsMemory_checkedAdd _ _
    | with_reducible exact keepsMemory_checkedSub _ _
    | with_reducible exact KeepsMemory.pure _
    | with_reducible exact KeepsMemory.revert _
    | with_reducible exact KeepsMemory.panic _
    | assumption
    | with_reducible apply KeepsMemory.ite
    | with_reducible apply KeepsMemory.bind
    | intro (_ : _))

end Fe.EVM
