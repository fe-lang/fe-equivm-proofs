import Ethereum.Semantics
import Fe.Core

/-!
# The EVM world of a Fe model

A contract's model runs in the EVM's own state types, so a certificate needs no relation
between two representations of storage.
-/

namespace Fe.EVM

open Ethereum

/-- The part of the EVM state a contract's model reads and writes. -/
structure World where
  accounts : AccountMap
  logs : LogSeries
  /-- The call's memory.  Its size is the address the next allocation gets.  It is the model's
      own: a certificate compares return data, never memory. -/
  memory : ByteArray := ByteArray.empty

/-- The world a message call starts in. -/
def World.init (σ : AccountMap) (A : Substate) : World := { accounts := σ, logs := A.logSeries }

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

/-- `alloc_raw(size)`: `size` fresh zero bytes at the end of memory.  Returns their address. -/
def alloc (size : UInt256) : FeM UInt256 := do
  let w ← get
  set { w with memory := w.memory ++ (⟨Array.replicate size.toNat 0⟩ : ByteArray) }
  return UInt256.ofNat w.memory.size

/-- Write `value` as the 32-byte big-endian word at `ptr`. -/
def mstore (ptr value : UInt256) : FeM Unit :=
  modify fun w => { w with memory := value.toByteArray.write 0 w.memory ptr.toNat 32 }

/-- The 32-byte big-endian word at `ptr`, reading zero past the end of memory. -/
def mload (ptr : UInt256) : FeM UInt256 := do
  return uInt256OfByteArray ((← get).memory.readWithPadding ptr.toNat 32)

/-- `zero_mem(ptr, len)`: write `len` zero bytes at `ptr`. -/
def zeroMem (ptr len : UInt256) : FeM Unit :=
  modify fun w =>
    { w with memory :=
        (⟨Array.replicate len.toNat 0⟩ : ByteArray).write 0 w.memory ptr.toNat len.toNat }

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

/-- The slot of entry `key` of a `StorageMap` rooted at `root`: Solidity's mapping layout. -/
def mapSlot (key root : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ root.toByteArray))

/-- A place a Fe access reaches.  Storage is the one address space modeled so far. -/
inductive Place
  | storage (slot : UInt256)

/-- Where each field of a struct or tuple lies below the first slot of its place. -/
structure Layout where
  /-- The slot of each field in storage, counted from the struct's own. -/
  storage : List Nat

/-- The place of field `index` of the struct at `p`. -/
def Place.field (p : Place) (layout : Layout) (index : Nat) : Place :=
  match p with
  | .storage slot => .storage (slot + UInt256.ofNat (layout.storage.getD index 0))

/-- The place of entry `key` of the `StorageMap` at `p`.  This is `StorageMap`'s `locate`,
    written by hand until the model has the memory its Fe definition hashes in. -/
def Place.entry (p : Place) (key : UInt256) : Place :=
  match p with
  | .storage slot => .storage (mapSlot key slot)

/-- The word at `p`. -/
def load (p : Place) : FeM UInt256 :=
  match p with
  | .storage slot => sload slot

/-- Store `val` at `p`. -/
def store (p : Place) (val : UInt256) : FeM Unit :=
  match p with
  | .storage slot => sstore slot val

/-- The word of `cd` at byte offset `off`. -/
def word (cd : ByteArray) (off : Nat) : UInt256 := uInt256OfByteArray (cd.readBytes off 32)

/-- A calldata word that is not a canonical address: a bit above the low 160 is set. -/
def NotAddress (w : UInt256) : Prop := 2 ^ 160 ≤ w.toNat

instance (w : UInt256) : Decidable (NotAddress w) := by unfold NotAddress; infer_instance

/-- The caller as a word. -/
def caller : FeM UInt256 := do return UInt256.ofNat (← read).source.val

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
