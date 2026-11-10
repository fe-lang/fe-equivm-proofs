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

/-- The world a message call starts in. -/
def World.init (σ : AccountMap) (A : Substate) : World := ⟨σ, A.logSeries⟩

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

end Fe.EVM
