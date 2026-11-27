import Fe.Sonatina.H.Memory

/-!
# Memory-free cores of the world operations (design §3.6, "Lean prerequisite")

The model library's message calls and creations (`Fe/EVM/Calls.lean`) read their input from
the world's `memory` and write their output there.  H's memory is its blocks, so H runs the
same operations on bytes: `messageCore` takes the call's input bytes and returns, beside the
flag, the return data, of which the caller writes `min retLen (size o)` bytes, as `message`
does; `createCore` takes the init code bytes.  Each is the model library's operation with the
memory read and write taken out, and `message_eq_core` and `createWith_eq_core` prove that the
model library's operations are these cores with the memory access put back, so H and the
machine IR's interpreter run one semantics of a call (§3.6).

The other operations that touch memory have a memory-free core in the model library already,
which H calls directly: `emit` (logs), `KEC` (`keccak256`), `Fe.M.stop` and `Fe.M.revert`
(`evm_return`, `evm_revert`); copies from calldata, code, return data and external code take
their bytes from `Env`/`World` fields and write plain bytes (§3.4); `evm_mcopy` copies cells
(`H/Inst.lean`, review 22 H2).
-/

namespace Fe.Sonatina.H

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

/-- `message` (`Fe/EVM/Calls.lean`) on the input bytes `input`, without memory: the flag, and
    the return data `o`, which `message` writes `min retLen (size o)` bytes of to memory. -/
def messageCore (gasArg : UInt256) (source recipient t : AccountAddress) (value value' : UInt256)
    (input : ByteArray) (perm : Bool) : FeM (UInt256 × ByteArray) := do
  let I ← read
  let s ← next
  let w ← get
  let T : ThetaCall :=
    { messageCall I w s gasArg source recipient t value value' ⟨0⟩ ⟨0⟩ perm with d := input }
  let made := value ≤ (w.accounts.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
  let (σ', _, A', z, o) := if made then T.run else (w.accounts, ⟨0⟩, s.substate, false, .empty)
  set { w with
    accounts := σ'
    logs := w.logs ++ appended s.substate A'
    returnData := o
    calls := if made then w.calls ++ [Made.theta T] else w.calls }
  return (if z then ⟨1⟩ else ⟨0⟩, o)

/-- The bytes of the return data a message call writes to memory: as many as both the window
    and the data have. -/
def retCount (retLen : UInt256) (o : ByteArray) : Nat := (min retLen (.ofNat o.size)).toNat

/-- The model library's message call is its memory-free core between a read of the input
    from memory and a write of the output to it. -/
theorem message_eq_core (gasArg : UInt256) (source recipient t : AccountAddress)
    (value value' argsPtr argsLen retPtr retLen : UInt256) (perm : Bool) (I : ExecutionEnv) (w : World) :
    (message gasArg source recipient t value value' argsPtr argsLen retPtr retLen perm).exec I w =
      (do
        let w ← get
        let (z, o) ← messageCore gasArg source recipient t value value'
          (w.memory.readWithPadding argsPtr.toNat argsLen.toNat) perm
        modify fun w => { w with memory := o.write 0 w.memory retPtr.toNat (retCount retLen o) }
        return z : FeM UInt256).exec I w := by
  cases hf : w.feed with
  | nil => simp [message, messageCore, next, hf]
  | cons s rest =>
    simp only [message, messageCore, next, hf, M.exec_bind, M.exec_read, M.exec_get, M.exec_set,
      M.exec_pure, M.exec_modify]
    split <;> rfl

/-- `createWith` (`Fe/EVM/Calls.lean`) on the init code bytes `init`, without memory. -/
def createCore (salt : Option ByteArray) (value : UInt256) (init : ByteArray) : FeM UInt256 := do
  let I ← read
  if I.perm = false then Fe.M.fail .static
  else if init.size > 49152 then Fe.M.diverge
  else
    let s ← next
    let w ← get
    let σ := w.accounts
    let self : Account := σ.get? I.codeOwner |>.getD default
    if h : self.nonce.toNat < 2 ^ 64 - 1
        ∧ value ≤ (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ I.depth < 1024
        ∧ init.size ≤ 49152 then
      let L : LambdaCall :=
        { σ := σ.insert I.codeOwner { self with nonce := self.nonce + ⟨1⟩ }, σ₀ := s.orig
          A := s.substate, s := I.codeOwner, o := I.sender, g := s.gas, p := .ofNat I.gasPrice
          v := value, i := init, e := ⟨I.depth.val + 1, Nat.succ_lt_succ h.2.2.1⟩, ζ := salt
          H := I.header, bvh := I.blobVersionedHashes, blocks := I.blocks, w := I.perm }
      match L.run with
      | (a, σ', _, A', z, o) =>
        set { w with
          accounts := σ'
          logs := w.logs ++ appended s.substate A'
          returnData := if z then ByteArray.empty else o
          calls := w.calls ++ [Made.lambda L] }
        return if z then UInt256.ofNat a else ⟨0⟩
    else
      set { w with returnData := ByteArray.empty }
      return ⟨0⟩

theorem readWithPadding_size (b : ByteArray) (addr len : Nat) :
    (b.readWithPadding addr len).size = len := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  split
  · simp [ByteArray_zeroes_size]
  · simp only [ByteArray.size_append, ByteArray.size_extract, ByteArray_zeroes_size]
    omega

/-- The model library's creation is its memory-free core on the init code read from memory. -/
theorem createWith_eq_core (salt : Option ByteArray) (value ptr len : UInt256) (I : ExecutionEnv)
    (w : World) :
    (createWith salt value ptr len).exec I w =
      (createCore salt value (w.memory.readWithPadding ptr.toNat len.toNat)).exec I w := by
  have hsz := readWithPadding_size w.memory ptr.toNat len.toNat
  have hlen : (len > ⟨49152⟩) ↔ (w.memory.readWithPadding ptr.toNat len.toNat).size > 49152 := by
    rw [hsz]; exact Iff.rfl
  unfold createWith createCore
  simp only [M.exec_bind, M.exec_read]
  by_cases hp : I.perm = false
  · simp [hp]
  · by_cases hl : len > ⟨49152⟩
    · simp [hp, hl, hlen.mp hl]
    · have hl' : ¬ (w.memory.readWithPadding ptr.toNat len.toNat).size > 49152 :=
        fun h => hl (hlen.mpr h)
      simp only [hp, hl, hl', if_false]
      cases hf : w.feed with
      | nil => simp [next, hf]
      | cons s rest => simp [next, hf]

end Fe.Sonatina.H
