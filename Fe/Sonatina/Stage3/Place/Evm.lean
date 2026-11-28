import Fe.Sonatina.Stage3.Place.Mem
import Fe.EVM.Entry

/-!
# The memory-free EVM operations ignore memory

H runs the EVM operations that touch no memory (`EvmOp.memFree`) as the machine IR's interpreter
does (`evmH`, `EvmOp.run`), on its own world, whose memory is not the machine's.  So the
simulation needs that such an operation neither reads nor writes memory: on other memory it ends
as it does, with that memory (`IgnoresMemory`, `Fe/EVM/Entry.lean`).  `memFree_ignoresMemory`
proves it by cases over `EvmOp.run`.

The calls and creations read and write memory; `H.message_eq_core` and `H.createWith_eq_core`
(`H/World.lean`) split them into their memory-free cores and the memory accesses around them.
-/

namespace Fe.Sonatina.Stage3.Place

open Ethereum Fe Fe.EVM Fe.Sonatina

theorem ignoresMemory_next : IgnoresMemory next := by
  intro I w memory
  unfold next
  simp only [M.exec_bind, M.exec_get]
  cases w.feed <;> rfl

set_option maxHeartbeats 1000000 in
/-- A memory-free EVM operation neither reads nor writes memory. -/
theorem memFree_ignoresMemory {op : EvmOp} (h : op.memFree = true) (args : List UInt256) :
    IgnoresMemory (op.run args) := by
  unfold EvmOp.run
  split <;> simp only [EvmOp.memFree, Bool.false_eq_true] at h
  all_goals intro I w memory
  all_goals simp only [Fe.EVM.selfAddress, Fe.EVM.balance, Fe.EVM.origin, Fe.EVM.caller,
    Fe.EVM.callvalue, Fe.EVM.calldataload, Fe.EVM.calldatasize, Fe.EVM.codesize,
    Fe.EVM.gasprice, Fe.EVM.extcodesize, Fe.EVM.extcodehash, Fe.EVM.returndatasize,
    Fe.EVM.blockhash, Fe.EVM.coinbase, Fe.EVM.timestamp, Fe.EVM.blockNumber,
    Fe.EVM.prevrandao, Fe.EVM.gaslimit, Fe.EVM.chainid, Fe.EVM.selfbalance, Fe.EVM.basefee,
    Fe.EVM.blobhash, Fe.EVM.blobbasefee, Fe.EVM.gas, Fe.EVM.cload, Fe.EVM.sload,
    Fe.EVM.tload, Fe.EVM.sstore, Fe.EVM.tstore, Fe.EVM.next, stuck, M.exec_bind, M.exec_read,
    M.exec_get, M.exec_set, M.exec_modify, M.exec_fail, M.exec_pure, M.exec_diverge,
    withMemory_ok, withMemory_none]
  all_goals first
    | (split_ifs <;> rfl)
    | (rcases w with ⟨_, _, _, _, f, _⟩; cases f <;> rfl)

/-- The memory-free core of a message call ignores memory. -/
theorem ignoresMemory_messageCore (g : UInt256) (src rcp t : AccountAddress) (v v' : UInt256)
    (input : ByteArray) (perm : Bool) :
    IgnoresMemory (H.messageCore g src rcp t v v' input perm) := by
  intro I w memory
  rcases w with ⟨a, l, m, rd, f, c⟩
  cases f with
  | nil => rfl
  | cons sp rest =>
    simp only [H.messageCore, Fe.EVM.next, M.exec_bind, M.exec_read, M.exec_get, M.exec_set,
      M.exec_pure]
    split <;> rfl

/-- The memory-free core of a creation ignores memory. -/
theorem ignoresMemory_createCore (salt : Option ByteArray) (v : UInt256) (init : ByteArray) :
    IgnoresMemory (H.createCore salt v init) := by
  intro I w memory
  rcases w with ⟨a, l, m, rd, f, c⟩
  unfold H.createCore
  simp only [M.exec_bind, M.exec_read]
  split
  · rfl
  split
  · rfl
  cases f with
  | nil => rfl
  | cons sp rest =>
    simp only [Fe.EVM.next, M.exec_bind, M.exec_get, M.exec_set, M.exec_pure]
    split
    · split <;> rfl
    · rfl

end Fe.Sonatina.Stage3.Place
