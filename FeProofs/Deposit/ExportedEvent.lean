import FeProofs.Deposit.ExportedStd
import FeProofs.Lib.AbiEncode

/-!
# FeDeposit's event, as exported

`DepositEvent`'s emission (`emit_Evm_DepositEvent`): a log entry of the contract with the
event's signature hash as its one topic and the ABI encoding of the five `bytes` fields as its
data.
-/

namespace FeProofs.Deposit.Exported

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory
open FeProofs.Lib (BytesHolds abiEncodeBytes)

/-- The topic of `DepositEvent`: the hash of its signature. -/
def depositEventTopic : UInt256 :=
  uInt256OfByteArray (KEC "DepositEvent(bytes,bytes,bytes,bytes,bytes)".toUTF8)

/-- The topic the compiler evaluates for `DepositEvent` is the hash of its signature. -/
theorem depositEventTopic_eq : depositEventTopic =
    UInt256.ofNat 45506446345753628416285423056165511379837572639148407563471291220684748896453 := by
  decide +kernel

variable (I : ExecutionEnv) (w : World)

set_option maxHeartbeats 4000000 in
/-- The event code the compiler generates for `DepositEvent`, on fields that hold the bytes
    `d0`, …, `d4`: a log entry of the contract with the event's topic and the ABI encoding of
    the five fields, encoded in a fresh buffer at the end of memory.  An encoding of `2 ^ 64`
    bytes or more fails with `Panic(0x41)`; under a static call the emission fails. -/
theorem emitDepositEvent_exec (e : DepositEvent) {d0 d1 d2 d3 d4 : ByteArray} {n : Nat}
    (h0 : BytesHolds e.pubkey d0 w.memory) (h1 : BytesHolds e.withdrawal_credentials d1 w.memory)
    (h2 : BytesHolds e.amount d2 w.memory) (h3 : BytesHolds e.signature d3 w.memory)
    (h4 : BytesHolds e.index d4 w.memory)
    (hn : (abiEncodeBytes [d0, d1, d2, d3, d4]).size = n)
    (hfit : w.memory.size + n < UInt256.size) :
    (emit_Evm_DepositEvent e).exec I w =
      if 2 ^ 64 - 1 < n then some (.error (.panic 0x41))
      else if I.perm then
        some (.ok ((), { w with
          memory := w.memory ++ abiEncodeBytes [d0, d1, d2, d3, d4]
          logs := w.logs.push ⟨I.codeOwner, #[depositEventTopic],
            abiEncodeBytes [d0, d1, d2, d3, d4]⟩ }))
      else some (.error .static) := by
  simp only [emit_Evm_DepositEvent, DepositEvent_emit_Evm, MemBuffer_span_ref,
    MemSlice_from_raw_parts_ref_u8, MemBuffer_drop, dealloc_u8, cast_u8_u8, pure_bind, bind_pure,
    bind_assoc, bind_pure_unit]
  rw [Fe.M.exec_bind, Lib.encodeBytes5_exec I w hn h0 h1 h2 h3 h4 hfit]
  by_cases hp : 2 ^ 64 - 1 < n
  · rw [ite_eq_left hp, ite_eq_left hp]
  rw [ite_eq_right hp, ite_eq_right hp]
  dsimp only
  have hpos : 0 < n := by rw [← hn, Lib.abiEncodeBytes5_size]; omega
  rw [Lib.evmLog1_exec, ← depositEventTopic_eq]
  dsimp only
  rw [ulit_toNat' w.memory.size (by omega), ulit_toNat' n (by omega),
    readWithPadding_tail w.memory _ 0 n (Nat.add_zero _).symm hpos (by omega), Nat.zero_add, ← hn,
    byteArray_extract_self]

end FeProofs.Deposit.Exported
