import FeProofs.Lib.ExportedCorrect
import FeProofs.Case44Bank.Exported
import FeProofs.Common.Abi
import Fe.EVM.Entry

/-!
# Case44Bank: the exported internal function and the std code of the entries

What the exported code the arm reaches does, independently of any model: the internal function
`credit` from any world (`credit_exec`), the decoder of `Credit`, and the deployment entry; and
the contract as exported, `contract`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib
open FeProofs.Lib (locateAddress_exec shr160_eq_zero_iff)

namespace FeProofs.Case44Bank.Exported

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

/-! The exported layout places the two fields of `Ledger` at slots 0 and 1: the root of the
balances map and the total. -/

theorem balancesField : Field.ledger.field Layout.Ledger 0 = .storage (UInt256.ofNat 0) := rfl
theorem totalField : Field.ledger.field Layout.Ledger 1 = .storage (UInt256.ofNat 1) := rfl

variable (I : ExecutionEnv) (w : World)

/-- The exported `credit` at a map whose root is `p.slot`, from any world with room for its two
    map lookups: `Panic(0x11)` if the entry's word plus `b` overflows, otherwise it stores the
    sum at the entry, which fails under a static call. -/
theorem credit_exec (p : Place) (a b : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    (credit p a b).exec I w =
      if UInt256.size ≤ (slotWord I w.accounts (mapSlot a p.slot)).toNat + b.toNat then
        some (.error (.panic 17))
      else if I.perm then
        some (.ok ((), { w with
          accounts := storeWord I.codeOwner w.accounts (mapSlot a p.slot)
            (slotWord I w.accounts (mapSlot a p.slot) + b)
          memory := keyed (keyed w.memory a p.slot) a p.slot }))
      else some (.error .static) := by
  have h2 : (keyed w.memory a p.slot).size + 64 < UInt256.size := by
    rw [keyed_size]; omega
  simp only [credit, Fe.M.exec_bind, Fe.M.exec_pure, locateAddress_exec I w p p.slot a
    (by omega), load, sload, store]
  simp only [checkedAdd, Fe.M.exec_ite, Fe.M.exec_panic, Fe.M.exec_read, Fe.M.exec_get]
  by_cases ho : UInt256.size ≤ (slotWord I w.accounts (mapSlot a p.slot)).toNat + b.toNat
  · simp [ho]
  · simp only [ho, if_false, Fe.M.exec_pure,
      locateAddress_exec I { w with memory := keyed w.memory a p.slot } p p.slot a h2, exec_sstore]
    by_cases hperm : I.perm = true <;> simp [hperm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `decode_runtime_args` at `Credit { who: Address, amount: u256 }`: revert on calldata that
    cannot hold the selector and two words or on a `who` that is not an address, otherwise the
    two words after the selector. -/
theorem decodeCredit_exec (hlo : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Credit.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else if NotAddress (word I.calldata 4) then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36⟩, w)) := by
  have hshort : I.calldata.size - 4 < 64 ↔ I.calldata.size < 68 := by omega
  simp [decode_runtime_args_Evm_Sol_Credit, decode_from_prechecked_head_Credit_Sol_CallData,
    Credit_decode_from_CallData, Credit_HEAD_SIZE, checkedAdd, checkedSub, toNat0, toNat4, toNat32,
    truncate_size _ hfits, UInt256.size, add0_32, add32_32, ne64, at4, at36,
    headCheck hlo hfits (by norm_num : 64 < 2 ^ 64), hshort, shr160_eq_zero_iff]
  by_cases h : I.calldata.size < 68 <;>
    by_cases ha : NotAddress (uInt256OfByteArray (I.calldata.readBytes 4 32)) <;>
    simp [h, ha, word]

/-- The deployment entry: reject call value; `init` does nothing, and there are no immutable
    fields. -/
theorem initEntry_exec (args : ByteArray) :
    (init_entry args).exec I w =
      if I.weiValue = ⟨0⟩ then some (.ok (ByteArray.empty, w))
      else some (.error (.revert ByteArray.empty)) := by
  by_cases hwv : I.weiValue = ⟨0⟩ <;> simp [init_entry, init, exec_nonPayable, hwv]

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

end FeProofs.Case44Bank.Exported
