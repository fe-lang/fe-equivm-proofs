import FeProofs.Deposit.Exported
import FeProofs.Lib.StaticCall
import FeProofs.Lib.ExportedCorrect

/-!
# FeDeposit's exported std code: what it does

The contract the exported definitions make, and what the std code its view arms and
constructor reach does: a hash of two words (`hash_pair`), the SSZ length mix-in
(`mix_in_length`), the little-endian `u64` chunk (`u64_chunk`), and the `bytes` return of
`get_deposit_count`.
-/

namespace FeProofs.Deposit.Exported

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory
open scoped FeProofs.Lib

/-! ## Word shifts as numbers -/

theorem shl_toNat (x : UInt256) {k : Nat} (hk : k < 256) :
    (x <<< UInt256.ofNat k).toNat = (x.toNat <<< k) % UInt256.size := by
  have hkv : (UInt256.ofNat k).toNat = k := ulit_toNat' k (by
    rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  show (UInt256.shiftLeft x (UInt256.ofNat k)).toNat = _
  unfold UInt256.shiftLeft
  rw [if_neg (by show ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  show (x.toNat <<< (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkv]

theorem shr_toNat (x : UInt256) {k : Nat} (hk : k < 256) :
    (x >>> UInt256.ofNat k).toNat = x.toNat >>> k := by
  have hkv : (UInt256.ofNat k).toNat = k := ulit_toNat' k (by
    rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  show (UInt256.shiftRight x (UInt256.ofNat k)).toNat = _
  unfold UInt256.shiftRight
  rw [if_neg (by show ¬ (UInt256.ofNat k).toNat ≥ 256; omega)]
  show (x.toNat >>> (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkv]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) x.val.isLt)

theorem word_eq_iff {a b : UInt256} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, fun h => u256_inj h⟩

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := deploy init_entry, runtime := entry runtime }

/- `simp` tries each of its lemmas about a bind or a map on every one in a model, whatever the
   monad.  These are about other monads. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

attribute [local simp]
  SupportsInterface_HEAD_SIZE SupportsInterface_decode_from_CallData
  decode_from_prechecked_head_SupportsInterface_Sol_CallData
  decode_runtime_args_Evm_Sol_SupportsInterface
  GetDepositCount_HEAD_SIZE GetDepositCount_decode_from_CallData
  decode_from_prechecked_head_GetDepositCount_Sol_CallData
  decode_runtime_args_Evm_Sol_GetDepositCount
  GetDepositRoot_HEAD_SIZE GetDepositRoot_decode_from_CallData
  decode_from_prechecked_head_GetDepositRoot_Sol_CallData
  decode_runtime_args_Evm_Sol_GetDepositRoot
  checkedAdd checkedSub alloc mstore readPaddedWord zeroMem returnData panicCode

variable (I : ExecutionEnv) (w : World)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `supportsInterface(bytes4)`'s decoder: revert on calldata too short for the word, or on a
    word whose low 28 bytes are not zero; else the word's top 4 bytes. -/
theorem decodeSupportsInterface_exec (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_SupportsInterface.exec I w =
      if I.calldata.size < 36 then some (.error (.revert ByteArray.empty))
      else if word I.calldata 4 <<< UInt256.ofNat 32 ≠ UInt256.ofNat 0 then
        some (.error (.revert ByteArray.empty))
      else some (.ok (⟨⟨word I.calldata 4 >>> UInt256.ofNat 224⟩⟩, w)) := by
  have hshort : I.calldata.size - 4 < 32 ↔ I.calldata.size < 36 := by omega
  have e1 : ¬ UInt256.size ≤ 32 := by decide
  have e2 : UInt256.ofNat 4 * UInt256.ofNat 8 = UInt256.ofNat 32 := by decide
  have e3 : (UInt256.ofNat 32 - UInt256.ofNat 4) * UInt256.ofNat 8 = UInt256.ofNat 224 := by
    decide
  simp [e1, e2, e3, toNat0, toNat32, truncate_size _ hfits, add0_32, ne32, at4, headCheck hlo hfits (by norm_num : 32 < 2 ^ 64), hshort,
    show UInt256.ofNat 4 ≠ UInt256.ofNat 0 by decide, show UInt256.ofNat 4 ≠ UInt256.ofNat 32 by decide,
    show (UInt256.ofNat 4).toNat = 4 from rfl]
  by_cases h : I.calldata.size < 36 <;>
    by_cases hw : uInt256OfByteArray (I.calldata.readBytes 4 32) <<< UInt256.ofNat 32 = UInt256.ofNat 0 <;>
    simp [h, hw, word]

end FeProofs.Deposit.Exported
