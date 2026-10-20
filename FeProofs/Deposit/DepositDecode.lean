import Reasoning.ABI
import FeProofs.Deposit.Spec

/-!
# FeDeposit `deposit` calldata decoding (Stele side)

The modern decoder on `(bytes, bytes, bytes, bytes32)` for calldata shorter than `2^64` bytes:
it succeeds exactly when the 128-byte head is present and each `bytes` argument's length word and
payload lie inside the calldata, and then binds each argument to its payload slice.
(Offsets and lengths are then below `2^64`, so the decoder's `2^64 - 1` caps never fire.)
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs.Deposit

/-- Calldata after the selector. -/
abbrev dArgs (cd : ByteArray) : List UInt8 := cd.toList.drop 4

/-- The calldata word at argument-relative offset `o`. -/
abbrev dWord (cd : ByteArray) (o : Nat) : Nat := (calldataWord cd (4 + o)).toNat

/-- The `bytes` argument whose length word is at argument-relative offset `o`. -/
abbrev dPayload (cd : ByteArray) (o : Nat) : ByteArray :=
  ByteArray.mk (((dArgs cd).drop (o + 32)).take (dWord cd o)).toArray

/-- The `bytes` argument at relative offset `o` lies inside the calldata. -/
def dBytesOk (cd : ByteArray) (o : Nat) : Prop :=
  4 + o + 32 ≤ cd.size ∧ 4 + o + 32 + dWord cd o ≤ cd.size

/-- Every `deposit` argument decodes. -/
def dArgsOk (cd : ByteArray) : Prop :=
  132 ≤ cd.size ∧ dBytesOk cd (dWord cd 0) ∧ dBytesOk cd (dWord cd 32) ∧ dBytesOk cd (dWord cd 64)

theorem cd_toList_length (cd : ByteArray) : cd.toList.length = cd.size := by
  rw [byteArray_toList_eq, Array.length_toList]; rfl

theorem dReadBytes_ok (cd : ByteArray) (o n : Nat) (h : 4 + o + n ≤ cd.size) :
    readBytes? (dArgs cd) o n = some (((dArgs cd).drop o).take n) := by
  unfold readBytes?
  rw [if_pos (by rw [List.length_take, List.length_drop, List.length_drop, cd_toList_length]; omega)]

theorem dReadBytes_none (cd : ByteArray) (o n : Nat) (h : cd.size < 4 + o + n) (hn : 0 < n) :
    readBytes? (dArgs cd) o n = none := by
  unfold readBytes?
  rw [if_neg (by rw [List.length_take, List.length_drop, List.length_drop, cd_toList_length]; omega)]

theorem dReadNat_ok (cd : ByteArray) (o : Nat) (h : 4 + o + 32 ≤ cd.size) :
    readNat? (dArgs cd) o = some (dWord cd o) := by
  unfold readNat? readWord?
  rw [dReadBytes_ok cd o 32 h]
  have hword : bytesToWord (((dArgs cd).drop o).take 32) = calldataWord cd (4 + o) := by
    have h' := decode_word_at_eq_any cd (4 + o) (by omega)
    simpa [dArgs, List.drop_drop, Nat.add_comm] using h'
  simp only [Option.bind, bind, hword]
  rfl

theorem dReadNat_none (cd : ByteArray) (o : Nat) (h : cd.size < 4 + o + 32) :
    readNat? (dArgs cd) o = none := by
  unfold readNat? readWord?
  rw [dReadBytes_none cd o 32 h (by decide)]
  rfl

theorem dWord_lt (cd : ByteArray) (o : Nat) : dWord cd o < 2 ^ 256 :=
  (calldataWord cd (4 + o)).val.isLt

theorem dBytes_ok (cd : ByteArray) (o : Nat) (hok : dBytesOk cd o)
    (hsmall : cd.size < 2 ^ 64) :
    decodeABIValue? .bytes (dArgs cd) o =
      some (.bytes (dPayload cd o), o + 32 + paddedSize (dWord cd o)) := by
  obtain ⟨hw, hp⟩ := hok
  have hmax : ¬ solcMaxU64 < dWord cd o := by unfold solcMaxU64; omega
  simp only [decodeABIValue?, dReadNat_ok cd o hw, solcMaxLen_modern, hmax, if_false,
    dReadBytes_ok cd (o + 32) (dWord cd o) (by omega), bind, Option.bind]

theorem dBytes_none (cd : ByteArray) (o : Nat) (hbad : ¬ dBytesOk cd o) :
    decodeABIValue? .bytes (dArgs cd) o = none := by
  unfold dBytesOk at hbad
  by_cases hw : 4 + o + 32 ≤ cd.size
  · have hp : cd.size < 4 + (o + 32) + dWord cd o := by omega
    by_cases hmax : solcMaxU64 < dWord cd o
    · simp only [decodeABIValue?, dReadNat_ok cd o hw, solcMaxLen_modern, hmax, if_true,
        bind, Option.bind]
    · simp only [decodeABIValue?, dReadNat_ok cd o hw, solcMaxLen_modern, hmax, if_false,
        dReadBytes_none cd (o + 32) (dWord cd o) hp (by omega), bind, Option.bind]
  · simp only [decodeABIValue?, dReadNat_none cd o (by omega), bind, Option.bind]

/-- The `bytes32` argument's 32 calldata bytes. -/
abbrev dRootBytes (cd : ByteArray) : List UInt8 := (((dArgs cd).drop 96).take 32).take 32

/-- The decoded `deposit` arguments. -/
abbrev dStore (cd : ByteArray) : Store :=
  ((((∅ : Store).insert "pubkey" (.bytes (dPayload cd (dWord cd 0)))).insert
    "withdrawal_credentials" (.bytes (dPayload cd (dWord cd 32)))).insert
    "signature" (.bytes (dPayload cd (dWord cd 64)))).insert
    "deposit_data_root" (.fixedBytes ⟨31, by decide⟩ (dRootBytes cd))

abbrev depositNames : List Ident :=
  ["pubkey", "withdrawal_credentials", "signature", "deposit_data_root"]

abbrev depositTypes : List ABIType :=
  [.bytes, .bytes, .bytes, .elem (.bytes ⟨31, by decide⟩)]

theorem dRootDecode (cd : ByteArray) (hn : 132 ≤ cd.size) :
    decodeABIValue? (.elem (.bytes ⟨31, by decide⟩)) (dArgs cd) 96 =
      some (.fixedBytes ⟨31, by decide⟩ (dRootBytes cd), 96 + 32) := by
  simp [decodeABIValue?, readBytes?, zeroPadding?, dRootBytes, cd_toList_length,
    show 32 ≤ cd.size - 100 by omega]

theorem depositDecodeArgs_ok {cd : ByteArray} (hok : dArgsOk cd) (hsmall : cd.size < 2 ^ 64) :
    decodeCalldata depositNames depositTypes cd = some (dStore cd) := by
  obtain ⟨hn, h0, h1, h2⟩ := hok
  have hlen := cd_toList_length cd
  have hargs : (dArgs cd).length = cd.size - 4 := by rw [List.length_drop, hlen]
  have hmax : ∀ o, 4 + o + 32 ≤ cd.size → ¬ solcMaxU64 < o := by
    intro o ho; unfold solcMaxU64; omega
  unfold decodeCalldata
  rw [if_neg (by rw [hlen]; omega), if_neg (by rw [hlen]; omega)]
  simp only [decodeCalldata.decodeArgs, depositTypes, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, solcTotalSizeDynamicGuard, List.isEmpty, Bool.false_eq_true,
    false_and, if_false, bind, Option.bind]
  rw [if_neg (by rw [hargs]; omega)]
  simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
    dReadNat_ok cd 0 (by omega), dReadNat_ok cd 32 (by omega), dReadNat_ok cd 64 (by omega),
    solcMaxLen_modern, hmax _ h0.1, hmax _ h1.1, hmax _ h2.1, if_false,
    dBytes_ok cd _ h0 hsmall, dBytes_ok cd _ h1 hsmall, dBytes_ok cd _ h2 hsmall,
    dRootDecode cd hn, staticABIEncodedSize?, bind, Option.bind, Bool.false_eq_true]
  simp [decodeCalldata.insertValues, dStore, hlen, show ¬ cd.size - 4 < 128 by omega]

theorem depositDecodeArgs_none {cd : ByteArray} (hbad : ¬ dArgsOk cd) (hsmall : cd.size < 2 ^ 64) :
    decodeCalldata depositNames depositTypes cd = none := by
  have hlen := cd_toList_length cd
  have hargs : (dArgs cd).length = cd.size - 4 := by rw [List.length_drop, hlen]
  have hmax : ∀ o, 4 + o + 32 ≤ cd.size → ¬ solcMaxU64 < o := by
    intro o ho; unfold solcMaxU64; omega
  unfold decodeCalldata
  by_cases h4 : cd.size < 4
  · rw [if_pos (by rw [hlen]; exact h4)]
  rw [if_neg (by rw [hlen]; exact h4), if_neg (by rw [hlen]; omega)]
  simp only [decodeCalldata.decodeArgs, depositTypes, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, solcTotalSizeDynamicGuard, List.isEmpty, Bool.false_eq_true,
    false_and, if_false, bind, Option.bind]
  by_cases hn : 132 ≤ cd.size
  · rw [if_neg (by rw [hargs]; omega)]
    unfold dArgsOk at hbad
    by_cases h0 : dBytesOk cd (dWord cd 0)
    · by_cases h1 : dBytesOk cd (dWord cd 32)
      · have h2 : ¬ dBytesOk cd (dWord cd 64) := fun h2 => hbad ⟨hn, h0, h1, h2⟩
        by_cases hcap : solcMaxU64 < dWord cd 64
        · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
            dReadNat_ok cd 0 (by omega), dReadNat_ok cd 32 (by omega), dReadNat_ok cd 64 (by omega),
            solcMaxLen_modern, hmax _ h0.1, hmax _ h1.1, hcap, if_false,
            dBytes_ok cd _ h0 hsmall, dBytes_ok cd _ h1 hsmall, bind, Option.bind]
          all_goals simp
        · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
            dReadNat_ok cd 0 (by omega), dReadNat_ok cd 32 (by omega), dReadNat_ok cd 64 (by omega),
            solcMaxLen_modern, hmax _ h0.1, hmax _ h1.1, hcap, if_false,
            dBytes_ok cd _ h0 hsmall, dBytes_ok cd _ h1 hsmall, dBytes_none cd _ h2, bind,
            Option.bind]
          all_goals simp
      · by_cases hcap : solcMaxU64 < dWord cd 32
        · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
            dReadNat_ok cd 0 (by omega), dReadNat_ok cd 32 (by omega),
            solcMaxLen_modern, hmax _ h0.1, hcap, if_false, dBytes_ok cd _ h0 hsmall, bind,
            Option.bind]
          all_goals simp
        · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
            dReadNat_ok cd 0 (by omega), dReadNat_ok cd 32 (by omega),
            solcMaxLen_modern, hmax _ h0.1, hcap, if_false, dBytes_ok cd _ h0 hsmall,
            dBytes_none cd _ h1, bind, Option.bind]
          all_goals simp
    · by_cases hcap : solcMaxU64 < dWord cd 0
      · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
          dReadNat_ok cd 0 (by omega), solcMaxLen_modern, hcap, bind, Option.bind]
        all_goals simp
      · simp only [decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add,
          dReadNat_ok cd 0 (by omega), solcMaxLen_modern, hcap, if_false, dBytes_none cd _ h0,
          bind, Option.bind]
        all_goals simp
  · simp [hlen, show cd.size - 4 < 128 by omega]

theorem depositDecode_ok {I : ExecutionEnv} (hok : dArgsOk I.calldata)
    (hsmall : I.calldata.size < 2 ^ 64) :
    config.externalABI.decodeCalldata? (depositTransition.params.map Param.name)
      (transitionSignature depositTransition).paramTypes I.calldata = some (dStore I.calldata) := by
  show decodeCalldata depositNames depositTypes I.calldata = _
  exact depositDecodeArgs_ok hok hsmall

theorem depositDecode_none {I : ExecutionEnv} (hbad : ¬ dArgsOk I.calldata)
    (hsmall : I.calldata.size < 2 ^ 64) :
    config.externalABI.decodeCalldata? (depositTransition.params.map Param.name)
      (transitionSignature depositTransition).paramTypes I.calldata = none := by
  show decodeCalldata depositNames depositTypes I.calldata = _
  exact depositDecodeArgs_none hbad hsmall

end FeProofs.Deposit
