import FeProofs.Fixtures.Exported
import Reasoning.EVMWord

/-!
# The std calldata decoder, as exported

`FeProofs.Fixtures.Decode.decode_args_u256_u256` is `Evm::decode_args<(u256, u256)>` as
`fe-lean-export` prints it from std: a view of calldata after the 4-byte selector, a frame check
of the 64-byte head, and one `calldataload` per field.  This file proves what that code does.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Fixtures.Decode

/-! ## Constants -/

theorem isSigned : IS_SIGNED = pure false := rfl
theorem mask : MASK = pure ⟨2 ^ 64 - 1⟩ := rfl
theorem isDynamic : IS_DYNAMIC = pure false := rfl
theorem headSize : HEAD_SIZE = pure ⟨32⟩ := rfl
theorem fieldHeadSize : abi_field_head_size_u256 = pure ⟨32⟩ := rfl
theorem pairHeadSize : HEAD_SIZE_u256_u256 = pure ⟨64⟩ := by
  simp [HEAD_SIZE_u256_u256, fieldHeadSize, checkedAdd]
  rfl

/-! ## Words -/

/-- A size below `2 ^ 64` survives the decoder's cast to `u64`: minus the view's base 0,
    masked, then cut to 64 bits. -/
theorem truncate_size (n : Nat) (h : n < 2 ^ 64) :
    truncate 64 ((UInt256.ofNat n).sub (UInt256.ofNat 0) &&& ⟨2 ^ 64 - 1⟩) = UInt256.ofNat n := by
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat n).sub (UInt256.ofNat 0) = UInt256.ofNat n := by
    apply u256_inj
    exact (usub_toNat (a := UInt256.ofNat n) (b := UInt256.ofNat 0) (Nat.zero_le _)).trans
      (Nat.sub_zero _)
  have hmask : ((⟨2 ^ 64 - 1⟩ : UInt256)).toNat = 2 ^ 64 - 1 := rfl
  have hand : (UInt256.ofNat n &&& (⟨2 ^ 64 - 1⟩ : UInt256)).toNat = n := by
    change (UInt256.land _ _).toNat = n
    rw [uland_toNat, hn, hmask]
    change Nat.land n (2 ^ 64 - 1) = n
    rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt h]
  rw [hsub]
  apply u256_inj
  unfold truncate
  rw [hand, Nat.mod_eq_of_lt h]

/-! ## The decoder -/

/-- The length of the calldata view: the calldata size, when that fits 64 bits. -/
theorem len_exec (I : ExecutionEnv) (w : World) (hsize : I.calldata.size < 2 ^ 64) :
    (len_CallData ⟨UInt256.ofNat 0⟩).exec I w =
      some (.ok (UInt256.ofNat I.calldata.size, w)) := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  simp [len_CallData, size, downcast_truncate_u256_u64, to_word, from_word, isSigned, mask,
    checkedSub, h0]
  exact truncate_size _ hsize

/-- `decode_args<(u256, u256)>` reverts with no data when the calldata is shorter than the
    selector and two words, and otherwise returns the two words after the selector. -/
theorem decode_args_exec (I : ExecutionEnv) (w : World) (hsize : I.calldata.size < 2 ^ 64) :
    decode_args_u256_u256.exec I w =
      if I.calldata.size < 68 then some (.error (.revert ByteArray.empty))
      else some (.ok ((word I.calldata 4, word I.calldata 36), w)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have h4 : (UInt256.ofNat 4).toNat = 4 := rfl
  have h64 : ((⟨64⟩ : UInt256)).toNat = 64 := rfl
  simp only [decode_args_u256_u256, input, new, decode_input_at_u256_u256_CallData,
    decode_frame_from_Sol_u256_u256_CallData, pairHeadSize, checked_frame_end_Sol, M.exec_bind,
    M.exec_pure, len_exec I w hsize, hn, h4, h64, pure_bind]
  by_cases hshort : I.calldata.size < 4
  · simp [hshort, decode_error, show I.calldata.size < 68 by omega]
  have hsub : (UInt256.ofNat I.calldata.size - UInt256.ofNat 4).toNat = I.calldata.size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat I.calldata.size) (b := UInt256.ofNat 4)
      (by rw [hn, h4]; omega)
    rw [hn, h4] at h
    exact h
  by_cases hhead : I.calldata.size < 68
  · simp [hshort, hsub, decode_error, hhead, show I.calldata.size - 4 < 64 by omega]
  have hat0 : (UInt256.ofNat 0 + UInt256.ofNat 4).toNat = 4 := rfl
  have hat1 : (UInt256.ofNat 0 + (UInt256.ofNat 4 + (⟨32⟩ : UInt256))).toNat = 36 := rfl
  have hfits : ¬ UInt256.size ≤ (UInt256.ofNat 4).toNat + ((⟨32⟩ : UInt256)).toNat := by decide
  simp [hshort, hsub, hhead, show ¬ I.calldata.size - 4 < 64 by omega,
    decode_from_prechecked_head_Sol_u256_u256_CallData,
    decode_field_from_prechecked_head_Sol_u256_CallData, isDynamic, fieldHeadSize,
    decode_from_Sol_CallData, word_at, checkedAdd, word, hat0, hat1, hfits]

end FeProofs.Fixtures.Decode
