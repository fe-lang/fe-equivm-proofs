import FeProofs.WETH9.SonatinaLoad

/-!
# FeWETH9's `%return_value__g7f54`, run

`%return_value ptr size` returns a dynamic string's ABI encoding: at the free pointer it zeroes
`32 + size` bytes (a `calldatacopy` from the end of calldata), stores the offset word 32, copies
the `size` bytes at `ptr` (the length word and the padded bytes) after it, and returns the
`32 + size` bytes.  It fails with `Panic(0x41)` at `2 ^ 64` bytes, as std's `alloc_bytes` does.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Reasoning.Theory

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

set_option maxHeartbeats 4000000 in
/-- `%return_value ptr size` from memory whose free pointer is its end: it returns the offset
    word 32 and the `size` bytes at `ptr`. -/
theorem returnValue_run (hf : m.func? "return_value__g7f54" = some returnValueFunc)
    (ptr S : Nat) (M : ByteArray)
    (hfp : uInt256OfByteArray (M.readWithPadding 64 32) = UInt256.ofNat M.size)
    (hin : ptr + S ≤ M.size) (hS : 0 < S) (hM : M.size < 2 ^ 128) (hS64 : S < 2 ^ 64)
    (hcd : I.calldata.size < 2 ^ 64) :
    (runFunc m ic "return_value__g7f54" [Val.int 256 ptr, Val.int 256 S]).exec I
        { w with memory := M } =
      if 32 + S < 2 ^ 64 then
        some (.error (.stop ((UInt256.ofNat 32).toByteArray ++ M.extract ptr (ptr + S))
          { w with memory := M ++ ((UInt256.ofNat 32).toByteArray ++ M.extract ptr (ptr + S)) }))
      else some (.error (.revert (panicData 65))) := by
  rw [runFunc_entry hf rfl]
  by_cases h64 : 32 + S < 2 ^ 64
  · rw [if_pos h64]
    simp [Fe.Sonatina.bind]
    repeat ir_step_nat
    have hX : (M.extract ptr (ptr + S)).size = S := by rw [ByteArray.size_extract]; omega
    rw [copy_past_end _ _ le_rfl le_rfl, write_end _ _ rfl,
      copy_to_end _ (by omega) (by rw [ByteArray.size_append, toByteArray_size]; omega)
        (by rw [ByteArray.size_append, toByteArray_size]),
      extract_append_left _ _ _ _ hin, ByteArray.append_assoc]
    refine ⟨?_, rfl⟩
    rw [readWithPadding_tail M _ 0 (32 + S) (by omega) (by omega)
        (by rw [ByteArray.size_append, toByteArray_size, hX]; omega),
      show 0 + (32 + S) = ((UInt256.ofNat 32).toByteArray ++ M.extract ptr (ptr + S)).size by
        rw [ByteArray.size_append, toByteArray_size, hX]; omega, byteArray_extract_self]
  · rw [if_neg h64]
    simp [Fe.Sonatina.bind]
    repeat ir_step_nat

end FeProofs.WETH9.Sonatina
