import Reasoning.Constructor
import Reasoning.Memory
import Reasoning.VyperCalls

/-!
# Deployments of a constructor taking one `uint256`

Solidity-style deployment appends the argument's 32-byte big-endian word to the initcode; no other
argument list encodes.

-- LIBRARY CANDIDATE: `Reasoning/Constructor.lean` (generalizes the per-example deployment-shape
-- lemmas such as `ctorStoreDeployment_shape`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs

/-- Reading a whole ABI argument word returns its bytes. -/
theorem readBytes_all32 (b : ByteArray) (h : b.size = 32) : b.readBytes 0 32 = b := by
  apply ByteArray.ext
  apply Array.ext'
  rw [readBytes_at_toList_any b 0 (by omega), List.drop_zero]
  exact List.take_of_length_le (by rw [Array.length_toList]; exact Nat.le_of_eq h)

/-- A copied constructor argument word can be loaded from its destination, independently of
    the initcode prefix and the memory already present below the destination. -/
theorem ctorLoadWord (code mem : ByteArray) (off : Nat) (w : UInt256)
    (hmem : mem.size ≤ off) (hoff : off < 2 ^ 32) :
    memLoad (UInt256.ofNat off)
      ((code ++ (EVM.Word.toBytesBE w).toByteArray).write code.size mem off 32) = w := by
  let tail := (EVM.Word.toBytesBE w).toByteArray
  change memLoad (UInt256.ofNat off) ((code ++ tail).write code.size mem off 32) = w
  have htail : tail.size = 32 := word_toBytesBE_toByteArray_size w
  have hgap : off - mem.size < USize.size :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le hoff USize.le_size)
  have heq : (code ++ tail).write code.size mem off 32 =
      (mem ++ ByteArray.zeroes (off - mem.size)) ++ tail := by
    rw [write_from_gap_eq _ _ _ _ _ (by decide) (by rw [ByteArray.size_append, htail]) hmem hgap,
      extract_append_right' code tail code.size (code.size + 32) rfl (by rw [htail])]
  have hpre : (mem ++ ByteArray.zeroes (off - mem.size)).size = off := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
  have hsz : off + 32 ≤ ((code ++ tail).write code.size mem off 32).size := by
    rw [heq, ByteArray.size_append, hpre, htail]
  refine memLoad_of_read _ off w (by simp only [UInt256.size]; omega) (by omega) ?_
  rw [readWithPadding_eq_extract _ off hsz, heq,
    extract_append_right' _ _ off (off + 32) hpre.symm (by rw [hpre, htail])]
  exact word_toBytesBE_toByteArray_eq_toByteArray w

theorem uint256CtorDeployment_shape {name : Ident} {initcode d : ByteArray} {args : List Value}
    (h : genSolidityConstructorDeployment [{ name := name, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
      initcode args = some d) :
    ∃ i : Int, args = [.int i] ∧ 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) ∧
      d = initcode ++ (EVM.Word.toBytesBE (EVM.word i.toNat)).toByteArray := by
  cases args with
  | nil =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
              abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
              encodeABIWord?] at h
      | nil =>
          cases arg with
          | int i =>
              by_cases hbounds : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
              · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?, hbounds] at h
                change (((if i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (initcode ++ args.toByteArray)) = some d at h
                split at h
                · simp at h
                  exact ⟨i, rfl, hbounds.1, hbounds.2, h.symm⟩
                · rename_i hnot
                  exact False.elim (hnot hbounds.2)
              · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat)
                    else none).bind fun word => some word.toBytesBE).bind
                    fun args => some (initcode ++ args.toByteArray)) = some d at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | _ =>
              simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                encodeABIWord?] at h

end FeProofs
