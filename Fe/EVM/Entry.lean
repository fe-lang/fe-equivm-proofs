import Fe.EVM.Refine
import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Solc

/-!
# Reasoning about an exported runtime entry

Facts that proofs about `fe-lean-export`'s runtime entry share, whatever the contract: word
arithmetic the std decoder and encoder perform, the selector word, and how an entry that stops
relates to a hand-written one that returns.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Words -/

theorem toNat0 : (UInt256.ofNat 0).toNat = 0 := rfl
theorem toNat4 : (UInt256.ofNat 4).toNat = 4 := rfl
theorem toNat32 : (UInt256.ofNat 32).toNat = 32 := rfl
theorem toNat64 : (UInt256.ofNat 64).toNat = 64 := rfl
theorem toNat96 : (UInt256.ofNat 96).toNat = 96 := rfl
theorem add0_32 : UInt256.ofNat 0 + UInt256.ofNat 32 = UInt256.ofNat 32 := rfl
theorem add32_32 : UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 := rfl
theorem add64_32 : UInt256.ofNat 64 + UInt256.ofNat 32 = UInt256.ofNat 96 := rfl
theorem ne32 : UInt256.ofNat 32 ≠ UInt256.ofNat 0 := by decide
theorem ne64 : UInt256.ofNat 64 ≠ UInt256.ofNat 0 := by decide
theorem ne96 : UInt256.ofNat 96 ≠ UInt256.ofNat 0 := by decide
theorem at4 : (UInt256.ofNat 0 + UInt256.ofNat 4).toNat = 4 := rfl
theorem at36 : (UInt256.ofNat 0 + (UInt256.ofNat 4 + UInt256.ofNat 32)).toNat = 36 := rfl
theorem toNat4_32 : (UInt256.ofNat 4 + UInt256.ofNat 32).toNat = 36 := rfl
theorem at68 :
    (UInt256.ofNat 0 + (UInt256.ofNat 4 + UInt256.ofNat 32 + UInt256.ofNat 32)).toNat = 68 := rfl
theorem toNatMax : (~~~UInt256.ofNat 0).toNat = UInt256.size - 1 := by decide
theorem toNatU64 : (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 := rfl
theorem sub32_0 : (UInt256.ofNat 32 - UInt256.ofNat 0).toNat = 32 := rfl

theorem add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply u256_inj
  rw [uadd_toNat, toNat0, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

/-- A length below `2 ^ 64` survives std's cast to `u64`: minus the view's base 0, masked, then
    cut to 64 bits. -/
theorem truncate_size (n : Nat) (h : n < 2 ^ 64) :
    truncate 64 ((UInt256.ofNat n).sub (UInt256.ofNat 0) &&& UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat n := by
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat n).sub (UInt256.ofNat 0) = UInt256.ofNat n := by
    apply u256_inj
    exact (usub_toNat (a := UInt256.ofNat n) (b := UInt256.ofNat 0) (Nat.zero_le _)).trans
      (Nat.sub_zero _)
  have hmask : (UInt256.ofNat 18446744073709551615).toNat = 2 ^ 64 - 1 := rfl
  have hand : (UInt256.ofNat n &&& UInt256.ofNat 18446744073709551615).toNat = n := by
    change (UInt256.land _ _).toNat = n
    rw [uland_toNat, hn, hmask]
    change Nat.land n (2 ^ 64 - 1) = n
    rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt h]
  rw [hsub]
  apply u256_inj
  unfold truncate
  rw [hand, Nat.mod_eq_of_lt h]

/-- Signed comparison of two words below `2 ^ 255` is comparison of their values. -/
theorem sltBool_small {a b : UInt256} (ha : a.toNat < 2 ^ 255) (hb : b.toNat < 2 ^ 255) :
    a.sltBool b = decide (a.toNat < b.toNat) := by
  unfold UInt256.sltBool
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

/-- Std's head check on calldata of `size` bytes, at least a selector and below `2 ^ 64`:
    `(size - 4) <s need`, signed, is `size - 4 < need`. -/
theorem headCheck {size need : Nat} (hlo : 4 ≤ size) (hfits : size < 2 ^ 64)
    (hneed : need < 2 ^ 64) :
    (UInt256.ofNat size - UInt256.ofNat 4).sltBool (UInt256.ofNat need) =
      decide (size - 4 < need) := by
  have hn : (UInt256.ofNat size).toNat = size := ulit_toNat' _ (by unfold UInt256.size; omega)
  have hm : (UInt256.ofNat need).toNat = need := ulit_toNat' _ (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat size - UInt256.ofNat 4).toNat = size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat size) (b := UInt256.ofNat 4) (by rw [hn, toNat4]; omega)
    rw [hn, toNat4] at h
    exact h
  rw [sltBool_small (by rw [hsub]; omega) (by rw [hm]; omega), hsub, hm]

/-! ## Memory after a return -/

/-- Memory after `return_value` encodes the word `v` into a fresh 32-byte buffer. -/
def returned (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0
    ((⟨Array.replicate 32 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 32 0⟩) memory.size 32)
    memory.size 32

/-- The word written into the fresh buffer reads back. -/
theorem returned_read (memory : ByteArray) (v : UInt256) :
    (v.toByteArray.write 0
        ((⟨Array.replicate 32 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 32 0⟩)
          memory.size 32)
        memory.size 32).readWithPadding memory.size 32 = v.toByteArray := by
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  apply toByteArray_write32_read_back
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hzeros])
    (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]
  omega

/-- An empty return ends the call with no data and changes nothing. -/
theorem returnNone_exec (I : ExecutionEnv) (w : World) :
    (returnData (UInt256.ofNat 0) (UInt256.ofNat 0)).exec I w =
      some (.error (.stop ByteArray.empty w)) := by
  simp [returnData, toNat0, byteArray_readWithPadding_zero]

/-! ## The selector -/

/-- The selector word: the first four bytes of calldata as a number. -/
abbrev selWord (cd : ByteArray) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩

theorem selector_exec (I : ExecutionEnv) (w : World) :
    calldataSelector.exec I w = some (.ok (selWord I.calldata, w)) := rfl

theorem selWord_hit {cd sel : ByteArray} {word : UInt256}
    (h : UInt256.eq word (selWord cd) = if (sel == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩)
    (hsel : (sel == cd.extract 0 4) = true) : selWord cd = word := by
  rw [hsel, if_pos rfl] at h
  by_contra hne
  rw [u256_eq_of_ne (fun e => hne e.symm)] at h
  exact absurd h (by decide)

theorem selWord_miss {cd sel : ByteArray} {word : UInt256}
    (h : UInt256.eq word (selWord cd) = if (sel == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩)
    (hsel : (sel == cd.extract 0 4) = false) : selWord cd ≠ word := by
  intro e
  rw [hsel, e, u256_eq_refl] at h
  exact absurd h (by decide)

/-! ## Entries -/

/-- An entry as a computation of return data: it never returns, so it has none to give. -/
def entry (m : FeM Empty) : FeM ByteArray := m >>= fun e => nomatch e

theorem entry_exec {m : FeM Empty} {I : ExecutionEnv} {w : World} {f : Exit World}
    (h : m.exec I w = some (.error f)) : (entry m).exec I w = some (.error f) := by
  simp [entry, h]

/-- With calldata below `2 ^ 64` bytes, std's head check is the one a hand-written entry makes. -/
theorem badHead_iff (cd : ByteArray) (words : Nat) (hfits : cd.size < 2 ^ 64) :
    BadHead cd words ↔ cd.size < 4 + 32 * words := by
  unfold BadHead
  constructor
  · rintro (h | h)
    · exact h
    · omega
  · exact Or.inl

/-- An entry that runs `arm` and returns its result through `ret` ends as a run of `arm` that
    returns the encoding `enc` of its result, when `ret` stops with that encoding and changes
    memory only, and `arm` leaves memory alone. -/
theorem endsAs_arm {α : Type} {arm : FeM α} {ret : α → FeM Empty} {enc : α → ByteArray}
    {I : ExecutionEnv} {w : World}
    (hret : ∀ r w', w'.memory.size < UInt256.size →
      ∃ memory, (ret r).exec I w' = some (.error (.stop (enc r) { w' with memory := memory })))
    (hkeep : KeepsMemory arm) (hmem : w.memory.size < UInt256.size) :
    EndsAs ((entry (arm >>= ret)).exec I w) ((arm >>= fun r => pure (enc r)).exec I w) := by
  cases h : arm.exec I w with
  | none => simp [entry, h]; exact .diverge
  | some res =>
    cases res with
    | error f => simp [entry, h]; exact .exit f
    | ok p =>
      obtain ⟨r, w'⟩ := p
      obtain ⟨memory, hr⟩ := hret r w' (by rw [hkeep I w r w' h]; exact hmem)
      simp [entry, h, hr]
      exact .stop_ok rfl rfl

end Fe.EVM
