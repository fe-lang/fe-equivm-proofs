import Reasoning.ABI
import Reasoning.Solc
import Reasoning.Dispatch

/-!
# ABI decoding facts shared by the contracts

Fe's canonical-`address` check `SHR(160, word) = 0` and fixed-width scalar decoding.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs

/-! ## Selectors -/

/-- The selector word as the dispatcher's blocks compute it, `SHR(224, CALLDATALOAD(0))`. -/
theorem selWord_eq {I : ExecutionEnv} {w : UInt256} (h : solcSelectorWord I = w) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32))
      (UInt256.ofNat 224) = w := h

/-! ## Head-length check -/

/-- Fe's head check `SLT(CALLDATASIZE - 4, 32 * words)` fails for calldata shorter than the head
or of at least `2^255 + 4` bytes (stated as the block summaries' branch condition). -/
theorem solcDecodeLenCheckBad (words : ℕ) {sz : ℕ} (hhead : 4 ≤ sz) (hsz : sz < UInt256.size)
    (hbad : sz < 4 + 32 * words ∨ 2 ^ 255 + 4 ≤ sz) (hneed : 32 * words < 2 ^ 255 := by norm_num) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) (UInt256.ofNat 4)) (UInt256.ofNat (32 * words)) ≠
      UInt256.ofNat 0 :=
  ne_of_eq_of_ne (hbad.elim (solcCalldataStaticLenCheckShort hhead · hsz hneed)
    (solcCalldataStaticLenCheckHuge · hsz hneed)) (by decide)

/-! ## `address` arguments -/

theorem shiftRight160_toNat (w : UInt256) :
    (UInt256.shiftRight w ⟨160⟩).toNat = w.toNat / EVM.twoPow 160 := by
  unfold UInt256.shiftRight
  rw [if_neg (by decide)]
  change (w.val.val >>> 160) % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.shiftRight_eq_div_pow]
  change w.toNat / 2 ^ 160 % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt
    (Nat.div_le_self w.toNat (2 ^ 160)) w.val.isLt)]
  rfl

theorem shiftRight160_eq_zero {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.shiftRight w (UInt256.ofNat 160) = UInt256.ofNat 0 := by
  apply u256_inj
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0
  rw [shiftRight160_toNat]
  rw [Nat.div_eq_of_lt]
  simpa [EVM.addressModulus] using hcanon

theorem shiftRight160_ne_zero {w : UInt256} (hdirty : EVM.addressModulus ≤ w.toNat) :
    UInt256.shiftRight w (UInt256.ofNat 160) ≠ UInt256.ofNat 0 := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0 at hnat
  rw [shiftRight160_toNat] at hnat
  rw [Nat.div_eq_zero_iff] at hnat
  rcases hnat with hpow | hlt
  · exact (by decide +kernel : EVM.twoPow 160 ≠ 0) hpow
  · exact (not_lt_of_ge (by simpa [EVM.addressModulus] using hdirty)) hlt

/-! ## Scalar arguments -/

/-- Assemble scalar decodings at successive 32-byte offsets. -/
theorem decodeScalarWords_of_indexed {bytes : List UInt8} (tys : List ABIType)
    (vals : List Value) (start : Nat) (hlen : tys.length = vals.length)
    (hword : ∀ i ty value, tys[i]? = some ty → vals[i]? = some value →
      decodeScalarWord? ty bytes (start + 32 * i) = some (value, start + 32 * i + 32)) :
    decodeScalarWords? tys bytes start = some vals := by
  induction tys generalizing vals start with
  | nil =>
    cases vals with
    | nil => rfl
    | cons v vs => simp at hlen
  | cons ty ts ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      have hl : ts.length = vs.length := by simpa using hlen
      have hfirst := hword 0 ty v (by simp) (by simp)
      simp only [Nat.mul_zero, Nat.add_zero] at hfirst
      have hrest : ∀ i ty' value, ts[i]? = some ty' → vs[i]? = some value →
          decodeScalarWord? ty' bytes (start + 32 + 32 * i) =
            some (value, start + 32 + 32 * i + 32) := by
        intro i ty' value ht hv
        have hp := hword (i + 1) ty' value (by simpa using ht) (by simpa using hv)
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hp
      simp only [decodeScalarWords?, hfirst, bind, Option.bind]
      rw [ih vs (start + 32) hl hrest]

/-- Decode any number of complete `uint256` words from the calldata head. -/
theorem decodeScalarWords_uint256s (cd : ByteArray) (n start : Nat)
    (hsz : 4 + start + 32 * n ≤ cd.size) :
    decodeScalarWords? (List.replicate n abiUInt256) (cd.toList.drop 4) start =
      some ((List.range n).map fun i =>
        .int (Int.ofNat (calldataWord cd (4 + start + 32 * i)).toNat)) := by
  apply decodeScalarWords_of_indexed
  · simp
  · intro i ty value hty hval
    have ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hty
    simp only [List.length_replicate] at hi
    simp only [List.getElem?_replicate, if_pos hi, Option.some.injEq] at hty
    subst ty
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at hval
    subst value
    have hlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hread : (((cd.toList.drop 4).drop (start + 32 * i)).take 32).length = 32 := by
      rw [List.drop_drop, List.length_take, List.length_drop, hlen]
      omega
    have hword : ABI.bytesToWord (((cd.toList.drop 4).drop (start + 32 * i)).take 32) =
        calldataWord cd (4 + start + 32 * i) := by
      simpa only [List.drop_drop, Nat.add_assoc] using
        (decode_word_at_eq_any cd (4 + start + 32 * i) (by omega))
    simp only [List.getElem_replicate]
    rw [decodeScalarWord_uint256_ok hread, hword]

/-- Lift scalar-word decoding through the selector and size guards. -/
theorem decodeCalldata_scalars {cd : ByteArray} {names : List Ident}
    {tys : List ABIType} {vals : List Value}
    (hscalar : tys.all isABIScalarWordType = true) (hhead : 4 ≤ cd.size)
    (hbig : tys ≠ [] → cd.size < 2 ^ 255 + 4)
    (hdecoded : decodeScalarWords? tys (cd.toList.drop 4) 0 = some vals) :
    decodeCalldata names tys cd = decodeCalldata.insertValues names vals ∅ := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq hscalar]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨hnonempty, hlarge⟩
    have hn : tys ≠ [] := by
      intro hempty
      subst tys
      simp at hnonempty
    have hb := hbig hn
    rw [List.length_drop, hlen] at hlarge
    omega)]
  rw [hdecoded]

/-- Decode a fixed-width `uint256` head, inserting values in argument order. -/
theorem decodeCalldata_uint256s {cd : ByteArray} (names : List Ident)
    (hsz : 4 + 32 * names.length ≤ cd.size)
    (hbig : names ≠ [] → cd.size < 2 ^ 255 + 4) :
    decodeCalldata names (List.replicate names.length abiUInt256) cd =
      decodeCalldata.insertValues names
        ((List.range names.length).map fun i =>
          .int (Int.ofNat (calldataWord cd (4 + 32 * i)).toNat)) ∅ := by
  apply decodeCalldata_scalars (by simp [List.all_replicate, isABIScalarWordType]) (by omega)
  · intro _
    apply hbig
    intro hempty
    subst names
    simp_all
  · simpa using decodeScalarWords_uint256s cd names.length 0 (by simpa using hsz)

theorem decodeCalldata_uint256_uint256_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  exact decodeCalldata_uint256s (cd := cd) [x, y] (by simpa using hsz68) (by intro _; exact hbig)

theorem decodeCalldata_uint256_uint256_none_short {cd : ByteArray} {x y : Ident}
    (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_short (by decide) (by simpa using hshort)

theorem decodeCalldata_uint256_uint256_none_huge {cd : ByteArray} {x y : Ident}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none :=
  decodeCalldata_scalar_none_huge (by decide) rfl hhuge

/-- `~~~w`, the bitwise complement. -/
theorem complement_toNat (w : UInt256) :
    (UInt256.complement w).toNat = EVM.wordModulus - 1 - w.toNat := by
  rw [show EVM.wordModulus = UInt256.size by decide]
  unfold UInt256.complement UInt256.toNat
  rw [Fin.val_sub, Fin.val_add]
  change (UInt256.size - ((w.val.val + 1) % UInt256.size)) % UInt256.size =
    UInt256.size - 1 - w.val.val
  have hle : w.val.val + 1 ≤ UInt256.size := by omega
  by_cases heq : w.val.val + 1 = UInt256.size
  · rw [heq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    omega
  · have hlt : w.val.val + 1 < UInt256.size := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hpos : 0 < UInt256.size - (w.val.val + 1) := by omega
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end FeProofs
