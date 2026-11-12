import FeProofs.Common.Abi

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory FeProofs

-- Empty heads accept any size at or above the selector, even past the signed limit.
example {cd : ByteArray} (h4 : 4 ≤ cd.size) : decodeCalldata [] [] cd = some ∅ := by
  simpa [decodeCalldata.insertValues] using
    (decodeCalldata_uint256s (cd := cd) [] (by simpa using h4) (by simp))

example {cd : ByteArray} (hshort : cd.size < 4) : decodeCalldata [] [] cd = none :=
  decodeCalldata_scalar_none_short (by decide) (by simpa using hshort)

example {cd : ByteArray} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata ["x"] [abiUInt256] cd = none :=
  decodeCalldata_scalar_none_huge (by decide) rfl hbig

example {cd : ByteArray} (h4 : 4 ≤ cd.size) : decodeCalldata ["x"] [] cd = none := by
  simpa [decodeCalldata.insertValues] using
    (decodeCalldata_scalars (cd := cd) (names := ["x"]) (tys := []) (vals := [])
      (by decide) h4 (by simp) rfl)

-- Repeated names are inserted in order, so the later value overwrites the earlier one.
example {cd : ByteArray} (hsz : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata ["x", "x"] [abiUInt256, abiUInt256] cd =
      some (((∅ : Store).insert "x" (.int (Int.ofNat (calldataWord cd 4).toNat))).insert "x"
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  simpa [decodeCalldata.insertValues] using
    (decodeCalldata_uint256s (cd := cd) ["x", "x"] (by simpa using hsz) (by intro _; exact hbig))

-- The induction also composes mixed scalar types with their own validity checks.
example (bytes : List UInt8) (address boolean : Value)
    (ha : decodeScalarWord? abiAddress bytes 0 = some (address, 32))
    (hb : decodeScalarWord? abiBool bytes 32 = some (boolean, 64)) :
    decodeScalarWords? [abiAddress, abiBool] bytes 0 = some [address, boolean] := by
  apply decodeScalarWords_of_indexed
  · rfl
  · intro i ty value ht hv
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hv
      subst ty; subst value
      simpa using ha
    | succ i =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ht hv
        subst ty; subst value
        simpa using hb
      | succ i => simp at ht

-- Invalid scalar words do not become successful arguments through the shared theorem.
example {bytes : List UInt8} (hlen : (bytes.take 32).length = 32)
    (hbad : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiAddress] bytes 0 = none := by
  have h := decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen)
    (by simpa using hbad)
  simp [decodeScalarWords?, h]

example {bytes : List UInt8} (hlen : (bytes.take 32).length = 32)
    (hzero : ABI.bytesToWord (bytes.take 32) ≠ ⟨0⟩)
    (hone : ABI.bytesToWord (bytes.take 32) ≠ ⟨1⟩) :
    decodeScalarWords? [abiBool] bytes 0 = none := by
  have h := decodeScalarWord_bool_none_noncanon (start := 0) (by simpa using hlen)
    (by simpa using hzero) (by simpa using hone)
  simp [decodeScalarWords?, h]
