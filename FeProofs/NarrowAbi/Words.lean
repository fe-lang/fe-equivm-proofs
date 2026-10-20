import FeProofs.NarrowAbi.Common

/-!
# FeNarrowAbi word facts

Calldata decoding of one scalar word, the Stele values of canonical `int8`/`address` words, the
EVM-side canonicality checks Fe compiles (`GT 255`, `SHR 160`, the `int8` low-byte/sign-extension
comparison), and the canonical return encodings.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.NarrowAbi

set_option maxRecDepth 2000000

abbrev argWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev int8Ty : ABIType := .elem (.int (.sint ⟨8, by decide⟩))

-- LIBRARY CANDIDATE: `Reasoning/SteleArithmetic.lean`; GENERALIZES `evalExpr_varInt` to any value.
/-! ## Calldata decoding of one scalar word -/

-- LIBRARY CANDIDATE: `Reasoning/ABI.lean`; GENERALIZES `decodeCalldata_uint_result` to any scalar
-- word type.
theorem decodeCalldata_word {cd : ByteArray} {name : Ident} {ty : ABIType}
    (hty : [ty].all isABIScalarWordType = true)
    (hlen : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [name] [ty] cd =
      (decodeABIWord? ty (calldataWord cd 4)).map (fun v => (∅ : Store).insert name v) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq hty]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, List.drop_zero, htake,
    ↓reduceIte, hword, bind, Option.bind]
  cases decodeABIWord? ty (calldataWord cd 4) <;> simp [decodeCalldata.insertValues]

theorem decodeCalldata_word_none_short {cd : ByteArray} {name : Ident} {ty : ABIType}
    (hty : [ty].all isABIScalarWordType = true) (hshort : cd.size < 36) :
    decodeCalldata [name] [ty] cd = none :=
  decodeCalldata_scalar_none_short hty (by simpa using hshort)

theorem decodeCalldata_word_none_huge {cd : ByteArray} {name : Ident} {ty : ABIType}
    (hty : [ty].all isABIScalarWordType = true) (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [name] [ty] cd = none :=
  decodeCalldata_scalar_none_huge hty rfl hhuge

/-! ## `int8` -/

def i8Value (w : UInt256) : Value :=
  if (↑w.val : Nat) < EVM.twoPow 7 then
    .int (Int.ofNat (↑w.val : Nat))
  else
    .int (Int.ofNat (↑w.val : Nat) - Int.ofNat EVM.wordModulus)

def i8Canonical (w : UInt256) : Prop :=
  w.toNat < EVM.twoPow 7 ∨ EVM.wordModulus - EVM.twoPow 7 ≤ w.toNat

theorem decodeWordI8_ok {w : UInt256} (hcanon : i8Canonical w) :
    decodeABIWord? int8Ty w = some (i8Value w) := by
  rcases hcanon with hpos | hneg
  · change (↑w.val : Nat) < EVM.twoPow 7 at hpos
    simp only [decodeABIWord?, i8Value]
    rw [if_neg (by decide : ¬8 = 0), if_pos hpos, if_pos hpos]
  · have hnpos : ¬w.toNat < EVM.twoPow 7 := by
      have hstart : EVM.twoPow 7 < EVM.wordModulus - EVM.twoPow 7 := by native_decide
      have hlt : w.toNat < EVM.wordModulus := w.val.isLt
      omega
    change ¬(↑w.val : Nat) < EVM.twoPow 7 at hnpos
    change EVM.wordModulus - EVM.twoPow 7 ≤ (↑w.val : Nat) at hneg
    simp only [decodeABIWord?, i8Value]
    rw [if_neg (by decide : ¬8 = 0), if_neg hnpos, if_pos hneg, if_neg hnpos]

theorem decodeWordI8_none {w : UInt256}
    (hpos : EVM.twoPow 7 ≤ w.toNat)
    (hneg : w.toNat < EVM.wordModulus - EVM.twoPow 7) :
    decodeABIWord? int8Ty w = none := by
  change EVM.twoPow 7 ≤ (↑w.val : Nat) at hpos
  change (↑w.val : Nat) < EVM.wordModulus - EVM.twoPow 7 at hneg
  simp only [decodeABIWord?]
  change (if (↑w.val : Nat) < EVM.twoPow 7 then _
    else if EVM.wordModulus - EVM.twoPow 7 ≤ (↑w.val : Nat) then _ else none) = none
  rw [if_neg (by omega), if_neg (by omega)]

theorem lowByte_toNat (w : UInt256) :
    (UInt256.land w ⟨255⟩).toNat = w.toNat % 256 := by
  rw [uland_toNat]
  change Nat.land w.toNat 255 = w.toNat % 256
  rw [show 255 = 2 ^ 8 - 1 by norm_num, nat_land_mask_eq_mod]
  norm_num

theorem lowByte_lt256 (w : UInt256) : (UInt256.land w ⟨255⟩).toNat < 256 := by
  rw [lowByte_toNat]
  exact Nat.mod_lt _ (by decide)

theorem shiftLeft248_toNat {low : UInt256} (hlow : low.toNat < 256) :
    (UInt256.shiftLeft low ⟨248⟩).toNat = low.toNat * 2 ^ 248 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide)]
  change (low.toNat <<< 248) % UInt256.size = low.toNat * 2 ^ 248
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  calc
    low.toNat * 2 ^ 248 < 256 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right hlow (by positivity)
    _ = UInt256.size := by norm_num [UInt256.size, Nat.pow_add]

theorem shiftRight248_toNat (w : UInt256) :
    (UInt256.shiftRight w ⟨248⟩).toNat = w.toNat / 2 ^ 248 := by
  unfold UInt256.shiftRight
  rw [if_neg (by decide)]
  simp only [UInt256.toNat, Fin.shiftRight_val]
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (↑(⟨248⟩ : UInt256).val : Nat) = 248 by decide]

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

theorem sarShiftLeft248_of_lt128 {low : UInt256} (hlow : low.toNat < 128) :
    UInt256.sar ⟨248⟩ (UInt256.shiftLeft low ⟨248⟩) = low := by
  apply u256_inj
  simp only [UInt256.sar]
  have hb : (UInt256.shiftLeft low ⟨248⟩).toNat < 2 ^ 255 := by
    rw [shiftLeft248_toNat (lt_trans hlow (by decide))]
    calc
      low.toNat * 2 ^ 248 < 128 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right hlow (by positivity)
      _ = 2 ^ 255 := by norm_num [Nat.pow_add]
  have hslt : UInt256.sltBool (UInt256.shiftLeft low ⟨248⟩) ⟨0⟩ = false := by
    have hnot : ¬UInt256.shiftLeft low ⟨248⟩ < (⟨0⟩ : UInt256) :=
      not_lt_of_ge (by
        show (⟨0⟩ : UInt256).val ≤ (UInt256.shiftLeft low ⟨248⟩).val
        exact Nat.zero_le _)
    unfold UInt256.sltBool
    rw [if_neg (by omega), if_neg (by decide)]
    simp [hnot]
  rw [if_neg (by simpa using hslt)]
  · change (UInt256.shiftRight (UInt256.shiftLeft low ⟨248⟩) ⟨248⟩).toNat = low.toNat
    unfold UInt256.shiftRight
    rw [if_neg (by decide)]
    simp only [UInt256.toNat]
    rw [Fin.shiftRight_val]
    change (UInt256.shiftLeft low ⟨248⟩).toNat >>> 248 = low.toNat
    rw [shiftLeft248_toNat (lt_trans hlow (by decide)), Nat.shiftRight_eq_div_pow,
      Nat.mul_comm, Nat.mul_div_right _ (by positivity)]

theorem sarShiftLeft248_of_ge128 {low : UInt256}
    (hlow : low.toNat < 256) (hsign : 128 ≤ low.toNat) :
    UInt256.sar ⟨248⟩ (UInt256.shiftLeft low ⟨248⟩) =
      UInt256.ofNat (EVM.wordModulus - 256 + low.toNat) := by
  apply u256_inj
  simp only [UInt256.sar]
  have hb : 2 ^ 255 ≤ (UInt256.shiftLeft low ⟨248⟩).toNat := by
    rw [shiftLeft248_toNat hlow]
    calc
      2 ^ 255 = 128 * 2 ^ 248 := by norm_num [Nat.pow_add]
      _ ≤ low.toNat * 2 ^ 248 := Nat.mul_le_mul_right _ hsign
  have hslt : UInt256.sltBool (UInt256.shiftLeft low ⟨248⟩) ⟨0⟩ = true := by
    unfold UInt256.sltBool
    rw [if_pos hb, if_neg (by decide)]
  rw [if_pos (by simpa using hslt)]
  · let shifted := UInt256.shiftLeft low ⟨248⟩
    have hshifted : shifted.toNat = low.toNat * 2 ^ 248 :=
      shiftLeft248_toNat hlow
    have hmod : EVM.wordModulus = 256 * 2 ^ 248 := by
      norm_num [EVM.wordModulus, EVM.twoPow, Nat.pow_add]
    have hcomp : (UInt256.complement shifted).toNat =
        (256 - low.toNat) * 2 ^ 248 - 1 := by
      rw [complement_toNat, hshifted, hmod]
      omega
    have hlowLe : low.toNat ≤ 255 := by omega
    have hdiv : ((256 - low.toNat) * 2 ^ 248 - 1) / 2 ^ 248 =
        255 - low.toNat := by
      apply Nat.div_eq_of_lt_le
      · have hpow : 0 < 2 ^ 248 := by positivity
        omega
      · have hpow : 0 < 2 ^ 248 := by positivity
        omega
    change (UInt256.complement
      (UInt256.shiftRight (UInt256.complement shifted) ⟨248⟩)).toNat =
        (UInt256.ofNat (EVM.wordModulus - 256 + low.toNat)).toNat
    rw [complement_toNat, shiftRight248_toNat, hcomp, hdiv]
    have hout : EVM.wordModulus - 256 + low.toNat < UInt256.size := by
      rw [← show EVM.wordModulus = UInt256.size by decide]
      omega
    rw [ulit_toNat' _ hout]
    omega

theorem negativeLowByte {w : UInt256}
    (hneg : EVM.wordModulus - 128 ≤ w.toNat) :
    let low := UInt256.land w ⟨255⟩
    low.toNat = w.toNat - (EVM.wordModulus - 256) ∧
      128 ≤ low.toNat ∧ low.toNat < 256 := by
  intro low
  have hword : w.toNat < EVM.wordModulus := w.val.isLt
  have hq : w.toNat / 256 = 2 ^ 248 - 1 := by
    apply Nat.div_eq_of_lt_le
    · exact le_trans (by native_decide : (2 ^ 248 - 1) * 256 ≤
        EVM.wordModulus - 128) hneg
    · rw [show (2 ^ 248 - 1 + 1) * 256 = EVM.wordModulus by native_decide]
      exact hword
  have hdecomp := Nat.div_add_mod w.toNat 256
  rw [hq] at hdecomp
  have hhigh : 256 * (2 ^ 248 - 1) = EVM.wordModulus - 256 := by native_decide
  rw [hhigh] at hdecomp
  have hlow : w.toNat % 256 = w.toNat - (EVM.wordModulus - 256) := by omega
  have hlowNat : low.toNat = w.toNat - (EVM.wordModulus - 256) := by
    change (UInt256.land w ⟨255⟩).toNat = _
    rw [lowByte_toNat, hlow]
  refine ⟨hlowNat, ?_, ?_⟩
  · rw [hlowNat]
    omega
  · rw [hlowNat]
    omega

theorem byteSignBit_of_ge128 {low : UInt256}
    (hge : 128 ≤ low.toNat) (hlt : low.toNat < 256) :
    UInt256.land low ⟨128⟩ = ⟨128⟩ := by
  apply u256_inj
  rw [uland_toNat]
  change low.toNat &&& 2 ^ 7 = 2 ^ 7
  rw [Nat.and_two_pow]
  have hdiv : low.toNat / 2 ^ 7 = 1 := by
    apply Nat.div_eq_of_lt_le <;> norm_num at hge hlt ⊢ <;> omega
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  norm_num [UInt256.size]

theorem byteSignBit_of_lt128 {low : UInt256} (h : low.toNat < 128) :
    UInt256.land low ⟨128⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [uland_toNat]
  change low.toNat &&& 2 ^ 7 = 0
  rw [Nat.and_two_pow, Nat.testBit_eq_false_of_lt h]
  rfl

theorem signExtendedLow_toNat (w : UInt256) :
    (UInt256.lor (UInt256.lnot ⟨255⟩) (UInt256.land w ⟨255⟩)).toNat =
      EVM.wordModulus - 256 + (UInt256.land w ⟨255⟩).toNat := by
  rw [u256_lor_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = EVM.wordModulus - 256 := by
    native_decide
  rw [hlnot, nat_lor_comm]
  have hhigh : EVM.wordModulus - 256 = (2 ^ 248 - 1) * 2 ^ 8 := by
    norm_num [EVM.wordModulus, EVM.twoPow, Nat.pow_add]
  rw [hhigh, nat_lor_shift_add _ _ _ (by simpa using lowByte_lt256 w)]
  rw [Nat.mod_eq_of_lt]
  · rw [← hhigh]
    omega
  · have hlt := lowByte_lt256 w
    calc
      (UInt256.land w ⟨255⟩).toNat + (2 ^ 248 - 1) * 2 ^ 8 <
          256 + (2 ^ 248 - 1) * 2 ^ 8 := Nat.add_lt_add_right hlt _
      _ = UInt256.size := by norm_num [UInt256.size, Nat.pow_add]

theorem negativeCanonicalWord {w : UInt256}
    (hneg : EVM.wordModulus - 128 ≤ w.toNat) :
    UInt256.lor (UInt256.lnot ⟨255⟩) (UInt256.land w ⟨255⟩) = w := by
  obtain ⟨hlow, _, _⟩ := negativeLowByte hneg
  apply u256_inj
  rw [signExtendedLow_toNat, hlow]
  have hword : w.toNat < EVM.wordModulus := w.val.isLt
  change EVM.wordModulus - 256 + (w.toNat - (EVM.wordModulus - 256)) = w.toNat
  omega

theorem sarShiftLeft248_low_lt128 {low : UInt256} (hlow : low.toNat < 128) :
    UInt256.sar (UInt256.ofNat 248) (UInt256.shiftLeft low (UInt256.ofNat 248)) = low :=
  sarShiftLeft248_of_lt128 hlow

theorem sarShiftLeft248_negative {w : UInt256} (hneg : EVM.wordModulus - 128 ≤ w.toNat) :
    UInt256.sar (UInt256.ofNat 248) (UInt256.shiftLeft w (UInt256.ofNat 248)) = w := by
  obtain ⟨hlow, hge, hlt⟩ := negativeLowByte hneg
  have hext := negativeCanonicalWord hneg
  have hshl : UInt256.shiftLeft w (UInt256.ofNat 248) =
      UInt256.shiftLeft (UInt256.land w ⟨255⟩) ⟨248⟩ := by
    apply u256_inj
    change (UInt256.shiftLeft w ⟨248⟩).toNat = (UInt256.shiftLeft (UInt256.land w ⟨255⟩) ⟨248⟩).toNat
    unfold UInt256.shiftLeft
    rw [if_neg (by decide), if_neg (by decide)]
    change (w.toNat <<< 248) % UInt256.size =
      ((UInt256.land w ⟨255⟩).toNat <<< 248) % UInt256.size
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, lowByte_toNat]
    have hmod : UInt256.size = 256 * 2 ^ 248 := by
      norm_num [UInt256.size, Nat.pow_add]
    have hdecomp := Nat.div_add_mod w.toNat 256
    calc
      w.toNat * 2 ^ 248 % UInt256.size =
          (256 * (w.toNat / 256) + w.toNat % 256) * 2 ^ 248 % UInt256.size := by
            rw [hdecomp]
      _ = ((w.toNat / 256) * UInt256.size + (w.toNat % 256) * 2 ^ 248) %
          UInt256.size := by rw [hmod]; ring_nf
      _ = (w.toNat % 256) * 2 ^ 248 % UInt256.size := by simp [Nat.add_mod]
  rw [hshl]
  change UInt256.sar ⟨248⟩ (UInt256.shiftLeft (UInt256.land w ⟨255⟩) ⟨248⟩) = w
  rw [sarShiftLeft248_of_ge128 hlt hge]
  apply u256_inj
  have hsum : EVM.wordModulus - 256 + (UInt256.land w ⟨255⟩).toNat = w.toNat := by
    rw [hlow]
    have hword : w.toNat < EVM.wordModulus := w.val.isLt
    omega
  rw [ulit_toNat' _ (by rw [hsum]; exact w.val.isLt), hsum]

theorem int8ReturnEncoding {w : UInt256} (hcanon : i8Canonical w) :
    encodeReturnValue? int8Ty (i8Value w) = some (UInt256.toByteArray w) := by
  rcases hcanon with hpos | hneg
  · change (↑w.val : Nat) < EVM.twoPow 7 at hpos
    refine scalarReturnEncoding (t := .int (.sint ⟨8, by decide⟩)) (w := w) rfl
      (by native_decide) ?_
    have hword : EVM.wordOfInt (Int.ofNat (↑w.val : Nat)) = w := by
      simpa only [UInt256.toNat] using wordOfInt_ofNat_toNat w
    simp [encodeABIValue?, encodeABIWord?, i8Value, hpos]
    exact congrArg EVM.Word.toBytesBE hword
  · have hlt : w.toNat < EVM.wordModulus := w.val.isLt
    have hnpos : ¬w.toNat < EVM.twoPow 7 := by
      have hstart : EVM.twoPow 7 < EVM.wordModulus - EVM.twoPow 7 := by native_decide
      omega
    have hvalueNeg : Int.ofNat w.toNat - Int.ofNat EVM.wordModulus < 0 := by
      have : Int.ofNat w.toNat < Int.ofNat EVM.wordModulus := Int.ofNat_lt.mpr hlt
      omega
    have habs : (Int.ofNat w.toNat - Int.ofNat EVM.wordModulus).natAbs =
        EVM.wordModulus - w.toNat := by
      rw [show Int.ofNat w.toNat - Int.ofNat EVM.wordModulus =
          -((EVM.wordModulus - w.toNat : ℕ) : Int) by simp only [Int.ofNat_eq_natCast]; omega,
        Int.natAbs_neg, Int.natAbs_natCast]
    have hword : EVM.wordOfInt
        (Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) = w := by
      rw [EVM.wordOfInt, if_pos hvalueNeg, habs]
      have hdiffPos : 0 < EVM.wordModulus - w.toNat := by omega
      have hdiffLt : EVM.wordModulus - w.toNat < EVM.wordModulus := by omega
      rw [Nat.mod_eq_of_lt hdiffLt, if_neg (by omega)]
      apply u256_inj
      change (EVM.wordModulus - (EVM.wordModulus - w.toNat)) % EVM.wordModulus = w.toNat
      rw [Nat.sub_sub_self (Nat.le_of_lt hlt), Nat.mod_eq_of_lt hlt]
    have hbound : -(Int.ofNat (EVM.twoPow 7)) ≤
          Int.ofNat w.toNat - Int.ofNat EVM.wordModulus ∧
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus < Int.ofNat (EVM.twoPow 7) := by
      constructor
      · have hpow : EVM.twoPow 7 ≤ EVM.wordModulus := by native_decide
        have hcast : Int.ofNat (EVM.wordModulus - EVM.twoPow 7) ≤
            Int.ofNat w.toNat := Int.ofNat_le.mpr hneg
        change (↑(EVM.wordModulus - EVM.twoPow 7) : Int) ≤ ↑w.toNat at hcast
        rw [Int.ofNat_sub hpow] at hcast
        change -(EVM.twoPow 7 : Int) ≤ (w.toNat : Int) - EVM.wordModulus
        omega
      · exact lt_of_lt_of_le hvalueNeg (Int.natCast_nonneg _)
    refine scalarReturnEncoding (t := .int (.sint ⟨8, by decide⟩)) (w := w) rfl
      (by native_decide) ?_
    change ¬(↑w.val : Nat) < EVM.twoPow 7 at hnpos
    change EVM.wordOfInt
      (Int.ofNat (↑w.val : Nat) - Int.ofNat EVM.wordModulus) = w at hword
    simp only [encodeABIValue?, encodeABIWord?, i8Value, if_neg hnpos]
    simp only [show (8 : ℕ) - 1 = 7 from rfl, show ¬ (8 = 0) from by decide, if_false]
    rw [if_pos (by
      change -(Int.ofNat (EVM.twoPow 7)) ≤ Int.ofNat w.toNat - Int.ofNat EVM.wordModulus ∧
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus < Int.ofNat (EVM.twoPow 7)
      exact hbound), hword]
    rfl

/-! ## `address` -/

theorem addressReturnEncoding {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    encodeReturnValue? (.elem .address) (.address (AccountAddress.ofNat w.toNat)) =
      some (UInt256.toByteArray w) := by
  simpa [solcAddrMask_clean hcanon] using
    solcAddressReturnEncoding (addrTy := .elem .address) rfl w

end FeProofs.NarrowAbi
