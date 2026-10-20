import FeProofs.Deposit.DepositLayout
import FeProofs.Deposit.DepositBridge
import Reasoning.VyperCalls

/-!
# FeDeposit memory at pc 650

With the accepted lengths 48, 32 and 96, the decoder allocates the pubkey at `0x100`, the
withdrawal credentials at `0x160` and the signature at `0x1a0`, each a length word followed by its
payload, and leaves the free pointer at `0x220`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs.Deposit

/-- A word written at `0x40` reads back from `[0x40, 0x60)`, whatever memory it extends. -/
theorem fpWord_extract (w : UInt256) (mem : ByteArray) :
    (w.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).extract 64 96 = w.toByteArray := by
  have h := toByteArray_write_read_back_of_gap w mem 64
    (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have hs : 64 + 32 ≤ (w.toByteArray.write 0 mem 64 32).size :=
    write_size_reach _ _ (by decide) (by rw [toByteArray_size])
      (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  rw [readWithPadding_eq_extract _ 64 hs] at h
  exact h

/-- The decoder's free-pointer bump reads back at `0x40` when the allocation lies above `0x60`. -/
theorem rMemAt_fp (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) (hfz : f ≤ z)
    (hgap : z < USize.size) (hcd : p.toNat + (32 + L) ≤ ee.calldata.size) (hf : 96 ≤ f) :
    (rMemAt ee mem p F).extract 64 96 =
      (F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray := by
  have hsz := rPreCopy_size ee mem p F hgap
  have hw32 : 32 ≤ (UInt256.toByteArray ⟨0⟩).size := by rw [toByteArray_size]
  have hm1 := write_size_reach
    (F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31)).toByteArray mem
    (srcOff := 0) (dest := (UInt256.ofNat 64).toNat) (len := 32) (by decide) (by rw [toByteArray_size])
    (Nat.lt_of_lt_of_le (by show 64 - mem.size < 2 ^ 32; omega) USize.le_size)
  have hm1' : 96 ≤ ((F + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (rAlloc ee p + UInt256.ofNat 31)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).size := hm1
  rw [rMemAt_eq ee mem p F hF hlen hz,
    write_extract_preserved ee.calldata _ (by omega) hcd (by omega) (by omega) (by omega) (Or.inl (by omega))]
  unfold rPreCopy
  rw [write_extract_below _ _ (by decide) hw32 (by omega) (by omega) hm1' (by omega)]
  exact fpWord_extract _ _

/-- Size of the decoder's memory: at least the cleared last word's end. -/
theorem rMemAt_size (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) (hfz : f ≤ z)
    (hgap : z < USize.size) (hcd : p.toNat + (32 + L) ≤ ee.calldata.size) :
    z + 32 ≤ (rMemAt ee mem p F).size := by
  have hsz := rPreCopy_size ee mem p F hgap
  rw [rMemAt_eq ee mem p F hF hlen hz]
  exact le_trans hsz (write_size_ge _ _ (by omega) hcd (by omega))

/-- The decoder's free pointer after an allocation above `0x60`. -/
theorem rMemAt_load64 (ee : ExecutionEnv) (mem : ByteArray) (p F : UInt256) {f z L : ℕ}
    (hF : F.toNat = f) (hlen : (UInt256.ofNat 32 + rLen ee p).toNat = 32 + L)
    (hz : (F + UInt256.sub (rAlloc ee p) (UInt256.ofNat 32)).toNat = z) (hfz : f ≤ z)
    (hgap : z < USize.size) (hcd : p.toNat + (32 + L) ≤ ee.calldata.size) (hf : 96 ≤ f) :
    memLoad (UInt256.ofNat 64) (rMemAt ee mem p F) =
      F + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rAlloc ee p + UInt256.ofNat 31) := by
  have hs := rMemAt_size ee mem p F hF hlen hz hfz hgap hcd
  refine memLoad_of_read _ 64 _ (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 64 (by omega)]
  exact rMemAt_fp ee mem p F hF hlen hz hfz hgap hcd hf

/-! ## The accepted `deposit` arguments -/

section Concrete

variable {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
  (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)

include hok in
theorem mLen_eq (i : Nat) (hi : i ≤ 2) (L : Nat) (hL : dLen I.calldata i = L) (hLs : L < UInt256.size) :
    rLen I (hPos I i) = UInt256.ofNat L := by
  obtain ⟨_, hg0, _, hg1, _, hg2, _⟩ := hok
  have hg : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact hg0
    · exact hg1
    · exact hg2
  have h := hLen_toNat I i (by unfold UInt256.size; omega) hg
  exact u256_inj (by rw [h, hL, ulit_toNat' L hLs])

include hok in
theorem mCd (i : Nat) (hi : i ≤ 2) (L : Nat) (hL : dLen I.calldata i = L)
    (hb : dBytesOk I.calldata (dWord I.calldata (32 * i))) :
    (hPos I i).toNat + (32 + L) ≤ I.calldata.size ∧
      (hPos I i).toNat = 4 + dWord I.calldata (32 * i) := by
  obtain ⟨_, hg0, _, hg1, _, hg2, _⟩ := hok
  have hg : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact hg0
    · exact hg1
    · exact hg2
  have hp := hPos_toNat I i hg
  rw [hWord_toNat I i (by unfold UInt256.size; omega)] at hp
  obtain ⟨_, h2⟩ := hb
  unfold dLen at hL
  refine ⟨?_, hp⟩
  rw [hp]; omega

theorem mFp0 : rFp ByteArray.empty = UInt256.ofNat 256 := by native_decide

end Concrete

section Layout

variable {I : ExecutionEnv} (hok : hOk I) (hargs : dArgsOk I.calldata)
  (hl0 : dLen I.calldata 0 = 48) (hl1 : dLen I.calldata 1 = 32) (hl2 : dLen I.calldata 2 = 96)

set_option maxHeartbeats 2000000 in
include hok hargs hl0 hl1 hl2 in
/-- The memory at pc 650: the free pointers, the allocations' extent, and the three payloads. -/
theorem hMem3_layout :
    rFp (hMem1 I) = UInt256.ofNat 352 ∧ rFp (hMem2 I) = UInt256.ofNat 416 ∧
    memLoad (UInt256.ofNat 64) (hMem3 I) = UInt256.ofNat 544 ∧ 544 ≤ (hMem3 I).size ∧
    (hMem3 I).extract 288 336 = dPayload I.calldata (dWord I.calldata 0) ∧
    (hMem3 I).extract 384 416 = dPayload I.calldata (dWord I.calldata 32) ∧
    (hMem3 I).extract 448 544 = dPayload I.calldata (dWord I.calldata 64) := by
  obtain ⟨_, hb0, hb1, hb2⟩ := hargs
  have e0 := mLen_eq hok 0 (by decide) 48 hl0 (by decide)
  have e1 := mLen_eq hok 1 (by decide) 32 hl1 (by decide)
  have e2 := mLen_eq hok 2 (by decide) 96 hl2 (by decide)
  obtain ⟨cd0, hp0⟩ := mCd hok 0 (by decide) 48 hl0 hb0
  obtain ⟨cd1, hp1⟩ := mCd hok 1 (by decide) 32 hl1 hb1
  obtain ⟨cd2, hp2⟩ := mCd hok 2 (by decide) 96 hl2 hb2
  have a0 : rAlloc I (hPos I 0) = UInt256.ofNat 96 := by
    show UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rLen I (hPos I 0) + UInt256.ofNat 63) = _
    rw [e0]; decide
  have a1 : rAlloc I (hPos I 1) = UInt256.ofNat 64 := by
    show UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rLen I (hPos I 1) + UInt256.ofNat 63) = _
    rw [e1]; decide
  have a2 : rAlloc I (hPos I 2) = UInt256.ofNat 128 := by
    show UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (rLen I (hPos I 2) + UInt256.ofNat 63) = _
    rw [e2]; decide
  -- layer 0: pubkey at 256
  have hF0 : (rFp ByteArray.empty).toNat = 256 := by rw [mFp0]; rfl
  have hlen0 : (UInt256.ofNat 32 + rLen I (hPos I 0)).toNat = 32 + 48 := by rw [e0]; rfl
  have hz0 : (rFp ByteArray.empty + UInt256.sub (rAlloc I (hPos I 0)) (UInt256.ofNat 32)).toNat = 320 := by
    rw [mFp0, a0]; rfl
  have hload1 : memLoad (UInt256.ofNat 64) (hMem1 I) = UInt256.ofNat 352 := by
    rw [hMem1, rMemAt_load64 I ByteArray.empty (hPos I 0) (rFp ByteArray.empty) hF0 hlen0 hz0
      (by omega) (lt_usize _ (by decide)) cd0 (by omega), mFp0, a0]
    decide
  have hfp1 : rFp (hMem1 I) = UInt256.ofNat 352 := by
    show (if _ then _ else _) = _
    rw [hload1]; decide
  have s1 := rMemAt_size I ByteArray.empty (hPos I 0) (rFp ByteArray.empty) hF0 hlen0 hz0
    (by omega) (lt_usize _ (by decide)) cd0
  -- layer 1: withdrawal credentials at 352
  have hF1 : (rFp (hMem1 I)).toNat = 352 := by rw [hfp1]; rfl
  have hlen1 : (UInt256.ofNat 32 + rLen I (hPos I 1)).toNat = 32 + 32 := by rw [e1]; rfl
  have hz1 : (rFp (hMem1 I) + UInt256.sub (rAlloc I (hPos I 1)) (UInt256.ofNat 32)).toNat = 384 := by
    rw [hfp1, a1]; rfl
  have hload2 : memLoad (UInt256.ofNat 64) (hMem2 I) = UInt256.ofNat 416 := by
    rw [hMem2, rMemAt_load64 I (hMem1 I) (hPos I 1) (rFp (hMem1 I)) hF1 hlen1 hz1
      (by omega) (lt_usize _ (by decide)) cd1 (by omega), hfp1, a1]
    decide
  have hfp2 : rFp (hMem2 I) = UInt256.ofNat 416 := by
    show (if _ then _ else _) = _
    rw [hload2]; decide
  have s2 := rMemAt_size I (hMem1 I) (hPos I 1) (rFp (hMem1 I)) hF1 hlen1 hz1
    (by omega) (lt_usize _ (by decide)) cd1
  -- layer 2: signature at 416
  have hF2 : (rFp (hMem2 I)).toNat = 416 := by rw [hfp2]; rfl
  have hlen2 : (UInt256.ofNat 32 + rLen I (hPos I 2)).toNat = 32 + 96 := by rw [e2]; rfl
  have hz2 : (rFp (hMem2 I) + UInt256.sub (rAlloc I (hPos I 2)) (UInt256.ofNat 32)).toNat = 512 := by
    rw [hfp2, a2]; rfl
  have hload3 : memLoad (UInt256.ofNat 64) (hMem3 I) = UInt256.ofNat 544 := by
    rw [hMem3, rMemAt_load64 I (hMem2 I) (hPos I 2) (rFp (hMem2 I)) hF2 hlen2 hz2
      (by omega) (lt_usize _ (by decide)) cd2 (by omega), hfp2, a2]
    decide
  have s3 := rMemAt_size I (hMem2 I) (hPos I 2) (rFp (hMem2 I)) hF2 hlen2 hz2
    (by omega) (lt_usize _ (by decide)) cd2
  -- payloads
  have hd0 : dWord I.calldata (dWord I.calldata 0) = 48 := hl0
  have hd1 : dWord I.calldata (dWord I.calldata 32) = 32 := hl1
  have hd2 : dWord I.calldata (dWord I.calldata 64) = 96 := hl2
  have pay0 : (hMem1 I).extract 288 336 = dPayload I.calldata (dWord I.calldata 0) := by
    have h := rMemAt_payload I ByteArray.empty (hPos I 0) (rFp ByteArray.empty) hF0 hlen0 hz0
      (by omega) (lt_usize _ (by decide)) cd0
    have hx := dPayload_extract I.calldata (dWord I.calldata 0)
    rw [hd0] at hx
    rw [hp0] at h
    simp only [Nat.mul_zero] at h hx
    rw [show 4 + dWord I.calldata 0 + 32 + 48 = 4 + dWord I.calldata 0 + 32 + 48 from rfl] at h
    exact h.trans hx
  have pay1 : (hMem2 I).extract 384 416 = dPayload I.calldata (dWord I.calldata 32) := by
    have h := rMemAt_payload I (hMem1 I) (hPos I 1) (rFp (hMem1 I)) hF1 hlen1 hz1
      (by omega) (lt_usize _ (by decide)) cd1
    have hx := dPayload_extract I.calldata (dWord I.calldata 32)
    rw [hd1] at hx
    rw [hp1] at h
    exact h.trans hx
  have pay2 : (hMem3 I).extract 448 544 = dPayload I.calldata (dWord I.calldata 64) := by
    have h := rMemAt_payload I (hMem2 I) (hPos I 2) (rFp (hMem2 I)) hF2 hlen2 hz2
      (by omega) (lt_usize _ (by decide)) cd2
    have hx := dPayload_extract I.calldata (dWord I.calldata 64)
    rw [hd2] at hx
    rw [hp2] at h
    exact h.trans hx
  have s1' : 352 ≤ (hMem1 I).size := s1
  have s2' : 416 ≤ (hMem2 I).size := s2
  refine ⟨hfp1, hfp2, hload3, by omega, ?_, ?_, pay2⟩
  · rw [hMem3, rMemAt_below I (hMem2 I) (hPos I 2) (rFp (hMem2 I)) hF2 hlen2 hz2 (by omega)
      (lt_usize _ (by decide)) cd2 (by omega) (by omega) (by omega) (by omega),
      hMem2, rMemAt_below I (hMem1 I) (hPos I 1) (rFp (hMem1 I)) hF1 hlen1 hz1 (by omega)
      (lt_usize _ (by decide)) cd1 (by omega) (by omega) (by omega) (by omega)]
    exact pay0
  · rw [hMem3, rMemAt_below I (hMem2 I) (hPos I 2) (rFp (hMem2 I)) hF2 hlen2 hz2 (by omega)
      (lt_usize _ (by decide)) cd2 (by omega) (by omega) (by omega) (by omega)]
    exact pay1

end Layout

end FeProofs.Deposit
