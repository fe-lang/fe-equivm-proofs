import FeProofs.WETH9.Common
import FeProofs.WETH9.CreationBlocks_001
import FeProofs.WETH9.CreationBlocks_002
import FeProofs.WETH9.CreationBlocks_003
import FeProofs.Common.Memory
import FeProofs.Common.PackedByte
import FeProofs.Common.SolString
import Reasoning.StorageLoops

/-!
# FeWETH9 constructor trace

The initcode stores the free memory pointer, rejects call value, then calls `SolString::store`
(pc 122) twice, for `name` (slot 0, 13 bytes at `0xc0`, returning to pc 56) and `symbol` (slot 1,
4 bytes at the free memory pointer, returning to pc 96), writes `decimals` into the low byte of
slot 2 and returns the runtime with `CODECOPY(0, 445, 1600)`.

`store` reads the old head `S` and decodes its length (`stored_len`, pc 372), panicking with
`0x22` when the length contradicts the short/long flag.  For a short value it then stores
`payload_word | 2 * len` in the slot.  When the old value was long (`old_words > 0`, pc 251) it
hashes the slot at memory `0xa0` and zeroes the old data words `keccak256(slot) + i` for
`i < old_words` (the bottom-tested loop at pc 342).  `strStore` runs the routine for any slot,
payload and old head.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9.Ctor

set_option maxRecDepth 2000000

/-- The initcode as the creation summaries see it (the constructor has no arguments). -/
abbrev ctorCode : ByteArray := feWETH9CreationBytecode ++ ByteArray.empty

/-! ## The clearing loop (pc 342) -/

/-- From `i = a < n`, the loop zeroes words `K + a, …, K + n - 1` and returns to `ret`. -/
theorem clearLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    (τ : AccountMap) (K ret : UInt256) (n : ℕ) (hn : n < UInt256.size) (hperm : ee.perm = true)
    (hret : (D_J feWETH9CreationBytecode 0).contains ret = true) :
    ∀ m a, a + m + 1 = n → ∀ {aw : UInt256} {k C : ℕ},
      RD ctorCode ee g s0 (UInt256.ofNat 342) [UInt256.ofNat a, K, UInt256.ofNat n, ret] mem aw
        rdata (clearDataWordsForwardFrom ee.codeOwner τ K ⟨0⟩ a) k C →
      ∃ aw' k' C', RD ctorCode ee g s0 ret [] mem aw' rdata
        (clearDataWordsForwardFrom ee.codeOwner τ K ⟨0⟩ n) k' C' := by
  intro m
  induction m with
  | zero =>
    intro a ha aw k C h
    obtain rfl : n = a + 1 := by omega
    have h1 : UInt256.ofNat 1 + UInt256.ofNat a = UInt256.ofNat (a + 1) := u256_one_add_ofNat a
    have hc : UInt256.lt (UInt256.ofNat 1 + UInt256.ofNat a) (UInt256.ofNat (a + 1)) =
        UInt256.ofNat 0 := by
      rw [h1]; exact ult_zero (le_refl _)
    rd_step h using [hperm, hc]
    rw [← clearDataWordsForwardFrom_append] at h
    rd_run h using [hret]
    exact ⟨_, _, _, h⟩
  | succ m ih =>
    intro a ha aw k C h
    have h1 : UInt256.ofNat 1 + UInt256.ofNat a = UInt256.ofNat (a + 1) := u256_one_add_ofNat a
    have hc : UInt256.lt (UInt256.ofNat 1 + UInt256.ofNat a) (UInt256.ofNat n) ≠
        UInt256.ofNat 0 := by
      rw [h1, ult_one (by rw [ulit_toNat' (a + 1) (by omega), ulit_toNat' n hn]; omega)]
      decide
    rd_step h using [hperm, hc]
    rw [h1, ← clearDataWordsForwardFrom_append] at h
    exact ih (a + 1) (by omega) h

/-! ## `SolString::store` (pc 122) -/

/-- `store(slot, value)` for a short value of `len` bytes at `ptr + 32`, returning to `ret`: a
    malformed old head panics; otherwise the head is stored and the old data words are zeroed.
    Memory is unchanged for a short old value; a long one leaves its slot at `0xa0`. -/
theorem strStore {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} (slot ptr len ret : UInt256)
    (hperm : ee.perm = true) (hret : (D_J feWETH9CreationBytecode 0).contains ret = true)
    (hlen0 : 0 < len.toNat) (hlen32 : len.toNat < 32) (V : UInt256)
    (hV : strHeadWord (memLoad (UInt256.ofNat 32 + ptr) mem) len = V)
    (h : RD ctorCode ee g s0 (UInt256.ofNat 122) [slot, ptr, len, ret] mem aw rdata σ k C) :
    (strHeadBad (solcSlotWord σ ee slot) → RDrev ctorCode g s0) ∧
    (¬ strHeadBad (solcSlotWord σ ee slot) → ∃ mem' aw' k' C',
      (mem' = mem ∨ mem' = slot.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) ∧
      RD ctorCode ee g s0 ret [] mem' aw' rdata
        (clearDataWordsForwardFrom ee.codeOwner (sstoreAccountMap ee.codeOwner σ slot V)
          (solidityBytesDataBaseSlot slot) ⟨0⟩ (strOldWords (solcSlotWord σ ee slot))) k' C') := by
  subst hV
  rd_step h
  dsimp only [solcSlotWord]
  generalize (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
    (fun ac => ac.storage.getD slot (⟨0⟩ : UInt256))) = S at h ⊢
  -- the new value is short and not empty
  have c154 : UInt256.isZero (UInt256.lt len (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
    rw [ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlen32)]; decide
  have c168 : UInt256.isZero len = UInt256.ofNat 0 :=
    isZero_eq_zero_of_ne fun h0 => by rw [h0] at hlen0; exact absurd hlen0 (by decide)
  rcases land_one_cases S with hf | hf
  · -- short old value: no data words
    have hf' : UInt256.land S (UInt256.ofNat 1) = UInt256.ofNat 0 := hf
    have hL : strHeadLen S = UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ := by
      rw [strHeadLen, ite_eq_left hf]
    have c372 : UInt256.isZero (UInt256.eq (UInt256.ofNat 1)
        (UInt256.land S (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hf']; decide
    have c133 : UInt256.isZero (UInt256.land (UInt256.ofNat 1) S) ≠ UInt256.ofNat 0 := by
      rw [u256_land_comm, hf']; decide
    by_cases hlt : (strHeadLen S).toNat < 32
    · have c402 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight
            (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1)) (UInt256.ofNat 32))) ≠
            UInt256.ofNat 0 := by
        rw [hf', shortLen_eq, ← hL, ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlt)]
        decide
      refine ⟨fun hbad => absurd hbad ?_, fun _ => ?_⟩
      · rw [strHeadBad, hf, ult_one (by exact hlt)]; decide
      rd_run h using [c372, c402, c133, c154, c168, hperm, hret]
      rw [u256_land_comm _ (leadMask len)] at h
      have hw : strOldWords S = 0 := by rw [strOldWords, ite_eq_left hf]
      rw [hw]
      exact ⟨_, _, _, _, Or.inl rfl, h⟩
    · have c402 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight
            (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1)) (UInt256.ofNat 32))) =
            UInt256.ofNat 0 := by
        rw [hf', shortLen_eq, ← hL, ult_zero (by rw [ulit_toNat' 32 (by decide)]; omega)]
        decide
      refine ⟨fun _ => ?_, fun hok => absurd ?_ hok⟩
      · rd_run h using [c372, c402]
        exact h
      · rw [strHeadBad, hf, ult_zero (by exact Nat.le_of_not_lt hlt)]; decide
  · -- long old value
    have hf' : UInt256.land S (UInt256.ofNat 1) = UInt256.ofNat 1 := hf
    have hne : UInt256.land S ⟨1⟩ ≠ ⟨0⟩ := by rw [hf]; decide
    have hL : strHeadLen S = UInt256.div S ⟨2⟩ := by
      rw [strHeadLen, ite_eq_right hne]
    have c372 : UInt256.isZero (UInt256.eq (UInt256.ofNat 1)
        (UInt256.land S (UInt256.ofNat 1))) = UInt256.ofNat 0 := by
      rw [hf']; decide
    have c133 : UInt256.isZero (UInt256.land (UInt256.ofNat 1) S) = UInt256.ofNat 0 := by
      rw [u256_land_comm, hf']; decide
    by_cases hlt : (strHeadLen S).toNat < 32
    · have c402 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight S (UInt256.ofNat 1))
            (UInt256.ofNat 32))) = UInt256.ofNat 0 := by
        rw [hf', longLen_eq, ← hL, ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlt)]
        decide
      refine ⟨fun _ => ?_, fun hok => absurd ?_ hok⟩
      · rd_run h using [c372, c402]
        exact h
      · rw [strHeadBad, hf, ult_one (by exact hlt)]; decide
    · have c402 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight S (UInt256.ofNat 1))
            (UInt256.ofNat 32))) ≠ UInt256.ofNat 0 := by
        rw [hf', longLen_eq, ← hL, ult_zero (by rw [ulit_toNat' 32 (by decide)]; omega)]
        decide
      refine ⟨fun hbad => absurd hbad ?_, fun _ => ?_⟩
      · rw [strHeadBad, hf, ult_zero (by exact Nat.le_of_not_lt hlt)]; decide
      -- at least one old data word, so the loop is entered
      have hw : ((UInt256.div S ⟨2⟩).toNat + 31) / 32 = strOldWords S := by
        rw [strOldWords, ite_eq_right hne, hL]
      have hpos : 0 < strOldWords S := by rw [← hw, ← hL]; omega
      have hwn := lt_trans (strOldWords_lt S) (show 2 ^ 251 < UInt256.size by decide)
      have c251 : UInt256.lt ⟨0⟩ (UInt256.shiftRight (UInt256.ofNat 31 +
          UInt256.shiftRight S (UInt256.ofNat 1)) (UInt256.ofNat 5)) ≠ UInt256.ofNat 0 := by
        rw [longWords_eq, hw, ult_one (by rw [ulit_toNat' _ hwn]; exact hpos)]; decide
      rd_run h to 342 using [c372, c402, c133, c154, c168, c251, hperm]
      rw [u256_land_comm _ (leadMask len), keccakWord_dataSlotWord _ _ 160 (by decide),
        longWords_eq, hw] at h
      obtain ⟨_, _, _, h⟩ := clearLoop _ _ ret _ hwn hperm hret (strOldWords S - 1) 0
        (by omega) h
      exact ⟨_, _, _, _, Or.inr rfl, h⟩

/-! ## The whole initcode under zero call value -/

/-- The bytes of `"Wrapped Ether"` and `"WETH"`, as the Stele constructor writes them. -/
def nameBytes : ByteArray := ⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩
def symbolBytes : ByteArray := ⟨#[87, 69, 84, 72]⟩

abbrev nameMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap := strWriteMap I σ ⟨0⟩ nameBytes

abbrev symbolMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  strWriteMap I (nameMap σ I) ⟨1⟩ symbolBytes

/-- `(sload(2) & ~0xff) | 18`. -/
abbrev decimalsWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.ofNat 18) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) w)

abbrev ctorMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (symbolMap σ I) (UInt256.ofNat 2)
    (decimalsWord (solcSlotWord (symbolMap σ I) I (UInt256.ofNat 2)))

/-- The final `CODECOPY(0, 445, 1600)` reads back as the runtime, whatever memory held. -/
theorem ctorRuntime_read (mem : ByteArray) :
    (ctorCode.write (UInt256.ofNat 445).toNat mem (⟨0⟩ : UInt256).toNat
        (UInt256.ofNat 1600).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 1600).toNat = feWETH9Bytecode := by
  rw [show (UInt256.ofNat 445).toNat = 445 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 1600).toNat = 1600 from rfl,
    write0_read_back_from_gen _ _ 445 1600 (by decide) (by native_decide) (by decide)]
  native_decide

/-- Zero call value: the initcode panics on a malformed `name` head, then on a malformed `symbol`
    head, and otherwise writes both strings and `decimals` and returns the runtime. -/
theorem feWETH9CtorEvm {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = ctorCode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    (strHeadBad (solcSlotWord σ I ⟨0⟩) → RDrev ctorCode g (initState σ σ₀ g A I)) ∧
    (¬ strHeadBad (solcSlotWord σ I ⟨0⟩) →
      (strHeadBad (solcSlotWord (nameMap σ I) I ⟨1⟩) → RDrev ctorCode g (initState σ σ₀ g A I)) ∧
      (¬ strHeadBad (solcSlotWord (nameMap σ I) I ⟨1⟩) →
        RDret ctorCode g (initState σ σ₀ g A I) (ctorMap σ I) feWETH9Bytecode)) := by
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd to 122 using [hwv]
  obtain ⟨hbad0, hok0⟩ := strStore _ _ _ _ hperm (by native_decide) (by decide) (by decide)
    (solidityShortBytesWord nameBytes) (by native_decide) rd
  refine ⟨hbad0, fun hg0 => ?_⟩
  obtain ⟨mem1, aw1, k1, C1, hmem1, rd1⟩ := hok0 hg0
  -- `name`'s old value was short (memory as it was) or long (its slot at `0xa0`)
  rcases hmem1 with rfl | rfl <;>
  · rd_run rd1 to 122
    obtain ⟨hbad1, hok1⟩ := strStore _ _ _ _ hperm (by native_decide) (by decide) (by decide)
      (solidityShortBytesWord symbolBytes) (by native_decide) rd1
    refine ⟨hbad1, fun hg1 => ?_⟩
    obtain ⟨mem2, aw2, k2, C2, _, rd2⟩ := hok1 hg1
    rd_step rd2 using [hperm]
    rw [ctorRuntime_read] at rd2
    exact rd2

/-- Non-zero call value: the initcode reverts first thing. -/
theorem feWETH9CtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = ctorCode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ctorCode g (initState σ σ₀ g A I) := by
  have rd := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd using [isZero_eq_zero_of_ne hwv]
  exact rd

end FeProofs.WETH9.Ctor
