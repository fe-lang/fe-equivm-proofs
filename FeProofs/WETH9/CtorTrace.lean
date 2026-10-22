import FeProofs.WETH9.Common
import FeProofs.WETH9.CreationBlocks_001
import FeProofs.WETH9.CreationBlocks_002
import FeProofs.WETH9.CreationBlocks_003
import FeProofs.Common.Memory
import FeProofs.Common.PackedByte
import Reasoning.StorageLoops

/-!
# FeWETH9 constructor trace

The initcode rejects call value, then calls `SolString::store` (pc 133) twice, for `name` (slot 0,
13 bytes, returning to pc 67) and `symbol` (slot 1, 4 bytes, returning to pc 107), writes `decimals`
into the low byte of slot 2 and returns the runtime with `CODECOPY(0, 470, 1590)`.

`store` reads the old head `S` and decodes its length (`stored_len`, pc 388), panicking with
`0x22` when the length contradicts the short/long flag.  For a short value it then stores
`payload_word | 2 * len` in the slot, hashes the slot at memory `0xa0` and zeroes the old data words
`keccak256(slot) + i` for `i < old_words` (pc 288), where `old_words` is zero for a short old value.
`strStore` runs the routine for any slot, payload and old head.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9.Ctor

set_option maxRecDepth 2000000

/-- The initcode as the creation summaries see it (the constructor has no arguments). -/
abbrev ctorCode : ByteArray := feWETH9CreationBytecode ++ ByteArray.empty

/-! ## String heads -/

/-- The length a string head encodes, as Stele and Fe's `stored_len` decode it. -/
def strHeadLen (S : UInt256) : UInt256 :=
  if UInt256.land S ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ else UInt256.div S ⟨2⟩

/-- A head whose length contradicts its short/long flag: both sides revert. -/
def strHeadBad (S : UInt256) : Prop :=
  UInt256.sub (UInt256.land S ⟨1⟩) (UInt256.lt (strHeadLen S) ⟨32⟩) = ⟨0⟩

/-- The data words a string with head `S` occupies: none for a short one. -/
def strOldWords (S : UInt256) : ℕ :=
  if UInt256.land S ⟨1⟩ = ⟨0⟩ then 0 else ((strHeadLen S).toNat + 31) / 32

/-- The mask of `leading_bytes(_, len)`: the first `len` bytes of a word. -/
abbrev leadMask (len : UInt256) : UInt256 :=
  UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len (UInt256.ofNat 3)))

/-- The head `store` writes for a short value of `len` bytes whose first word is `w`. -/
def strHeadWord (w len : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land (leadMask len) (UInt256.land w (leadMask len)))
    (UInt256.shiftLeft len (UInt256.ofNat 1))

theorem land_one_cases (S : UInt256) : UInt256.land S ⟨1⟩ = ⟨0⟩ ∨ UInt256.land S ⟨1⟩ = ⟨1⟩ := by
  have h := uInt256_land_one_toNat S
  rcases Nat.mod_two_eq_zero_or_one S.toNat with h2 | h2
  · exact Or.inl (u256_inj (by rw [h, h2]; rfl))
  · exact Or.inr (u256_inj (by rw [h, h2]; rfl))

/-- A short head's length: `(S & 0xff) >> 1`. -/
theorem shortLen_eq (S : UInt256) :
    UInt256.shiftRight (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1) =
      UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), uland_toNat, uland_toNat, udiv_toNat,
    show (UInt256.ofNat 255).toNat = 255 from rfl, show (⟨2⟩ : UInt256).toNat = 2 from rfl,
    show (⟨127⟩ : UInt256).toNat = 127 from rfl, Nat.land_comm,
    show (255 : ℕ) = 2 ^ 8 - 1 from rfl, show (127 : ℕ) = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A long head's length: `S >> 1`. -/
theorem longLen_eq (S : UInt256) :
    UInt256.shiftRight S (UInt256.ofNat 1) = UInt256.div S ⟨2⟩ := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 1 (by decide), udiv_toNat]
  rfl

theorem strHeadLen_long_lt (S : UInt256) : (UInt256.div S ⟨2⟩).toNat < 2 ^ 255 := by
  rw [udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from rfl]
  have hS : S.toNat < 2 ^ 256 := S.val.isLt
  omega

/-- A long head's data word count: `(31 + (S >> 1)) >> 5`. -/
theorem longWords_eq (S : UInt256) :
    UInt256.shiftRight (UInt256.ofNat 31 + UInt256.shiftRight S (UInt256.ofNat 1))
        (UInt256.ofNat 5) =
      UInt256.ofNat (((UInt256.div S ⟨2⟩).toNat + 31) / 32) := by
  have hlt := strHeadLen_long_lt S
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 5 (by decide), uadd_toNat, longLen_eq,
    show (UInt256.ofNat 31).toNat = 31 from rfl,
    Nat.mod_eq_of_lt (show 31 + (UInt256.div S ⟨2⟩).toNat < UInt256.size by
      change _ < 2 ^ 256; omega),
    ulit_toNat' _ (show ((UInt256.div S ⟨2⟩).toNat + 31) / 32 < UInt256.size by
      change _ < 2 ^ 256; omega)]
  omega

theorem strOldWords_lt (S : UInt256) : strOldWords S < 2 ^ 251 := by
  unfold strOldWords strHeadLen
  split
  · decide
  · have := strHeadLen_long_lt S
    omega

/-- `KECCAK256(0xa0, 32)` over the slot stored at `0xa0`: the slot's string data base. -/
theorem keccakWord_dataSlot (slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 160) (UInt256.ofNat 32)
        (slot.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) =
      solidityBytesDataBaseSlot slot := by
  unfold keccakWord
  rw [show (UInt256.ofNat 160).toNat = 160 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    toByteArray_write_read_back_of_gap slot mem 160 (small_gap mem 160 (by decide))]
  exact keccakSlot_eq _

/-! ## The clearing loop (pc 288) -/

/-- From `i = a`, the loop zeroes words `K + a, …, K + n - 1` and returns to `ret`. -/
theorem clearLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    (τ : AccountMap) (K ret : UInt256) (n : ℕ) (hn : n < UInt256.size) (hperm : ee.perm = true)
    (hret : (D_J feWETH9CreationBytecode 0).contains ret = true) :
    ∀ m a, a + m = n → ∀ {aw : UInt256} {k C : ℕ},
      RD ctorCode ee g s0 (UInt256.ofNat 288) [UInt256.ofNat a, K, UInt256.ofNat n, ret] mem aw
        rdata (clearDataWordsForwardFrom ee.codeOwner τ K ⟨0⟩ a) k C →
      ∃ aw' k' C', RD ctorCode ee g s0 ret [] mem aw' rdata
        (clearDataWordsForwardFrom ee.codeOwner τ K ⟨0⟩ n) k' C' := by
  intro m
  induction m with
  | zero =>
    intro a ha aw k C h
    obtain rfl : a = n := by omega
    have hc : UInt256.lt (UInt256.ofNat a) (UInt256.ofNat a) = UInt256.ofNat 0 :=
      ult_zero (le_refl _)
    rd_run h using [hc, hret]
    exact ⟨_, _, _, h⟩
  | succ m ih =>
    intro a ha aw k C h
    have hc : UInt256.lt (UInt256.ofNat a) (UInt256.ofNat n) ≠ UInt256.ofNat 0 := by
      rw [ult_one (by rw [ulit_toNat' a (by omega), ulit_toNat' n hn]; omega)]
      decide
    rd_step h using [hc]
    rd_step h using [hperm]
    rw [show UInt256.ofNat 1 + UInt256.ofNat a = UInt256.ofNat (a + 1) from u256_one_add_ofNat a,
      ← clearDataWordsForwardFrom_append] at h
    exact ih (a + 1) (by omega) h

/-! ## `SolString::store` (pc 133) -/

/-- `store(slot, value)` for a short value of `len` bytes at `ptr + 32`, returning to `ret`: a
    malformed old head panics; otherwise the head is stored and the old data words are zeroed. -/
theorem strStore {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} (slot ptr len ret : UInt256)
    (hperm : ee.perm = true) (hret : (D_J feWETH9CreationBytecode 0).contains ret = true)
    (hlen0 : 0 < len.toNat) (hlen32 : len.toNat < 32) (V : UInt256)
    (hV : strHeadWord (memLoad (⟨0⟩ + (UInt256.ofNat 32 + ptr)) mem) len = V)
    (h : RD ctorCode ee g s0 (UInt256.ofNat 133) [slot, ptr, len, ret] mem aw rdata σ k C) :
    (strHeadBad (solcSlotWord σ ee slot) → RDrev ctorCode g s0) ∧
    (¬ strHeadBad (solcSlotWord σ ee slot) → ∃ aw' k' C', RD ctorCode ee g s0 ret []
      (slot.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) aw' rdata
      (clearDataWordsForwardFrom ee.codeOwner (sstoreAccountMap ee.codeOwner σ slot V)
        (solidityBytesDataBaseSlot slot) ⟨0⟩ (strOldWords (solcSlotWord σ ee slot))) k' C') := by
  subst hV
  rd_step h
  dsimp only [solcSlotWord]
  generalize (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
    (fun ac => ac.storage.getD slot (⟨0⟩ : UInt256))) = S at h ⊢
  -- the new value is short
  have c165 : UInt256.isZero (UInt256.lt len (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
    rw [ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlen32)]; decide
  have c314 : UInt256.lt ⟨0⟩ len ≠ UInt256.ofNat 0 := by
    rw [ult_one (by exact hlen0)]; decide
  have hsub : UInt256.sub len ⟨0⟩ = len :=
    u256_inj (by rw [usub_toNat (Nat.zero_le _)]; rfl)
  have c328 : UInt256.isZero (UInt256.lt (UInt256.sub len ⟨0⟩) (UInt256.ofNat 32)) =
      UInt256.ofNat 0 := by
    rw [hsub]; exact c165
  rcases land_one_cases S with hf | hf
  · -- short old value
    have hf' : UInt256.land S (UInt256.ofNat 1) = UInt256.ofNat 0 := hf
    have hL : strHeadLen S = UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩ := by
      rw [strHeadLen, if_pos hf]
    have c388 : UInt256.isZero (UInt256.eq (UInt256.ofNat 1)
        (UInt256.land S (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hf']; decide
    have c144 : UInt256.isZero (UInt256.land (UInt256.ofNat 1) S) ≠ UInt256.ofNat 0 := by
      rw [u256_land_comm, hf']; decide
    by_cases hlt : (strHeadLen S).toNat < 32
    · have c418 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight
            (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1)) (UInt256.ofNat 32))) ≠
            UInt256.ofNat 0 := by
        rw [hf', shortLen_eq, ← hL, ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlt)]
        decide
      refine ⟨fun hbad => absurd hbad ?_, fun _ => ?_⟩
      · rw [strHeadBad, hf, ult_one (by exact hlt)]; decide
      rd_run h to 288 using [c388, c418, c144, c165, c314, c328, hperm]
      rw [hsub, keccakWord_dataSlot] at h
      have hw : strOldWords S = 0 := by rw [strOldWords, if_pos hf]
      rw [hw]
      exact clearLoop _ _ ret 0 (by decide) hperm hret 0 0 rfl h
    · have c418 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight
            (UInt256.land (UInt256.ofNat 255) S) (UInt256.ofNat 1)) (UInt256.ofNat 32))) =
            UInt256.ofNat 0 := by
        rw [hf', shortLen_eq, ← hL, ult_zero (by rw [ulit_toNat' 32 (by decide)]; omega)]
        decide
      refine ⟨fun _ => ?_, fun hok => absurd ?_ hok⟩
      · rd_run h using [c388, c418]
        exact h
      · rw [strHeadBad, hf, ult_zero (by exact Nat.le_of_not_lt hlt)]; decide
  · -- long old value
    have hf' : UInt256.land S (UInt256.ofNat 1) = UInt256.ofNat 1 := hf
    have hne : UInt256.land S ⟨1⟩ ≠ ⟨0⟩ := by rw [hf]; decide
    have hL : strHeadLen S = UInt256.div S ⟨2⟩ := by
      rw [strHeadLen, if_neg hne]
    have c388 : UInt256.isZero (UInt256.eq (UInt256.ofNat 1)
        (UInt256.land S (UInt256.ofNat 1))) = UInt256.ofNat 0 := by
      rw [hf']; decide
    have c144 : UInt256.isZero (UInt256.land (UInt256.ofNat 1) S) = UInt256.ofNat 0 := by
      rw [u256_land_comm, hf']; decide
    by_cases hlt : (strHeadLen S).toNat < 32
    · have c418 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight S (UInt256.ofNat 1))
            (UInt256.ofNat 32))) = UInt256.ofNat 0 := by
        rw [hf', longLen_eq, ← hL, ult_one (by rw [ulit_toNat' 32 (by decide)]; exact hlt)]
        decide
      refine ⟨fun _ => ?_, fun hok => absurd ?_ hok⟩
      · rd_run h using [c388, c418]
        exact h
      · rw [strHeadBad, hf, ult_one (by exact hlt)]; decide
    · have c418 : UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1)
          (UInt256.land S (UInt256.ofNat 1))) (UInt256.lt (UInt256.shiftRight S (UInt256.ofNat 1))
            (UInt256.ofNat 32))) ≠ UInt256.ofNat 0 := by
        rw [hf', longLen_eq, ← hL, ult_zero (by rw [ulit_toNat' 32 (by decide)]; omega)]
        decide
      refine ⟨fun hbad => absurd hbad ?_, fun _ => ?_⟩
      · rw [strHeadBad, hf, ult_zero (by exact Nat.le_of_not_lt hlt)]; decide
      rd_run h to 288 using [c388, c418, c144, c165, c314, c328, hperm]
      rw [hsub, keccakWord_dataSlot, longWords_eq] at h
      have hw : ((UInt256.div S ⟨2⟩).toNat + 31) / 32 = strOldWords S := by
        rw [strOldWords, if_neg hne, hL]
      rw [hw] at h
      exact clearLoop _ _ ret _ (lt_trans (strOldWords_lt S) (by decide)) hperm hret _ 0
        (Nat.zero_add _) h

/-! ## The whole initcode under zero call value -/

/-- The bytes of `"Wrapped Ether"` and `"WETH"`, as the Stele constructor writes them. -/
def nameBytes : ByteArray := ⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩
def symbolBytes : ByteArray := ⟨#[87, 69, 84, 72]⟩

/-- The account map after `store` writes the short string `bytes` at `slot`: the head first, then
    the old data words zeroed. -/
abbrev strWriteMap (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256) (bytes : ByteArray) :
    AccountMap :=
  clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ slot (solidityShortBytesWord bytes))
    (solidityBytesDataBaseSlot slot) ⟨0⟩ (strOldWords (solcSlotWord σ I slot))

abbrev nameMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap := strWriteMap I σ ⟨0⟩ nameBytes

abbrev symbolMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  strWriteMap I (nameMap σ I) ⟨1⟩ symbolBytes

/-- `(sload(2) & ~0xff) | 18`. -/
abbrev decimalsWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.ofNat 18) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) w)

abbrev ctorMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (symbolMap σ I) (UInt256.ofNat 2)
    (decimalsWord (solcSlotWord (symbolMap σ I) I (UInt256.ofNat 2)))

/-- The final `CODECOPY(0, 470, 1590)` reads back as the runtime, whatever memory held. -/
theorem ctorRuntime_read (mem : ByteArray) :
    (ctorCode.write (UInt256.ofNat 470).toNat mem (⟨0⟩ : UInt256).toNat
        (UInt256.ofNat 1590).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 1590).toNat = feWETH9Bytecode := by
  rw [show (UInt256.ofNat 470).toNat = 470 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 1590).toNat = 1590 from rfl,
    write0_read_back_from_gen _ _ 470 1590 (by decide) (by native_decide) (by decide)]
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
  rd_run rd to 133 using [hwv]
  obtain ⟨hbad0, hok0⟩ := strStore _ _ _ _ hperm (by native_decide) (by decide) (by decide)
    (solidityShortBytesWord nameBytes) (by native_decide) rd
  refine ⟨hbad0, fun hg0 => ?_⟩
  obtain ⟨aw1, k1, C1, rd1⟩ := hok0 hg0
  rd_run rd1 to 133
  obtain ⟨hbad1, hok1⟩ := strStore _ _ _ _ hperm (by native_decide) (by decide) (by decide)
    (solidityShortBytesWord symbolBytes) (by native_decide) rd1
  refine ⟨hbad1, fun hg1 => ?_⟩
  obtain ⟨aw2, k2, C2, rd2⟩ := hok1 hg1
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
