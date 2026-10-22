import FeProofs.WETH9.Common
import FeProofs.Common.SolString
import FeProofs.WETH9.Dispatch

/-!
# FeWETH9 strings: `SolString::load` and the `string` return encoder

Both getters, `name()` (pc 137) and `symbol()` (pc 571), push their field's slot and a return
address and jump to the shared `SolString::load` routine at pc 800 (`src/sol_string.fe`):

- `stored_len` (pc 1115) decodes the header word and panics with `Panic(0x22)` when the length
  contradicts the short/long flag (`storedLen_ok`, `storedLen_revert`);
- `ptr::alloc_bytes` (pc 812) checks the allocation, `32 + 32 * ceil(len / 32)` bytes, against
  `2^64 - 1` (`Panic(0x41)`) and bumps the free memory pointer from `0xe0` (`loadHead`); the
  length word goes to `0xe0`;
- a short string's leading bytes (pc 878), or each data word of a long one cut to the bytes left
  (the loop at pc 963, `loadLoop`), are stored after the length word (`loadBody`);
- `DynString::from_abi_tail`'s checks (pc 975) pass and the routine returns the pointer and the
  size (`loadTail`).

The arm then jumps to the `string` return encoder at pc 1236 (`encodeReturn`), which returns the
offset word `0x20` followed by the length word and the padded bytes.  `loadString_ok` and
`loadString_revert` package the routine for `StringGetter.lean`.

Memory below the string (`HdrMem`) holds the free memory pointer at `0x40` and the length word at
`0xe0`; the loop appends to it.  Every bound comes from the allocation check: the routine only
gets past pc 812 when the allocation is below `2^64` bytes.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9.Strings

set_option maxRecDepth 2000000

local notation "code" => feWETH9Bytecode

/-! ## Word arithmetic of the routine -/

/-- `(len + 31) >> 5`: the data words. -/
theorem strWords_eq {L : ℕ} (hL : L < 2 ^ 64) :
    UInt256.shiftRight (UInt256.ofNat L + UInt256.ofNat 31) (UInt256.ofNat 5) =
      UInt256.ofNat ((L + 31) / 32) := by
  apply u256_inj
  rw [shiftRight_toNat_of_lt _ 5 (by decide), uadd_toNat, lit_toNat (n := L) (by omega),
    lit_toNat (n := 31) (by omega), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega),
    lit_toNat (by omega)]
  rfl

/-- `32 + (words << 5)`: the allocation size. -/
theorem strSize_eq {W : ℕ} (hW : W < 2 ^ 64) :
    UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat W) (UInt256.ofNat 5) =
      UInt256.ofNat (32 + 32 * W) := by
  apply u256_inj
  rw [uadd_toNat, shl5_toNat hW, lit_toNat (n := 32) (by omega),
    Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega), lit_toNat (by omega)]

/-- The free memory pointer after the allocation at `0xe0`. -/
theorem allocFmp_eq {W : ℕ} (hW : W < 2 ^ 64) :
    UInt256.ofNat 224 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
        (UInt256.ofNat (32 + 32 * W) + UInt256.ofNat 31) = UInt256.ofNat (256 + 32 * W) := by
  have hmask : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat (2 ^ 256 - 2 ^ 5) := by
    apply u256_inj
    rw [lnot_toNat_gen, lit_toNat (n := 31) (by omega), lit_toNat (by omega)]
    norm_num
  have hland : (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 5))
      (UInt256.ofNat (63 + 32 * W))).toNat = 32 + 32 * W := by
    rw [u256_land_high_mask_toNat _ 5 (by decide), lit_toNat (by omega)]
    omega
  apply u256_inj
  rw [hmask, lit_add_eq (by omega), show 32 + 32 * W + 31 = 63 + 32 * W by omega, uadd_toNat,
    hland, lit_toNat (n := 224) (by omega), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega),
    lit_toNat (by omega)]
  omega

theorem memLoad64_empty : memLoad (UInt256.ofNat 64) ByteArray.empty = ⟨0⟩ := rfl

/-- The address the loop stores data word `i` at: `0xe0 + 32 + 32 * i`. -/
theorem loopAddr_toNat {i : ℕ} (hi : i < 2 ^ 64) :
    (UInt256.ofNat 224 +
      (UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5))).toNat =
        256 + 32 * i := by
  rw [shl5_eq hi, lit_add_eq (by omega), lit_add_eq (by omega), lit_toNat (by omega)]
  omega

/-- The bytes left at data word `i`: `len - (i << 5)`. -/
theorem loopRem_eq {L i : ℕ} (hi : 32 * i ≤ L) (hL : L < 2 ^ 64) :
    UInt256.sub (UInt256.ofNat L) (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)) =
      UInt256.ofNat (L - 32 * i) := by
  apply u256_inj
  rw [usub_toNat (by rw [shl5_toNat (by omega), lit_toNat (by omega)]; exact hi),
    shl5_toNat (by omega), lit_toNat (n := L) (by omega), lit_toNat (by omega)]

/-- `from_abi_tail`'s word count `((len - 1) >> 5) + 1`, for `len > 0`. -/
theorem tailWords_eq {L : ℕ} (h0 : 0 < L) (hL : L < 2 ^ 64) :
    UInt256.shiftRight (UInt256.sub (UInt256.ofNat L) (UInt256.ofNat 1)) (UInt256.ofNat 5) +
      UInt256.ofNat 1 = UInt256.ofNat ((L + 31) / 32) := by
  have hq : UInt256.shiftRight (UInt256.sub (UInt256.ofNat L) (UInt256.ofNat 1)) (UInt256.ofNat 5) =
      UInt256.ofNat ((L - 1) / 32) := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt _ 5 (by decide),
      usub_toNat (by rw [lit_toNat (n := 1) (by omega), lit_toNat (n := L) (by omega)]; omega),
      lit_toNat (n := 1) (by omega), lit_toNat (n := L) (by omega), lit_toNat (by omega)]
    rfl
  rw [hq, lit_add_eq (by omega), show (L - 1) / 32 + 1 = (L + 31) / 32 by omega]

/-! ## Memory below the string -/

/-- The area below a loaded string: the free memory pointer at `0x40` and the string's length at
`0xe0`, where its bytes start. -/
structure HdrMem (X : ByteArray) (fmp len : UInt256) : Prop where
  size : X.size = 256
  fmp : X.extract 64 96 = fmp.toByteArray
  len : X.extract 224 256 = len.toByteArray

/-- `SolString::load`'s allocation: the free memory pointer, then the length word. -/
theorem hdrMem_alloc (fmp len : UInt256) :
    HdrMem (len.toByteArray.write 0 (fmp.toByteArray.write 0 ByteArray.empty 64 32) 224 32)
      fmp len := by
  have h1 := toByteArray_write_eq fmp ByteArray.empty 64 (by simp) (lt_usize _ (by simp))
  have hs1 : (fmp.toByteArray.write 0 ByteArray.empty 64 32).size = 96 := by
    rw [h1]; simp [ByteArray_zeroes_size]
  have h2 := toByteArray_write_eq len (fmp.toByteArray.write 0 ByteArray.empty 64 32) 224
    (by omega) (lt_usize _ (by omega))
  rw [hs1] at h2
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; simp [ByteArray_zeroes_size, hs1]
  · rw [h2, ByteArray.append_assoc, extract_append_left _ _ _ _ (by omega), h1,
      extract_append_right_window _ _ _ _ (by simp [ByteArray_zeroes_size])]
    simpa [ByteArray_zeroes_size] using toByteArray_extract_all fmp
  · rw [h2, extract_append_right_window _ _ _ _ (by simp [ByteArray_zeroes_size, hs1])]
    simpa [ByteArray_zeroes_size, hs1] using toByteArray_extract_all len

/-- `KECCAK256`'s scratch word at `0xa0` leaves the area intact. -/
theorem HdrMem.write160 {X : ByteArray} {fmp len : UInt256} (h : HdrMem X fmp len)
    (w : UInt256) : HdrMem (w.toByteArray.write 0 X 160 32) fmp len := by
  have hs := h.size
  refine ⟨?_, ?_, ?_⟩
  · rw [copyWindow_size _ _ _ _ _ (by decide) (by rw [toByteArray_size]) (by omega), hs]
    rfl
  · rw [wordWrite_extract _ _ (by omega) (by omega) (Or.inl (by omega)) (by omega), h.fmp]
  · rw [wordWrite_extract _ _ (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩) (by omega),
      h.len]

/-- `KECCAK256(0xa0, 32)` over the slot: the string's first data slot. -/
theorem HdrMem.memLoad64 {X : ByteArray} {fmp len : UInt256} (h : HdrMem X fmp len)
    (D : ByteArray) : memLoad (UInt256.ofNat 64) (X ++ D) = fmp := by
  have hs : (X ++ D).size = 256 + D.size := by rw [ByteArray.size_append, h.size]
  refine memLoad_of_extract (by decide) (by omega) ?_
  rw [extract_append_left _ _ _ _ (by have := h.size; omega)]
  exact h.fmp

theorem HdrMem.memLoad224 {X : ByteArray} {fmp len : UInt256} (h : HdrMem X fmp len)
    (D : ByteArray) : memLoad (UInt256.ofNat 224) (X ++ D) = len := by
  have hs : (X ++ D).size = 256 + D.size := by rw [ByteArray.size_append, h.size]
  refine memLoad_of_extract (by decide) (by omega) ?_
  rw [extract_append_left _ _ _ _ (by have := h.size; omega)]
  exact h.len

/-- The loaded string in memory: its length word, then the bytes appended after the area. -/
theorem HdrMem.extract {X : ByteArray} {fmp len : UInt256} (h : HdrMem X fmp len)
    (D : ByteArray) : (X ++ D).extract 224 (256 + D.size) = len.toByteArray ++ D := by
  rw [extract_append_span _ _ _ _ (by rw [h.size]; omega) (by rw [h.size]; omega), h.size, h.len,
    show 256 + D.size - 256 = D.size by omega, byteArray_extract_self]

/-- The encoder's `RETURN` data: it zeroes a buffer at the free memory pointer (the end of
memory; `CALLDATACOPY` from `CALLDATASIZE`), stores the offset word `0x20`, copies the `n` bytes
at `0xe0` after it, and returns the buffer. -/
theorem encoderOutput (cd M : ByteArray) {n : ℕ} (hM : M.size = 224 + n) (hn : 0 < n)
    (hn64 : 32 + n < 2 ^ 64) :
    (((UInt256.ofNat 32).toByteArray.write 0 (cd.write cd.size M M.size (32 + n)) M.size 32).write
        224 ((UInt256.ofNat 32).toByteArray.write 0 (cd.write cd.size M M.size (32 + n)) M.size 32)
        (M.size + 32) n).readWithPadding M.size (32 + n) =
      (UInt256.ofNat 32).toByteArray ++ M.extract 224 (224 + n) := by
  rw [write_past_end _ _ (le_refl _) (by omega), wordWrite_end _ _ rfl]
  have hB : (M ++ (UInt256.ofNat 32).toByteArray).size = M.size + 32 := by
    rw [ByteArray.size_append, toByteArray_size]
  rw [← hB, write_at_end_eq_from _ _ 224 n (by omega) (by rw [hB]; omega),
    extract_append_left _ _ _ _ (by omega), ByteArray.append_assoc,
    readWithPadding_eq_extract' _ _ _ (by omega) hn64
      (by rw [ByteArray.size_append, ByteArray.size_append, toByteArray_size,
            ByteArray.size_extract]
          omega),
    extract_append_right_window _ _ _ _ (le_refl _), Nat.sub_self,
    show M.size + (32 + n) - M.size =
      ((UInt256.ofNat 32).toByteArray ++ M.extract 224 (224 + n)).size by
        rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract]; omega,
    byteArray_extract_self]

/-! ## The routine -/

theorem RD.appendEmpty {ee : ExecutionEnv} {g : Sat256} {s0 : State} {pc : UInt256}
    {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : ℕ} (h : RD code ee g s0 pc stk mem aw rdata σ k C) :
    RD code ee g s0 pc stk (mem ++ ByteArray.empty) aw rdata σ k C := by
  rwa [ByteArray.append_empty]

section
variable {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
  {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {head : UInt256} {R : List UInt256}

/-- `stored_len`'s check at pc 1145 (`long == (len < 32)` panics), for a header word whose flag
and length are `f` and `l`. -/
abbrev lenCheck (f l : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.eq (UInt256.eq (UInt256.ofNat 1) f) (UInt256.lt l (UInt256.ofNat 32)))

/-- `stored_len(head)` on a well-formed header returns its decoded length to pc 812. -/
theorem storedLen_ok {L : ℕ} (hdec : solidityDecodeBytesLengthHeader head = .ok L)
    (hR : R.length ≤ 1000)
    (rd : RD code ee g s0 (UInt256.ofNat 1115) (head :: UInt256.ofNat 812 :: head :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD code ee g s0 (UInt256.ofNat 812) (UInt256.ofNat L :: head :: R)
      mem aw rdata σ k' C' := by
  have hh := u256_toNat_lt head
  rcases decodeHeader_cases head with ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · rw [hok] at hdec; cases hdec
    have hc : lenCheck (UInt256.land head (UInt256.ofNat 1))
        (UInt256.shiftRight head (UInt256.ofNat 1)) ≠ UInt256.ofNat 0 := by
      rw [lenCheck, headFlag_odd ho, headLen_long, lit_ge32 hge (by omega)]; decide
    rd_run rd to 812 using [headFlag_odd ho, hc]
    rw [headLen_long] at rd
    exact ⟨_, _, rd⟩
  · rw [hok] at hdec; cases hdec
    have hc : lenCheck (UInt256.land head (UInt256.ofNat 1))
        (UInt256.shiftRight (UInt256.land (UInt256.ofNat 255) head) (UInt256.ofNat 1)) ≠
          UInt256.ofNat 0 := by
      rw [lenCheck, headFlag_even he, headLen_short, lit_lt32 hlt]; decide
    rd_run rd to 812 using [headFlag_even he, hc]
    rw [headLen_short] at rd
    exact ⟨_, _, rd⟩
  · rw [hrev] at hdec; cases hdec

/-- `stored_len(head)` on a malformed header panics. -/
theorem storedLen_revert (hdec : solidityDecodeBytesLengthHeader head = .revert)
    (hR : R.length ≤ 1000)
    (rd : RD code ee g s0 (UInt256.ofNat 1115) (head :: UInt256.ofNat 812 :: head :: R)
      mem aw rdata σ k C) :
    RDrev code g s0 := by
  have hh := u256_toNat_lt head
  rcases decodeHeader_cases head with ⟨_, _, hok⟩ | ⟨_, _, hok⟩ | ⟨hbad, _⟩
  · rw [hok] at hdec; cases hdec
  · rw [hok] at hdec; cases hdec
  -- the panic payload goes to the free memory pointer, or to `0xe0` below it
  have hfp := em
    (UInt256.gt (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 223) = UInt256.ofNat 0)
  rcases hbad with ⟨ho, hlt⟩ | ⟨he, hge⟩
  · have hc : lenCheck (UInt256.land head (UInt256.ofNat 1))
        (UInt256.shiftRight head (UInt256.ofNat 1)) = UInt256.ofNat 0 := by
      rw [lenCheck, headFlag_odd ho, headLen_long, lit_lt32 hlt]; decide
    rcases hfp with hfp | hfp <;> (rd_run rd using [headFlag_odd ho, hc, hfp]; exact rd)
  · have hc : lenCheck (UInt256.land head (UInt256.ofNat 1))
        (UInt256.shiftRight (UInt256.land (UInt256.ofNat 255) head) (UInt256.ofNat 1)) =
          UInt256.ofNat 0 := by
      rw [lenCheck, headFlag_even he, headLen_short, lit_ge32 hge (by omega)]; decide
    rcases hfp with hfp | hfp <;> (rd_run rd using [headFlag_even he, hc, hfp]; exact rd)

/-- `SolString::load` up to the allocation (pc 800 to 853): the header's length decoded and the
allocation size checked. -/
theorem loadHead {slot ret : UInt256} {L : ℕ}
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ ee slot) = .ok L)
    (hfit : 64 + 32 * ((L + 31) / 32) < 2 ^ 64) (hR : R.length ≤ 990)
    (rd : RD code ee g s0 (UInt256.ofNat 800) (slot :: ret :: R) ByteArray.empty aw rdata σ k C) :
    ∃ aw' k' C', RD code ee g s0 (UInt256.ofNat 853)
      (UInt256.ofNat 224 :: UInt256.ofNat (32 + 32 * ((L + 31) / 32)) ::
        UInt256.ofNat ((L + 31) / 32) :: UInt256.ofNat L :: solcSlotWord σ ee slot :: slot ::
        ret :: R)
      ByteArray.empty aw' rdata σ k' C' := by
  have hL : L < 2 ^ 64 := by omega
  rd_step rd
  obtain ⟨k1, C1, rd⟩ := storedLen_ok hdec (by simp; omega) rd
  have hc : UInt256.gt (UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.shiftRight
      (UInt256.ofNat L + UInt256.ofNat 31) (UInt256.ofNat 5)) (UInt256.ofNat 5))
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.ofNat 192)) = UInt256.ofNat 0 := by
    rw [strWords_eq hL, strSize_eq (by omega)]
    refine ugt_zero ?_
    rw [lit_toNat (by omega)]
    change _ ≤ 2 ^ 64 - 1
    omega
  have hm : UInt256.gt (memLoad (UInt256.ofNat 64) ByteArray.empty) (UInt256.ofNat 223) =
      UInt256.ofNat 0 := by rw [memLoad64_empty]; decide
  rd_run rd to 853 using [hc, hm]
  rw [strWords_eq hL, strSize_eq (by omega)] at rd
  exact ⟨_, _, _, rd⟩

/-- The bytes the copy loop has stored after `n` iterations: the data words from `base`, each cut
to the string's remaining length. -/
abbrev loopBytes (σ : AccountMap) (ee : ExecutionEnv) (base : UInt256) (L n : ℕ) : ByteArray :=
  wordsBytes (fun j => leadWord (solcSlotWord σ ee (base + UInt256.ofNat j)) (L - 32 * j)) n

/-- The long-string copy loop (pc 963), from iteration `i` to its exit at pc 975: each data word
is cut to the bytes left and appended to memory. -/
theorem loadLoop {X : ByteArray} {L : ℕ} {base S : UInt256} (hX : X.size = 256)
    (hL : L < 2 ^ 64) (hR : R.length ≤ 1000) :
    ∀ n i (aw : UInt256) (k C : ℕ), i + n = (L + 31) / 32 →
      RD code ee g s0 (UInt256.ofNat 963) (UInt256.ofNat i :: base :: S ::
          UInt256.ofNat ((L + 31) / 32) :: UInt256.ofNat L :: UInt256.ofNat 224 :: R)
        (X ++ loopBytes σ ee base L i) aw rdata σ k C →
      ∃ aw' k' C', RD code ee g s0 (UInt256.ofNat 975)
        (S :: UInt256.ofNat L :: UInt256.ofNat 224 :: R)
        (X ++ loopBytes σ ee base L ((L + 31) / 32)) aw' rdata σ k' C' := by
  intro n
  induction n with
  | zero =>
    intro i aw k C hi rd
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat ((L + 31) / 32)) = UInt256.ofNat 0 := by
      rw [ult_zero (by rw [lit_toNat (by omega), lit_toNat (by omega)]; omega)]; rfl
    rw [show i = (L + 31) / 32 by omega] at rd hc
    rd_run rd to 975 using [hc]
    exact ⟨_, _, _, rd⟩
  | succ n ih =>
    intro i aw k C hi rd
    have hW : (L + 31) / 32 < 2 ^ 64 := by omega
    have hiL : 32 * i < L := by omega
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat ((L + 31) / 32)) ≠ UInt256.ofNat 0 := by
      rw [ult_one (by rw [lit_toNat (by omega), lit_toNat (by omega)]; omega)]; decide
    have hrem := loopRem_eq (i := i) (by omega) hL
    have hsz : (X ++ loopBytes σ ee base L i).size = 256 + 32 * i := by
      rw [ByteArray.size_append, hX, wordsBytes_size]
    rd_step rd using [hc]
    by_cases hlt : L - 32 * i < 32
    · -- the last word: keep its leading bytes
      have hc2 : UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat L)
          (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5))) (UInt256.ofNat 32)) =
          UInt256.ofNat 0 := by
        rw [hrem, lit_lt32 hlt]; decide
      rd_run rd to 963 using [hc2]
      rw [hrem, loopAddr_toNat (by omega), ← hsz, wordWrite_end _ _ rfl, ByteArray.append_assoc,
        lit_add_eq (by omega), Nat.add_comm 1 i] at rd
      have hmem : loopBytes σ ee base L i ++ (UInt256.land (solcSlotWord σ ee (base +
          UInt256.ofNat i)) (leadMask (UInt256.ofNat (L - 32 * i)))).toByteArray =
          loopBytes σ ee base L (i + 1) := by
        simp only [loopBytes, wordsBytes, leadWord, if_pos hlt]
      rw [hmem] at rd
      exact ih (i + 1) _ _ _ (by omega) rd
    · -- a full word
      have hc2 : UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat L)
          (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5))) (UInt256.ofNat 32)) ≠
          UInt256.ofNat 0 := by
        rw [hrem, lit_ge32 (by omega) (by omega)]; decide
      rd_run rd to 963 using [hc2]
      rw [loopAddr_toNat (by omega), ← hsz, wordWrite_end _ _ rfl, ByteArray.append_assoc,
        lit_add_eq (by omega), Nat.add_comm 1 i] at rd
      have hmem : loopBytes σ ee base L i ++
          (solcSlotWord σ ee (base + UInt256.ofNat i)).toByteArray =
          loopBytes σ ee base L (i + 1) := by
        simp only [loopBytes, wordsBytes, leadWord, if_neg hlt]
      rw [hmem] at rd
      exact ih (i + 1) _ _ _ (by omega) rd

/-- `SolString::load` from the allocation to pc 975: the length word at `0xe0`, then the
string's bytes padded to words. -/
theorem loadBody {slot ret : UInt256} {L : ℕ}
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ ee slot) = .ok L)
    (hfit : 64 + 32 * ((L + 31) / 32) < 2 ^ 64) (hR : R.length ≤ 990)
    (rd : RD code ee g s0 (UInt256.ofNat 853)
      (UInt256.ofNat 224 :: UInt256.ofNat (32 + 32 * ((L + 31) / 32)) ::
        UInt256.ofNat ((L + 31) / 32) :: UInt256.ofNat L :: solcSlotWord σ ee slot :: slot ::
        ret :: R)
      ByteArray.empty aw rdata σ k C) :
    ∃ X aw' k' C', HdrMem X (UInt256.ofNat (256 + 32 * ((L + 31) / 32))) (UInt256.ofNat L) ∧
      RD code ee g s0 (UInt256.ofNat 975)
        (UInt256.ofNat (32 + 32 * ((L + 31) / 32)) :: UInt256.ofNat L :: UInt256.ofNat 224 ::
          ret :: R)
        (X ++ (strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L))) aw' rdata σ k' C' := by
  have hL : L < 2 ^ 64 := by omega
  have hh := u256_toNat_lt (solcSlotWord σ ee slot)
  have hX := hdrMem_alloc (UInt256.ofNat (256 + 32 * ((L + 31) / 32))) (UInt256.ofNat L)
  rcases decodeHeader_cases (solcSlotWord σ ee slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · -- long: copy the data words
    rw [hok] at hdec
    have hLe : (solcSlotWord σ ee slot).toNat / 2 = L := by injection hdec
    have hc : UInt256.land (solcSlotWord σ ee slot) (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
      rw [headFlag_odd ho]; decide
    rd_run rd to 963 using [hc]
    u256_lits at rd
    rw [allocFmp_eq (by omega), keccakWord_dataSlot _ _ 160 (by decide)] at rd
    obtain ⟨aw', k', C', rd⟩ := loadLoop (base := solidityBytesDataBaseSlot slot)
      (hX.write160 slot).size hL (by simp; omega) ((L + 31) / 32) 0 _ _ _ (by omega)
      (RD.appendEmpty rd)
    have hD : loopBytes σ ee (solidityBytesDataBaseSlot slot) L ((L + 31) / 32) =
        strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L) := by
      rw [loopBytes, leadWords_eq _ L (by omega), strBytes, if_neg (by omega)]
      rfl
    rw [hD] at rd
    exact ⟨_, _, _, _, hX.write160 slot, rd⟩
  · rw [hok] at hdec
    have hLe : (solcSlotWord σ ee slot).toNat % 256 / 2 = L := by injection hdec
    have hc : UInt256.land (solcSlotWord σ ee slot) (UInt256.ofNat 1) = UInt256.ofNat 0 :=
      headFlag_even he
    by_cases h0 : L = 0
    · -- empty: nothing to copy
      subst h0
      have hc0 : UInt256.isZero (UInt256.ofNat 0) ≠ UInt256.ofNat 0 := by decide
      rd_run rd to 975 using [hc, hc0]
      u256_lits at rd
      rw [allocFmp_eq (by omega)] at rd
      have hD : strBytes σ ee slot 0 ++ zpad (32 * ((0 + 31) / 32) - 0) = ByteArray.empty := by
        apply byteArray_eq_empty_of_size_eq_zero
        rw [strBytes, if_pos (by omega)]
        simp
      rw [hD]
      exact ⟨_, _, _, _, hX, RD.appendEmpty rd⟩
    · -- short: the header's leading bytes
      have hc0 : UInt256.isZero (UInt256.ofNat L) = UInt256.ofNat 0 :=
        isZero_eq_zero_of_ne (lit_ne_zero h0 (by omega))
      have hc1 : UInt256.isZero (UInt256.lt (UInt256.ofNat L) (UInt256.ofNat 32)) =
          UInt256.ofNat 0 := by
        rw [lit_lt32 (by omega)]; decide
      rd_run rd to 975 using [hc, hc0, hc1]
      u256_lits at rd
      rw [allocFmp_eq (by omega), wordWrite_end _ _ hX.size.symm] at rd
      have hD : (UInt256.land (solcSlotWord σ ee slot) (leadMask (UInt256.ofNat L))).toByteArray =
          strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L) := by
        have hw : leadWord (solcSlotWord σ ee slot) L =
            UInt256.land (solcSlotWord σ ee slot) (leadMask (UInt256.ofNat L)) :=
          if_pos (by omega)
        rw [← hw, leadWord_toByteArray, strBytes, if_pos (by omega), Nat.min_eq_left (by omega),
          show 32 * ((L + 31) / 32) - L = 32 - L by omega]
      rw [hD] at rd
      exact ⟨_, _, _, _, hX, rd⟩
  · rw [hrev] at hdec; cases hdec

/-- `DynString::from_abi_tail`'s checks (pc 975 to the return): the allocation size matches the
length, and the length word reads back; then `SolString::load` returns `(data, size)` to `ret`. -/
theorem loadTail {X D : ByteArray} {fmp ret : UInt256} {L : ℕ}
    (hX : HdrMem X fmp (UInt256.ofNat L)) (hL : L < 2 ^ 64)
    (hret : (D_J code 0).contains ret = true) (hR : R.length ≤ 1000)
    (rd : RD code ee g s0 (UInt256.ofNat 975)
      (UInt256.ofNat (32 + 32 * ((L + 31) / 32)) :: UInt256.ofNat L :: UInt256.ofNat 224 ::
        ret :: R)
      (X ++ D) aw rdata σ k C) :
    ∃ aw' k' C', RD code ee g s0 ret
      (UInt256.ofNat 224 :: UInt256.ofNat (32 + 32 * ((L + 31) / 32)) :: R)
      (X ++ D) aw' rdata σ k' C' := by
  have hcLen : UInt256.isZero (UInt256.eq (UInt256.ofNat L)
      (memLoad (UInt256.ofNat 224) (X ++ D))) = UInt256.ofNat 0 := by
    rw [hX.memLoad224, u256_eq_refl]; decide
  by_cases h0 : L = 0
  · subst h0
    have hc0 : UInt256.ofNat 0 = UInt256.ofNat 0 := rfl
    rd_run rd using [hc0, hcLen, hret]
    exact ⟨_, _, _, rd⟩
  · have hW : (L + 31) / 32 < 2 ^ 64 := by omega
    have hcAdd : UInt256.lt (UInt256.shiftRight (UInt256.sub (UInt256.ofNat L) (UInt256.ofNat 1))
        (UInt256.ofNat 5) + UInt256.ofNat 1)
        (UInt256.shiftRight (UInt256.sub (UInt256.ofNat L) (UInt256.ofNat 1)) (UInt256.ofNat 5)) =
          UInt256.ofNat 0 := by
      rw [tailWords_eq (by omega) hL]
      refine (ult_zero ?_).trans rfl
      rw [lit_toNat (by omega), shiftRight_toNat_of_lt _ 5 (by decide),
        usub_toNat (by rw [lit_toNat (n := 1) (by omega), lit_toNat (n := L) (by omega)]; omega),
        lit_toNat (n := 1) (by omega), lit_toNat (n := L) (by omega)]
      omega
    rd_step rd using [lit_ne_zero h0 (by omega)]
    rd_step rd using [hcAdd]
    rw [tailWords_eq (by omega) hL] at rd
    have hcMul : UInt256.eq (UInt256.ofNat ((L + 31) / 32)) (UInt256.shiftRight (UInt256.shiftLeft
        (UInt256.ofNat ((L + 31) / 32)) (UInt256.ofNat 5)) (UInt256.ofNat 5)) ≠
          UInt256.ofNat 0 := by
      rw [shl5_eq hW, shr5_eq hW, u256_eq_refl]; decide
    rd_step rd using [hcMul]
    rw [shl5_eq hW] at rd
    have hS := lit_add_eq (a := 32) (b := 32 * ((L + 31) / 32)) (by omega)
    have hcAdd2 : UInt256.lt (UInt256.ofNat 32 + UInt256.ofNat (32 * ((L + 31) / 32)))
        (UInt256.ofNat 32) = UInt256.ofNat 0 := by
      rw [hS, ult_zero (by rw [lit_toNat (by omega), lit_toNat (by omega)]; omega)]; rfl
    rd_step rd using [hcAdd2]
    rw [hS] at rd
    have hcSize : UInt256.isZero (UInt256.eq (UInt256.ofNat (32 + 32 * ((L + 31) / 32)))
        (UInt256.ofNat (32 + 32 * ((L + 31) / 32)))) = UInt256.ofNat 0 := by
      rw [u256_eq_refl]; decide
    rd_run rd using [hcSize, hcLen, hret]
    exact ⟨_, _, _, rd⟩

/-- `SolString::load` (pc 800 to `ret`) on a well-formed header with a fitting length: memory
holds the length word and the padded bytes at `0xe0`, and the free memory pointer past them. -/
theorem loadString_ok {slot ret : UInt256} {L : ℕ}
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ ee slot) = .ok L)
    (hfit : 64 + 32 * ((L + 31) / 32) < 2 ^ 64) (hret : (D_J code 0).contains ret = true)
    (hR : R.length ≤ 990)
    (rd : RD code ee g s0 (UInt256.ofNat 800) (slot :: ret :: R) ByteArray.empty aw rdata σ k C) :
    ∃ M aw' k' C', M.size = 256 + 32 * ((L + 31) / 32) ∧
      memLoad (UInt256.ofNat 64) M = UInt256.ofNat (256 + 32 * ((L + 31) / 32)) ∧
      M.extract 224 (256 + 32 * ((L + 31) / 32)) = (UInt256.ofNat L).toByteArray ++
        (strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L)) ∧
      RD code ee g s0 ret (UInt256.ofNat 224 :: UInt256.ofNat (32 + 32 * ((L + 31) / 32)) :: R)
        M aw' rdata σ k' C' := by
  obtain ⟨_, _, _, rd⟩ := loadHead hdec hfit hR rd
  obtain ⟨X, _, _, _, hX, rd⟩ := loadBody hdec hfit hR rd
  obtain ⟨_, _, _, rd⟩ := loadTail hX (by omega) hret (by omega) rd
  have hD : (strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L)).size =
      32 * ((L + 31) / 32) := by
    rw [ByteArray.size_append, strBytes_size, zpad_size]; omega
  have hext := hX.extract (strBytes σ ee slot L ++ zpad (32 * ((L + 31) / 32) - L))
  rw [hD] at hext
  exact ⟨_, _, _, _, by rw [ByteArray.size_append, hX.size, hD], hX.memLoad64 _, hext, rd⟩

/-- `SolString::load` (pc 800) on a malformed header panics. -/
theorem loadString_revert {slot ret : UInt256}
    (hdec : solidityDecodeBytesLengthHeader (solcSlotWord σ ee slot) = .revert)
    (hR : R.length ≤ 990)
    (rd : RD code ee g s0 (UInt256.ofNat 800) (slot :: ret :: R) mem aw rdata σ k C) :
    RDrev code g s0 := by
  rd_step rd
  exact storedLen_revert hdec (by simp; omega) rd

/-- The `string` return encoder (pc 1236): the `n` bytes at `0xe0` (a length word and the padded
bytes) are returned after the offset word `0x20`. -/
theorem encodeReturn {M : ByteArray} {n : ℕ} (hM : M.size = 224 + n)
    (h64 : memLoad (UInt256.ofNat 64) M = UInt256.ofNat (224 + n)) (hn : 0 < n)
    (hfit : 32 + n < 2 ^ 64) (hcd : ee.calldata.size < 2 ^ 256) (hR : R.length ≤ 1000)
    (rd : RD code ee g s0 (UInt256.ofNat 1236) (UInt256.ofNat 224 :: UInt256.ofNat n :: R)
      M aw rdata σ k C) :
    RDret code g s0 σ ((UInt256.ofNat 32).toByteArray ++ M.extract 224 (224 + n)) := by
  have hS := lit_add_eq (a := 32) (b := n) (by omega)
  have hcAdd : UInt256.isZero (UInt256.lt (UInt256.ofNat 32 + UInt256.ofNat n)
      (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hS, ult_zero (by rw [lit_toNat (by omega), lit_toNat (by omega)]; omega)]; decide
  rd_step rd using [hcAdd]
  rw [hS] at rd
  have hcAlloc : UInt256.gt (UInt256.ofNat (32 + n)) (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
      (UInt256.ofNat 192)) = UInt256.ofNat 0 := by
    refine (ugt_zero ?_).trans rfl
    rw [lit_toNat (by omega)]
    change _ ≤ 2 ^ 64 - 1
    omega
  have hcFmp : UInt256.gt (memLoad (UInt256.ofNat 64) M) (UInt256.ofNat 223) ≠
      UInt256.ofNat 0 := by
    rw [h64, ugt_one (by rw [lit_toNat (by omega), lit_toNat (by omega)]; omega)]; decide
  rd_run rd using [hcAlloc, hcFmp]
  rw [h64, lit_add_eq (a := 224 + n) (b := 32) (by omega), lit_toNat (n := 224 + n) (by omega),
    lit_toNat (n := 224 + n + 32) (by omega), lit_toNat (n := 32 + n) (by omega),
    lit_toNat (n := n) (by omega), lit_toNat (n := ee.calldata.size) hcd,
    show (UInt256.ofNat 224).toNat = 224 from rfl, ← hM] at rd
  rwa [encoderOutput ee.calldata M hM hn hfit] at rd

end

end FeProofs.WETH9.Strings
