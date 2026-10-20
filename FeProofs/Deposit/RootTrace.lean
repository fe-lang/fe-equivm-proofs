import FeProofs.Deposit.Dispatch

/-!
# FeDeposit `get_deposit_root()` — EVM trace segments

The runtime trace of `get_deposit_root` (arm entry pc 1853), cut at its `STATICCALL`s:

* prologue (pcs 1853–1866): call-value check, `SLOAD(32)` for the count, and the loop state
  `[size, node, height, count] = [count, 0, 0, count]`;
* loop head (pc 1866): `height < 32` continues (pc 1876), otherwise the loop exits (pc 1991);
* odd/even lane (pc 1876): `size & 1 == 1` writes `branch[height]` and `node` to `0xa0`/`0xc0`
  (pc 1888), otherwise `node` and `zero_hashes[height]` (pc 1932); both stop at the
  `STATICCALL(gas, 2, 0xa0, 0x40, 0xa0, 0x20)` (pcs 1908, 1957);
* after each call (pcs 1909/1958): revert unless it succeeded with at least 32 return bytes, then
  `node := MLOAD(0xa0)`, `size >>= 1`, `height += 1` and jump back to pc 1866;
* exit (pc 1991): `node` and `u64_chunk(count)` to `0xa0`/`0xc0`, the final `STATICCALL` (pc 2084),
  the same checks (pcs 2085/2092) and `RETURN` of `MLOAD(0xa0)` (pc 2101).

The memory facts at the end identify the call payload with the two written words and the loaded
word with the first word of the call's output.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## Memory facts -/

/-- Two consecutive word writes at `0xa0`/`0xc0` read back as their 64-byte concatenation, whatever
    the memory held before. -/
theorem rootPayload (mem : ByteArray) (w1 w2 : UInt256) :
    (((UInt256.toByteArray w2).write 0 ((UInt256.toByteArray w1).write 0 mem 160 32) 192 32)
        ).readWithPadding 160 64 = w1.toByteArray ++ w2.toByteArray := by
  have hgap1 : 160 - mem.size < USize.size := lt_usize _ (by omega)
  have hs1 := toByteArray_write_size_ge_off_add32 w1 mem 160 hgap1
  have hgap2 : 192 - ((UInt256.toByteArray w1).write 0 mem 160 32).size < USize.size :=
    lt_usize _ (by omega)
  have hs2 := toByteArray_write_size_ge_off_add32 w2 _ 192 hgap2
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ 160 32 32 (by decide) (by decide) (by omega),
    toByteArray_write_read_below_of_gap w2 _ 192 160 hs1 (by decide) hgap2,
    toByteArray_write_read_back_of_gap w1 mem 160 hgap1,
    toByteArray_write_read_back_of_gap w2 _ 192 hgap2]

/-! ## Trace segments -/

local notation "code" => feDepositBytecode

/-- The stored deposit count (slot 32). -/
abbrev countWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (UInt256.ofNat 32)

theorem rootPrologue {σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (rd : RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1853) [sel]
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ k C) :
    ∃ k' C', RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1866)
      [countWord σ I, ⟨0⟩, ⟨0⟩, countWord σ I] ByteArray.empty (UInt256.ofNat 0)
      ByteArray.empty σ k' C' := by
  rd_run rd to 1866 using [hwv]
  exact ⟨_, _, rd⟩

theorem rootCallvalue {σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1853) [sel]
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  rd_run rd using [hwv]
  exact rd

section Loop

variable {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
  {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}

theorem rootHeadContinue {size node h count : UInt256} (hh : h.toNat < 32)
    (rd : RD code ee g s0 (UInt256.ofNat 1866) [size, node, h, count] mem aw rdata σ k C) :
    RD code ee g s0 (UInt256.ofNat 1876) [size, node, h, count] mem aw rdata σ (k + 7) (C + 26) := by
  rd_run rd to 1876 using [ult_one (a := h) (b := UInt256.ofNat 32) hh]
  exact rd

theorem rootHeadExit {size node h count : UInt256} (hh : 32 ≤ h.toNat)
    (rd : RD code ee g s0 (UInt256.ofNat 1866) [size, node, h, count] mem aw rdata σ k C) :
    RD code ee g s0 (UInt256.ofNat 1991) [size, node, h, count] mem aw rdata σ (k + 7) (C + 26) := by
  rd_run rd to 1991 using [ult_zero (a := h) (b := UInt256.ofNat 32) hh]
  exact rd

/-- Odd lane: `branch[height]` and `node` are written to `0xa0`/`0xc0`, stopping at the call. -/
theorem rootOddPre {size node h count : UInt256}
    (hodd : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 1)
    (rd : RD code ee g s0 (UInt256.ofNat 1876) [size, node, h, count] mem aw rdata σ k C) :
    ∃ gw k' C', RD code ee g s0 (UInt256.ofNat 1908)
      [gw, UInt256.ofNat 2, UInt256.ofNat 160, UInt256.ofNat 64, UInt256.ofNat 160,
        UInt256.ofNat 32, gw, size, h, count]
      ((UInt256.toByteArray node).write 0
        ((UInt256.toByteArray (solcSlotWord σ ee h)).write 0 mem 160 32) 192 32)
      (M (M aw (UInt256.ofNat 160) ⟨32⟩) (UInt256.ofNat 192) ⟨32⟩) rdata σ k' C' := by
  rd_run rd using [hodd, uInt256_eq_self]
  exact ⟨_, _, _, rd⟩

/-- Even lane: `node` and `zero_hashes[height]` are written to `0xa0`/`0xc0`, stopping at the
    call. -/
theorem rootEvenPre {size node h count : UInt256}
    (heven : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 0)
    (rd : RD code ee g s0 (UInt256.ofNat 1876) [size, node, h, count] mem aw rdata σ k C) :
    ∃ gw k' C', RD code ee g s0 (UInt256.ofNat 1957)
      [gw, UInt256.ofNat 2, UInt256.ofNat 160, UInt256.ofNat 64, UInt256.ofNat 160,
        UInt256.ofNat 32, gw, size, h, count]
      ((UInt256.toByteArray (solcSlotWord σ ee (UInt256.ofNat 33 + h))).write 0
        ((UInt256.toByteArray node).write 0 mem 160 32) 192 32)
      (M (M aw (UInt256.ofNat 160) ⟨32⟩) (UInt256.ofNat 192) ⟨32⟩) rdata σ k' C' := by
  rd_run rd using [heven]
  exact ⟨_, _, _, rd⟩

/-- After an in-loop hash call: revert unless it succeeded with at least 32 return bytes;
    otherwise load the digest and continue at the loop head. -/
theorem rootLoopPost (pc : UInt256) {z : Bool} {o : ByteArray} {gw size h count : UInt256}
    (hpc : pc = UInt256.ofNat 1909 ∨ pc = UInt256.ofNat 1958)
    (ho : o.size < UInt256.size)
    (rd : RD code ee g s0 pc ((if z then ⟨1⟩ else ⟨0⟩) :: gw :: [size, h, count]) mem aw o σ k C) :
    ((z = false ∨ o.size < 32) → RDrev code g s0) ∧
    (z = true → 32 ≤ o.size → ∃ k' C', RD code ee g s0 (UInt256.ofNat 1866)
      [UInt256.shiftRight size (UInt256.ofNat 1), memLoad (UInt256.ofNat 160) mem,
        UInt256.ofNat 1 + h, count] mem (M aw (UInt256.ofNat 160) ⟨32⟩) o σ k' C') := by
  rcases hpc with rfl | rfl <;> refine ⟨fun hbad => ?_, fun hz hlen => ?_⟩ <;>
    first
    | (cases z
       · rd_run rd; exact rd
       · rd_run rd using [lt32_size_word_ne (hbad.resolve_left (by simp))]; exact rd)
    | (subst hz; rd_run rd to 1866 using [lt32_size_word hlen ho]; exact ⟨_, _, rd⟩)

/-- After the final (length mix-in) hash call: revert unless it succeeded with at least 32
    return bytes; otherwise return the loaded digest. -/
theorem rootExitPost {z : Bool} {o : ByteArray} {gw : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000) (ho : o.size < UInt256.size)
    (rd : RD code ee g s0 (UInt256.ofNat 2085) ((if z then ⟨1⟩ else ⟨0⟩) :: gw :: R) mem aw o σ k C) :
    ((z = false ∨ o.size < 32) → RDrev code g s0) ∧
    (z = true → 32 ≤ o.size →
      RDret code g s0 σ (memLoad (UInt256.ofNat 160) mem).toByteArray) := by
  refine ⟨fun hbad => ?_, fun hz hlen => ?_⟩
  · cases z
    · rd_run rd; exact rd
    · rd_run rd using [lt32_size_word_ne (hbad.resolve_left (by simp))]; exact rd
  · subst hz
    rd_run rd using [lt32_size_word hlen ho]
    u256_lits at rd
    rwa [toByteArray_write32_read_back mem _ 0 (Nat.zero_le _)] at rd

end Loop

end FeProofs.Deposit
