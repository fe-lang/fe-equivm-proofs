import FeProofs.Deposit.Dispatch

/-!
# FeDeposit `get_deposit_root()` — EVM trace segments

The runtime trace of `get_deposit_root` (arm entry pc 1821), cut at its `STATICCALL`s:

* prologue (pcs 1821–1840): call-value check, `SLOAD(32)` for the count, and the loop state
  `[size, node, height, count] = [count, 0, 0, count]`;
* odd/even lane (pc 1840, entered with `height < 32`): `size & 1 == 1` writes `branch[height]`
  and `node` to `0xa0`/`0xc0` (pc 1853), otherwise `node` and `zero_hashes[height]` (pc 1897);
  both stop at the `STATICCALL(gas, 2, 0xa0, 0x40, 0xa0, 0x20)` (pcs 1873, 1922);
* after each call (pcs 1874/1923): revert unless it succeeded with at least 32 return bytes, then
  `node := MLOAD(0xa0)`, `size >>= 1`, `height += 1` (pc 1942), and back to pc 1840 while
  `height < 32`, otherwise on to pc 1959 with `[height, node, size, count]`;
* exit (pc 1959): `node` and `u64_chunk(count)` to `0x60`/`0x80`, the final `STATICCALL`
  (pc 2051), the same checks (pcs 2052/2059) and `RETURN` of `MLOAD(0x60)` (pc 2068).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## Trace segments -/

local notation "code" => feDepositBytecode

/-- The stored deposit count (slot 32). -/
abbrev countWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (UInt256.ofNat 32)

theorem rootPrologue {σ σ₀ A I} {g : Sat256} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (rd : RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1821) [sel]
      entryMem aw ByteArray.empty σ k C) :
    ∃ k' C', RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1840)
      [countWord σ I, ⟨0⟩, ⟨0⟩, countWord σ I] entryMem aw ByteArray.empty σ k' C' := by
  rd_run rd to 1840 using [hwv]
  exact ⟨_, _, rd⟩

theorem rootCallvalue {σ σ₀ A I} {g : Sat256} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD code I g (initState σ σ₀ g A I) (UInt256.ofNat 1821) [sel]
      entryMem aw ByteArray.empty σ k C) :
    RDrev code g (initState σ σ₀ g A I) := by
  rd_run rd using [hwv]
  exact rd

section Loop

variable {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
  {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}

/-- Odd lane: `branch[height]` and `node` are written to `0xa0`/`0xc0`, stopping at the call. -/
theorem rootOddPre {size node h count : UInt256}
    (hodd : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 1)
    (rd : RD code ee g s0 (UInt256.ofNat 1840) [size, node, h, count] mem aw rdata σ k C) :
    ∃ gw k' C', RD code ee g s0 (UInt256.ofNat 1873)
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
    (rd : RD code ee g s0 (UInt256.ofNat 1840) [size, node, h, count] mem aw rdata σ k C) :
    ∃ gw k' C', RD code ee g s0 (UInt256.ofNat 1922)
      [gw, UInt256.ofNat 2, UInt256.ofNat 160, UInt256.ofNat 64, UInt256.ofNat 160,
        UInt256.ofNat 32, gw, size, h, count]
      ((UInt256.toByteArray (solcSlotWord σ ee (UInt256.ofNat 33 + h))).write 0
        ((UInt256.toByteArray node).write 0 mem 160 32) 192 32)
      (M (M aw (UInt256.ofNat 160) ⟨32⟩) (UInt256.ofNat 192) ⟨32⟩) rdata σ k' C' := by
  rd_run rd using [heven]
  exact ⟨_, _, _, rd⟩

/-- After an in-loop hash call: revert unless it succeeded with at least 32 return bytes;
    otherwise load the digest, halve `size`, advance `height`, and either continue the loop
    (pc 1840) or leave it (pc 1959). -/
theorem rootLoopPost (pc : UInt256) {z : Bool} {o : ByteArray} {gw size h count : UInt256}
    (hpc : pc = UInt256.ofNat 1874 ∨ pc = UInt256.ofNat 1923)
    (ho : o.size < UInt256.size)
    (rd : RD code ee g s0 pc ((if z then ⟨1⟩ else ⟨0⟩) :: gw :: [size, h, count]) mem aw o σ k C) :
    ((z = false ∨ o.size < 32) → RDrev code g s0) ∧
    (z = true → 32 ≤ o.size →
      ((UInt256.ofNat 1 + h).toNat < 32 → ∃ k' C', RD code ee g s0 (UInt256.ofNat 1840)
        [UInt256.shiftRight size (UInt256.ofNat 1), memLoad (UInt256.ofNat 160) mem,
          UInt256.ofNat 1 + h, count] mem (M aw (UInt256.ofNat 160) ⟨32⟩) o σ k' C') ∧
      (32 ≤ (UInt256.ofNat 1 + h).toNat → ∃ k' C', RD code ee g s0 (UInt256.ofNat 1959)
        [UInt256.ofNat 1 + h, memLoad (UInt256.ofNat 160) mem,
          UInt256.shiftRight size (UInt256.ofNat 1), count] mem (M aw (UInt256.ofNat 160) ⟨32⟩) o σ
          k' C')) := by
  rcases hpc with rfl | rfl <;> refine ⟨fun hbad => ?_, fun hz hlen => ⟨fun hlt => ?_, fun hge => ?_⟩⟩ <;>
    first
    | (cases z
       · rd_run rd; exact rd
       · rd_run rd using [lt32_size_word_ne (hbad.resolve_left (by simp))]; exact rd)
    | (subst hz
       rd_run rd to 1840 using [lt32_size_word hlen ho,
         ult_one (a := UInt256.ofNat 1 + h) (b := UInt256.ofNat 32) hlt]
       exact ⟨_, _, rd⟩)
    | (subst hz
       rd_run rd to 1959 using [lt32_size_word hlen ho,
         ult_zero (a := UInt256.ofNat 1 + h) (b := UInt256.ofNat 32) hge]
       exact ⟨_, _, rd⟩)

/-- After the final (length mix-in) hash call: revert unless it succeeded with at least 32
    return bytes; otherwise return the loaded digest. -/
theorem rootExitPost {z : Bool} {o : ByteArray} {gw : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000) (ho : o.size < UInt256.size)
    (rd : RD code ee g s0 (UInt256.ofNat 2052) ((if z then ⟨1⟩ else ⟨0⟩) :: gw :: R) mem aw o σ k C) :
    ((z = false ∨ o.size < 32) → RDrev code g s0) ∧
    (z = true → 32 ≤ o.size →
      RDret code g s0 σ (memLoad (UInt256.ofNat 96) mem).toByteArray) := by
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
