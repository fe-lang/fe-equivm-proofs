import FeProofs.Deposit.Dispatch

/-!
# FeDeposit `deposit()` — the event segment (pc 1026 → 1592)

After the deposit-data root has been recomputed (its word at the top-of-stack pointer), the
bytecode compares it with `CALLDATALOAD(0x64)` (pc 1026; mismatch reverts at pc 1036), builds the
`amount`/`index` eight-byte values and the ABI encoding of `DepositEvent` (pcs 1175–1491), emits
it with `LOG1` (pc 1534), and checks `count < 2^32 - 1` (pc 1548; otherwise revert via 1549).
The encoding's allocation guards (pcs 1331, 1355, 1383, 1408, 1435, 1464, 1490) only depend on the
three payload lengths on the stack and pass for any lengths below `2^60`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

local notation "code" => feDepositBytecode

/-! ## Allocation-guard arithmetic -/

/-- The event encoding's total size: `0xa0` head plus the three padded payloads. -/
abbrev eventTotal (r0 r1 r4 : UInt256) : UInt256 :=
  UInt256.ofNat 64 + (r0 + (UInt256.ofNat 64 + (r1 + (UInt256.ofNat 160 + r4))))

section Arith

variable {r0 r1 r4 : UInt256} (h0 : r0.toNat < 4294967296) (h1 : r1.toNat < 4294967296)
  (h4 : r4.toNat < 4294967296)
include h0 h1 h4

theorem eventTotal_toNat :
    (eventTotal r0 r1 r4).toNat = 288 + r0.toNat + r1.toNat + r4.toNat := by
  have hsz : 1000000000000 < UInt256.size := by decide
  have l64 : (UInt256.ofNat 64).toNat = 64 := ulit_toNat' 64 (by omega)
  have l160 : (UInt256.ofNat 160).toNat = 160 := ulit_toNat' 160 (by omega)
  simp only [eventTotal]
  simp only [uadd_toNat, l64, l160]
  rw [Nat.mod_eq_of_lt (a := 160 + r4.toNat) (by omega),
    Nat.mod_eq_of_lt (a := r1.toNat + (160 + r4.toNat)) (by omega),
    Nat.mod_eq_of_lt (a := 64 + (r1.toNat + (160 + r4.toNat))) (by omega),
    Nat.mod_eq_of_lt (a := r0.toNat + (64 + (r1.toNat + (160 + r4.toNat)))) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem eventSub1 : ((eventTotal r0 r1 r4).sub (UInt256.ofNat 160)).toNat =
    128 + r0.toNat + r1.toNat + r4.toNat := by
  have hsz : 1000000000000 < UInt256.size := by decide
  rw [usub_toNat (by rw [eventTotal_toNat h0 h1 h4, ulit_toNat' 160 (by omega)]; omega),
    eventTotal_toNat h0 h1 h4, ulit_toNat' 160 (by omega)]
  omega

theorem eventSub2 : (((eventTotal r0 r1 r4).sub (UInt256.ofNat 160)).sub r4).toNat =
    128 + r0.toNat + r1.toNat := by
  rw [usub_toNat (by rw [eventSub1 h0 h1 h4]; omega), eventSub1 h0 h1 h4]; omega

theorem eventSub3 : ((((eventTotal r0 r1 r4).sub (UInt256.ofNat 160)).sub r4).sub r1).toNat =
    128 + r0.toNat := by
  rw [usub_toNat (by rw [eventSub2 h0 h1 h4]; omega), eventSub2 h0 h1 h4]; omega

theorem eventSub4 : (((((eventTotal r0 r1 r4).sub (UInt256.ofNat 160)).sub r4).sub r1).sub
    (UInt256.ofNat 64)).toNat = 64 + r0.toNat := by
  have hsz : 1000000000000 < UInt256.size := by decide
  rw [usub_toNat (by rw [eventSub3 h0 h1 h4, ulit_toNat' 64 (by omega)]; omega),
    eventSub3 h0 h1 h4, ulit_toNat' 64 (by omega)]; omega

theorem eventSub5 : ((((((eventTotal r0 r1 r4).sub (UInt256.ofNat 160)).sub r4).sub r1).sub
    (UInt256.ofNat 64)).sub r0).toNat = 64 := by
  rw [usub_toNat (by rw [eventSub4 h0 h1 h4]; omega), eventSub4 h0 h1 h4]; omega

end Arith

theorem eventMax64 :
    (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.ofNat 192)).toNat = 18446744073709551615 := by
  native_decide

section Trace

variable {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
  {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}

/-- The stored deposit count (slot 32), as the bytecode reads it. -/
abbrev eventCount (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  solcSlotWord σ ee (UInt256.ofNat 32)

/-- The supplied `deposit_data_root` word, `CALLDATALOAD(0x64)`. -/
abbrev eventRoot (ee : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)

/-- **The event segment, EVM side** (pc 1026 → 1592): a root mismatch reverts; with a matching
    root the event is encoded and logged (halting in static mode), and the count check either
    reverts or reaches pc 1592 with `[node, count, …]`. -/
theorem depositEventTrace {p a r0 r1 r2 r3 r4 r5 : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (h0 : r0.toNat < 4294967296) (h1 : r1.toNat < 4294967296) (h4 : r4.toNat < 4294967296)
    (rd : RD code ee g s0 (UInt256.ofNat 1026) (p :: a :: r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: R)
      mem aw rdata σ k C) :
    (memLoad p mem ≠ eventRoot ee → RDrev code g s0) ∧
    (memLoad p mem = eventRoot ee → ee.perm = false → RDstatic code g s0) ∧
    (memLoad p mem = eventRoot ee → ee.perm = true →
      4294967295 ≤ (eventCount σ ee).toNat → RDrev code g s0) ∧
    (memLoad p mem = eventRoot ee → ee.perm = true → (eventCount σ ee).toNat < 4294967295 →
      ∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
        RD code ee g s0 (UInt256.ofNat 1592) (memLoad p mem :: eventCount σ ee :: r5 :: R)
          mem' aw' rdata σ k' C') := by
  have hsz : 1000000000000 < UInt256.size := by decide
  refine ⟨fun hne => ?_, ?_⟩
  · rd_run rd using [uInt256_eq_zero_of_ne (fun h => hne (uInt256_eq_one_eq h))]
    exact rd
  -- the matching-root path up to pc 1491
  have pre : memLoad p mem = eventRoot ee → ∃ mem9 aw9 k9 C9 x0 x2 x3 x4 x5 x6 x7 x8,
      RD code ee g s0 (UInt256.ofNat 1491)
        (x0 :: eventCount σ ee :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: r5 :: R)
        mem9 aw9 rdata σ k9 C9 ∧ x2 = memLoad p mem := by
    intro heq
    rd_run rd to 1491 using [(by rw [heq, uInt256_eq_self]; decide),
      (by rw [ugt_zero (show (eventTotal r0 r1 r4).toNat ≤ _ by
        rw [eventTotal_toNat h0 h1 h4, eventMax64]; omega)]; decide),
      (by rw [ugt_zero (a := UInt256.ofNat 160) (b := eventTotal r0 r1 r4)
        (by rw [eventTotal_toNat h0 h1 h4, ulit_toNat' 160 (by omega)]; omega)]; decide),
      ugt_zero (by rw [eventSub1 h0 h1 h4]; omega), ugt_zero (by rw [eventSub2 h0 h1 h4]; omega),
      ugt_zero (by rw [eventSub3 h0 h1 h4, ulit_toNat' 64 (by omega)]; omega),
      ugt_zero (by rw [eventSub4 h0 h1 h4]; omega),
      ugt_zero (by rw [eventSub5 h0 h1 h4, ulit_toNat' 64 (by omega)])]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rd, rfl⟩
  refine ⟨fun heq hpf => ?_, fun heq hperm hbig => ?_, fun heq hperm hlt => ?_⟩
  · obtain ⟨mem9, aw9, k9, C9, x0, x2, x3, x4, x5, x6, x7, x8, rd9, -⟩ := pre heq
    rd_step rd9
    exact rd9
  · obtain ⟨mem9, aw9, k9, C9, x0, x2, x3, x4, x5, x6, x7, x8, rd9, -⟩ := pre heq
    rd_run rd9 using [hperm, ult_zero (by rw [ulit_toNat' 4294967295 (by omega)]; exact hbig)]
    exact rd9
  · obtain ⟨mem9, aw9, k9, C9, x0, x2, x3, x4, x5, x6, x7, x8, rd9, hx2⟩ := pre heq
    subst hx2
    rd_run rd9 to 1592 using [hperm,
      (by rw [ult_one (by rw [ulit_toNat' 4294967295 (by omega)]; exact hlt)]; decide)]
    exact ⟨_, _, _, _, rd9⟩

end Trace

end FeProofs.Deposit
