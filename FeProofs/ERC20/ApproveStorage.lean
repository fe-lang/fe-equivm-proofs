import FeProofs.ERC20.Common

/-!
# FeERC20 `allowance` slot facts

The generated Solidity layout puts `allowance[owner][spender]` at
`keccak256(spender ‖ keccak256(owner ‖ 1))`.  Fe hashes the same preimages in scratch memory at
`0x00..0x40`: owner then slot 1, then spender then the inner hash.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The generated Solidity layout of the contract's storage. -/
def approveLayout : StorageLayout := storageBackend.locate?

theorem approveConfig_storageBackend : config.storageBackend = solidityStorageBackend approveLayout :=
  rfl

/-- Solidity's mapping slot `keccak256(key ‖ base)`. -/
def approveMapSlot (key base : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ base.toByteArray))

theorem approveAllowanceLoc (o s : KeyValue) :
    approveLayout { base := "allowance", steps := [.mindex o, .mindex s] } =
      some (.leaf (uint256Loc (approveMapSlot (keyValueToWord s)
        (approveMapSlot (keyValueToWord o) (UInt256.ofNat 1))))) :=
  rfl

theorem approveGap (mem : ByteArray) (off : Nat) (h : off < 2 ^ 32) : off - mem.size < USize.size :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h USize.le_size)

/-- Two words written at `0x00` and `0x20` read back as the 64-byte preimage `a ‖ b`. -/
theorem approvePair_read (mem : ByteArray) (a b : UInt256) :
    (b.toByteArray.write 0 (a.toByteArray.write 0 mem 0 32) 32 32).readWithPadding 0 64 =
      a.toByteArray ++ b.toByteArray := by
  have h0 := toByteArray_write_size_ge_off_add32 a mem 0 (approveGap mem 0 (by decide))
  have h1 := toByteArray_write_size_ge_off_add32 b (a.toByteArray.write 0 mem 0 32) 32
    (approveGap _ 32 (by decide))
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ 0 32 32 (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega),
    toByteArray_write_read_below_of_gap b _ 32 0 (by omega) (by omega)
      (approveGap _ 32 (by decide)),
    toByteArray_write_read_back_of_gap a mem 0 (approveGap mem 0 (by decide))]
  try rw [Nat.zero_add]
  rw [toByteArray_write_read_back_of_gap b _ 32 (approveGap _ 32 (by decide))]

/-- `KECCAK256(0, 64)` over the two scratch words is the mapping slot of `a` at base `b`. -/
theorem approvePair_keccak (mem : ByteArray) (a b : UInt256) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
        (b.toByteArray.write 0 (a.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = approveMapSlot a b := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (UInt256.ofNat 64).toNat = 64 from rfl, approvePair_read]
  exact mappingSlot_single a b

theorem approveShr160_toNat (w : UInt256) :
    (UInt256.shiftRight w ⟨160⟩).toNat = w.toNat / EVM.twoPow 160 := by
  unfold UInt256.shiftRight
  rw [if_neg (by decide)]
  change (w.val.val >>> 160) % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.shiftRight_eq_div_pow]
  change w.toNat / 2 ^ 160 % UInt256.size = w.toNat / EVM.twoPow 160
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt
    (Nat.div_le_self w.toNat (2 ^ 160)) w.val.isLt)]
  rfl

theorem approveShr160_eq_zero {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.shiftRight w (UInt256.ofNat 160) = UInt256.ofNat 0 := by
  apply u256_inj
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0
  rw [approveShr160_toNat, Nat.div_eq_of_lt]
  simpa [EVM.addressModulus] using hcanon

theorem approveShr160_ne_zero {w : UInt256} (hdirty : EVM.addressModulus ≤ w.toNat) :
    UInt256.shiftRight w (UInt256.ofNat 160) ≠ UInt256.ofNat 0 := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  change (UInt256.shiftRight w ⟨160⟩).toNat = 0 at hnat
  rw [approveShr160_toNat, Nat.div_eq_zero_iff] at hnat
  rcases hnat with hpow | hlt
  · exact (by native_decide : EVM.twoPow 160 ≠ 0) hpow
  · exact (not_lt_of_ge (by simpa [EVM.addressModulus] using hdirty)) hlt

end FeProofs.ERC20
