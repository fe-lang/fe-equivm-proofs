import FeProofs.Precompiles.Keccak256.Round
import FeProofs.Precompiles.Buffer

/-!
# Keccak: EVMLean's Keccak-256 of 64 bytes

The Keccak-256 of the 64 bytes `toBytes32 a ++ toBytes32 b` is one block: EVMLean's `hash`
absorbs no full block and pads the 64 bytes into the final block, whose 17 lanes are the eight
lanes of the bytes, `1` (the suffix `0x01` at byte 64) and `2 ^ 63` (the final bit at byte 135).
So the hash is `digest` of `Keccak256.permute (mix64 a b)` (`hash64`), where `mix64 a b` holds the
lanes and `digest` reads the first 32 bytes of the state, little-endian lane by lane.
-/

open Ethereum

namespace FeProofs.Keccak

open FeProofs.Precompiles

/-! ## Bytes -/

/-- Byte `k` of `toBytes32 a`. -/
def bt (a k : ℕ) : ℕ := a / 2 ^ (8 * (31 - k)) % 256

/-- Lane `i` of the bytes of `toBytes32 a`: bytes `8 i` to `8 i + 7`, the first least
significant. -/
def laneOf (a i : ℕ) : UInt64 :=
  UInt64.ofNat (be8 (bt a (8 * i + 7)) (bt a (8 * i + 6)) (bt a (8 * i + 5)) (bt a (8 * i + 4))
    (bt a (8 * i + 3)) (bt a (8 * i + 2)) (bt a (8 * i + 1)) (bt a (8 * i)))

/-- The state after absorbing the padded block of `toBytes32 a ++ toBytes32 b`. -/
def mix64 (a b : ℕ) : Vector UInt64 25 :=
  #v[laneOf a 0, laneOf a 1, laneOf a 2, laneOf a 3, laneOf b 0, laneOf b 1, laneOf b 2,
    laneOf b 3, 1, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The 32 bytes of the digest of a state. -/
def digest (st : Vector UInt64 25) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 =>
    (st[Fin.ofNat 25 (i.val / 8)].shiftRight (8 * (i.val % 8)).toUInt64).toUInt8⟩

theorem tb_size (a : ℕ) : (Weierstrass.toBytes32 a).size = 32 := Array.size_ofFn

theorem ba_get! (d : ByteArray) (k : ℕ) (h : k < d.size) : d[k]! = d[k] := by
  simp [h]

theorem tb_get (a k : ℕ) (hk : k < 32) :
    (Weierstrass.toBytes32 a)[k]'(by rw [tb_size]; exact hk) = (a >>> (8 * (31 - k))).toUInt8 := by
  simp only [ByteArray.getElem_eq_getElem_data, Weierstrass.toBytes32, Array.getElem_ofFn]

theorem app_lo {A B : ByteArray} (hA : A.size = 32) (hB : B.size = 32) {k : ℕ} (hk : k < 32) :
    (A ++ B)[k]! = A[k]'(by omega) := by
  rw [ba_get! _ _ (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_left (by omega)]

theorem app_hi {A B : ByteArray} (hA : A.size = 32) (hB : B.size = 32) {k : ℕ} (hk : 32 ≤ k)
    (hk' : k < 64) : (A ++ B)[k]! = B[k - 32]'(by omega) := by
  rw [ba_get! _ _ (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_right (by omega)]
  simp only [hA]

theorem tb_lo (a b : ℕ) {k : ℕ} (hk : k < 32) :
    (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)[k]! = (a >>> (8 * (31 - k))).toUInt8 := by
  rw [app_lo (tb_size a) (tb_size b) hk, tb_get a k hk]

theorem tb_hi (a b : ℕ) {k : ℕ} (hk : 32 ≤ k) (hk' : k < 64) :
    (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b)[k]! =
      (b >>> (8 * (31 - (k - 32)))).toUInt8 := by
  rw [app_hi (tb_size a) (tb_size b) hk hk', tb_get b (k - 32) (by omega)]

theorem toUInt8_toNat (a s : ℕ) : (a >>> s).toUInt8.toNat = a / 2 ^ s % 256 := by
  rw [Nat.toUInt8, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]

theorem or_step {x y s : ℕ} (hx : x < 2 ^ s) : x ||| y * 2 ^ s = x + y * 2 ^ s := by
  rw [Nat.lor_comm, mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx, add_comm]

theorem shl_byte (b : UInt8) {s : ℕ} (hs : s ≤ 56) :
    (b.toUInt64.shiftLeft (Nat.toUInt64 s)).toNat = b.toNat * 2 ^ s := by
  have hb := b.toNat_lt
  change (b.toUInt64 <<< s.toUInt64).toNat = _
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show s % 2 ^ 64 < 64 by omega), Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  calc b.toNat * 2 ^ s < 256 * 2 ^ s := by
        exact Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos s)
    _ = 2 ^ (8 + s) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Eight bytes ORed into a lane at their offsets. -/
theorem or8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (0 ||| b0.toUInt64.shiftLeft (Nat.toUInt64 0) ||| b1.toUInt64.shiftLeft (Nat.toUInt64 8) |||
        b2.toUInt64.shiftLeft (Nat.toUInt64 16) ||| b3.toUInt64.shiftLeft (Nat.toUInt64 24) |||
        b4.toUInt64.shiftLeft (Nat.toUInt64 32) ||| b5.toUInt64.shiftLeft (Nat.toUInt64 40) |||
        b6.toUInt64.shiftLeft (Nat.toUInt64 48) ||| b7.toUInt64.shiftLeft (Nat.toUInt64 56) : UInt64) =
      UInt64.ofNat (be8 b7.toNat b6.toNat b5.toNat b4.toNat b3.toNat b2.toNat b1.toNat b0.toNat) := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_or, shl_byte _ (show 0 ≤ 56 by omega), shl_byte _ (show 8 ≤ 56 by omega),
    shl_byte _ (show 16 ≤ 56 by omega), shl_byte _ (show 24 ≤ 56 by omega),
    shl_byte _ (show 32 ≤ 56 by omega), shl_byte _ (show 40 ≤ 56 by omega),
    shl_byte _ (show 48 ≤ 56 by omega), shl_byte _ le_rfl, UInt64.toNat_zero, Nat.zero_or]
  simp (disch := omega) only [or_step]
  rw [UInt64.toNat_ofNat', be8, Nat.mod_eq_of_lt (by omega)]
  ring

/-! ## The hash -/

set_option maxRecDepth 10000 in
/-- **Keccak-256 of 64 bytes**: one permutation of the padded block. -/
theorem hash64 (a b : ℕ) :
    Keccak256.hash (Weierstrass.toBytes32 a ++ Weierstrass.toBytes32 b) =
      digest (Keccak256.permute (mix64 a b)) := by
  unfold Keccak256.hash
  unfold_keccak_private [Ethereum.Keccak256.encodeDigest, Ethereum.Keccak256.absorb,
    Ethereum.Keccak256.absorbBlock, Ethereum.Keccak256.finalBlock, Ethereum.Keccak256.decodeLane]
  simp only [ByteArray.size_append, tb_size, Keccak256.rateBytes, Keccak256.digestBytes,
    Nat.reduceAdd, Nat.reduceDiv, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp only [Id.run_pure, List.range', List.forIn_cons, List.forIn_nil, pure_bind, map_pure,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceSub, Fin.ofNat, Fin.getElem_fin,
    Nat.zero_mul]
  simp only [Vector.getElem_ofFn, Vector.getElem_set, Vector.getElem_replicate, Nat.reduceEqDiff,
    Nat.reduceLT, ↓reduceIte, Nat.zero_add]
  simp (disch := omega) only [tb_lo, tb_hi]
  simp only [or8, toUInt8_toNat, UInt64.zero_xor, Nat.reduceSub, Nat.reduceMul]
  refine congrArg (fun v => digest (Keccak256.permute v)) ?_
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp only [Vector.getElem_set, Vector.getElem_replicate, Nat.reduceEqDiff,
    ↓reduceIte, mix64, laneOf, bt, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] <;> rfl

end FeProofs.Keccak
