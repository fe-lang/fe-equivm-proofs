import FeProofs.Lib.AbiEncode
import FeProofs.Lib.StaticCall
import FeProofs.Precompiles.Buffer
import FeProofs.Common.PackedByte

/-!
# Std's SSZ hashing, as exported

A specification of SSZ's hashing over 32-byte chunks, as byte arrays (`hashPair`, `u64Chunk`,
`mixInLength`), and what std's `ssz` code does: `hash_pair` hashes two words with the SHA-256
precompile, `u64_chunk` makes a `uint64`'s chunk, `mix_in_length` mixes a length into a root.

A word stands for the chunk of its 32 big-endian bytes (`UInt256.toByteArray`).  The names the
definitions would be proved equal to in EthLib's consensus specification: `hashPair` is SSZ's
`hash(a + b)` of two chunks (EthLib's `merkleize` step), `u64Chunk` the `hash_tree_root` of a
`uint64` (`serialize` padded to a chunk), `mixInLength` SSZ's `mix_in_length` of a length below
`2 ^ 64` (EthLib's `mixInLength`).

A hash makes two requests of the feed: `gas()`, then the static call.  `sha256To_exec` and
`hashPair_exec`: under a feed whose next two entries are `s1` and `s2`, the call is the one
`staticR` names with the gas word `s1.gas`; when it succeeds the result is the digest, when it
fails the run reverts with no data.  No condition on gas is needed: a call short of gas fails.
-/

namespace FeProofs.Lib

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

/-! ## The specification -/

/-- SSZ's hash of two chunks: SHA-256 of their concatenation. -/
def hashPair (a b : ByteArray) : ByteArray := SHA256.hash (a ++ b)

/-- The chunk of a `uint64`: its eight bytes little-endian, then zeros. -/
def u64Chunk (x : Nat) : ByteArray := Precompiles.le8 x ++ zeros 24

/-- SSZ's `mix_in_length` of a root and a length below `2 ^ 64`. -/
def mixInLength (root : ByteArray) (len : Nat) : ByteArray := hashPair root (u64Chunk len)

theorem hashPair_size (a b : ByteArray) : (hashPair a b).size = 32 := SHA256.hash_size _

/-- The word of a hash of two words: `hashPair` of their chunks. -/
def hashW (a b : UInt256) : UInt256 := uInt256OfByteArray (hashPair a.toByteArray b.toByteArray)

theorem hashW_bytes (a b : UInt256) :
    (hashW a b).toByteArray = hashPair a.toByteArray b.toByteArray :=
  toByteArray_uInt256OfByteArray_of_size32 (hashPair_size _ _)

/-! ## A hash through the precompile -/

variable (I : ExecutionEnv) (w : World)

set_option maxHeartbeats 4000000 in
/-- `sha256_64_to(p, r)`: SHA-256 of the 64 bytes at `p` through the precompile, its digest
    written at `r`.  On a call that succeeds, the digest's word; on one that fails, a revert
    with no data. -/
theorem sha256To_exec {s1 s2 : Supply} {rest : List Supply} (hfeed : w.feed = s1 :: s2 :: rest)
    (p r : UInt256) (hr : r.toNat ≤ w.memory.size) :
    (sha256_64_to p r).exec I w =
      if (staticR I w.accounts s1.gas s2 (UInt256.ofNat 2)
          (w.memory.readWithPadding p.toNat 64)).2.2.2.1 then
        some (.ok (uInt256OfByteArray (SHA256.hash (w.memory.readWithPadding p.toNat 64)),
          staticWorld I { w with feed := s2 :: rest } s1.gas s2 rest (UInt256.ofNat 2)
            (w.memory.readWithPadding p.toNat 64) r (UInt256.ofNat 32)))
      else some (.error (.revert .empty)) := by
  generalize hd : w.memory.readWithPadding p.toNat 64 = d
  have hs := staticR_sha256 (I := I) (σ := w.accounts) (g := s1.gas) (s := s2) (d := d)
  have hc := staticcall_exec (I := I) (w := { w with feed := s2 :: rest }) rfl s1.gas
    (UInt256.ofNat 2) p (UInt256.ofNat 64) r (UInt256.ofNat 32)
  simp only [show (UInt256.ofNat 64).toNat = 64 from rfl, hd] at hc
  rw [sha256_64_to]
  simp only [staticcallPrecompile]
  rw [exec_bind_ok I w (gas_exec hfeed), Fe.M.exec_bind, hc]
  by_cases hz : (staticR I w.accounts s1.gas s2 (UInt256.ofNat 2) d).2.2.2.1 = true
  · have ho := hs hz
    obtain ⟨H, hH⟩ : ∃ H : UInt256, H.toByteArray = SHA256.hash d :=
      ⟨_, toByteArray_uInt256OfByteArray_of_size32 (SHA256.hash_size d)⟩
    have hne : ¬ ((⟨1⟩ : UInt256) = UInt256.ofNat 0) := by decide
    simp only [hz, ite_true]
    simp [hne, returndatasize, mload, staticWorld, toNat32, ho, ← hH,
      show UInt256.ofNat 32 ⊓ UInt256.ofNat 32 = UInt256.ofNat 32 from rfl]
    rw [toByteArray_write32_read_back _ _ _ hr, uInt256OfByteArray_toByteArray]
  · simp only [hz, Bool.false_eq_true, ite_false]
    simp [revertEmpty, show ({ val := 0 } : UInt256) = UInt256.ofNat 0 from rfl]

theorem allocBytes_exec {n : Nat} (hn : n ≤ 2 ^ 64 - 1) (hroom : w.memory.size + n < UInt256.size) :
    (alloc_bytes (UInt256.ofNat n)).exec I w =
      some (.ok (UInt256.ofNat w.memory.size, { w with memory := w.memory ++ zeros n })) := by
  have hmaxa : ¬ UInt256.size - 1 < 18446744073709551615 := by decide
  simp [alloc_bytes, toNatMax, hmaxa, ulit_toNat' n (by omega),
    show (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 from rfl,
    show ¬ 18446744073709551615 < n by omega, alloc, hroom, replicate_zeros]

theorem hashPair_eq (a b : UInt256) :
    hash_pair a b = (do
      let p ← alloc_bytes (UInt256.ofNat 64)
      mstore p a
      mstore (p + UInt256.ofNat 32) b
      sha256_64_to p p) := by
  simp only [hash_pair, alloc_pair, alloc_ChunkPair, cast_u8_ChunkPair, write_pair,
    hash_pair_buffer, pair_offset, byte_ptr_ChunkPair, cast_ChunkPair_u8, pure_bind, bind_assoc,
    bind_pure]

/-- The memory after `hash_pair` stores its two words in a fresh buffer. -/
theorem pair_memory (mem : ByteArray) (a b : UInt256) :
    b.toByteArray.write 0 (a.toByteArray.write 0 (mem ++ zeros 64) mem.size 32) (mem.size + 32) 32 =
      mem ++ (a.toByteArray ++ b.toByteArray) := by
  have ha := toByteArray_size (v := a)
  have hb := toByteArray_size (v := b)
  rw [write_tail _ _ _ 0 0 32 (Nat.add_zero _).symm (by decide) (by omega)
      (by rw [zeros_size']; omega), zeros_extract', zeros_extract', toByteArray_extract_all,
    show zeros (min 0 64 - 0) = .empty from rfl, ByteArray.empty_append,
    zeros_size', show min 64 64 - (0 + 32) = 32 from rfl]
  have h1 : (a.toByteArray ++ zeros 32).size = 64 := by
    rw [ByteArray.size_append, ha, zeros_size']
  rw [write_tail _ _ _ 0 32 32 rfl (by decide) (by omega) (by omega), toByteArray_extract_all,
    extract_append_left _ _ _ _ (by rw [ha]), show (32 : Nat) = a.toByteArray.size from ha.symm,
    byteArray_extract_self]
  rw [byteArray_extract_empty_of_le _ (by simp only [ByteArray.size_append, zeros_size']; omega),
    ByteArray.append_empty]

set_option maxHeartbeats 4000000 in
/-- `hash_pair(a, b)`: the two words in a fresh buffer at the end of memory, hashed by the
    SHA-256 precompile from the feed's next two entries.  On a call that succeeds, `hashW a b`;
    on one that fails, a revert with no data. -/
theorem hashPair_exec {s1 s2 : Supply} {rest : List Supply} (hfeed : w.feed = s1 :: s2 :: rest)
    (a b : UInt256) (hroom : w.memory.size + 64 < UInt256.size) :
    (hash_pair a b).exec I w =
      if (staticR I w.accounts s1.gas s2 (UInt256.ofNat 2)
          (a.toByteArray ++ b.toByteArray)).2.2.2.1 then
        some (.ok (hashW a b,
          staticWorld I { w with
              memory := w.memory ++ (a.toByteArray ++ b.toByteArray)
              feed := s2 :: rest }
            s1.gas s2 rest (UInt256.ofNat 2) (a.toByteArray ++ b.toByteArray)
            (UInt256.ofNat w.memory.size) (UInt256.ofNat 32)))
      else some (.error (.revert .empty)) := by
  have tm : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ (by omega)
  have tm32 : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [ofNat_add_ofNat (by omega), ulit_toNat' _ (by omega)]
  have hd : (w.memory ++ (a.toByteArray ++ b.toByteArray)).readWithPadding w.memory.size 64 =
      a.toByteArray ++ b.toByteArray := by
    rw [readWithPadding_tail _ _ 0 64 (Nat.add_zero _).symm (by decide)
      (by simp [ByteArray.size_append]), Nat.zero_add,
      show (64 : Nat) = (a.toByteArray ++ b.toByteArray).size by
        simp [ByteArray.size_append], byteArray_extract_self]
  rw [hashPair_eq, exec_bind_ok I w (allocBytes_exec I w (by decide) hroom)]
  simp only [Fe.M.exec_bind, mstore, Fe.M.exec_modify, tm, tm32, pair_memory]
  have hs := sha256To_exec I { w with memory := w.memory ++ (a.toByteArray ++ b.toByteArray) }
    hfeed (UInt256.ofNat w.memory.size) (UInt256.ofNat w.memory.size)
    (by rw [tm, ByteArray.size_append]; omega)
  simp only [tm, hd] at hs
  rw [hs]
  rfl

/-! ## The chunk of a `uint64` -/

/-- The eight low bytes of `x` in reverse order. -/
def rev8 (x : Nat) : Nat :=
  ((x &&& 255) <<< 56) ||| (((x >>> 8) &&& 255) <<< 48) ||| (((x >>> 16) &&& 255) <<< 40) |||
  (((x >>> 24) &&& 255) <<< 32) ||| (((x >>> 32) &&& 255) <<< 24) ||| (((x >>> 40) &&& 255) <<< 16) |||
  (((x >>> 48) &&& 255) <<< 8) ||| ((x >>> 56) &&& 255)

theorem mul_add_or (a b : Nat) (hb : b < 256) : a * 256 + b = a <<< 8 ||| b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hb), Nat.shiftLeft_eq]

theorem byte_eq (x n : Nat) : x / 256 ^ n % 256 = (x >>> (8 * n)) % 2 ^ 8 := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]; rfl

set_option maxHeartbeats 4000000 in
theorem foldl_rev8 (x : Nat) :
    (List.range 8).foldl (fun acc n => acc * 256 + x / 256 ^ n % 256) 0 = rev8 x := by
  have hlt : ∀ n, x / 256 ^ n % 256 < 256 := fun n => Nat.mod_lt _ (by decide)
  have h255 : ∀ i, Nat.testBit 255 i = decide (i < 8) := fun i => Nat.testBit_two_pow_sub_one 8 i
  have h256 : ∀ y i, (y % 256).testBit i = (decide (i < 8) && y.testBit i) := fun y i =>
    Nat.testBit_mod_two_pow y 8 i
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  rw [mul_add_or _ _ (hlt _), mul_add_or _ _ (hlt _), mul_add_or _ _ (hlt _), mul_add_or _ _ (hlt _),
    mul_add_or _ _ (hlt _), mul_add_or _ _ (hlt _), mul_add_or _ _ (hlt _)]
  simp only [byte_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · interval_cases j <;> simp [rev8, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, h255, h256]
  · simp [rev8, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      h255, h256, Nat.sub_sub, show ¬ j - 56 < 8 by omega, show ¬ j - 48 < 8 by omega,
      show ¬ j - 40 < 8 by omega, show ¬ j - 32 < 8 by omega, show ¬ j - 24 < 8 by omega,
      show ¬ j - 16 < 8 by omega, show ¬ j - 8 < 8 by omega, show ¬ j < 8 by omega]

set_option maxHeartbeats 4000000 in
/-- The three passes of std's `u64_chunk` reverse the eight low bytes. -/
theorem byteSwap64_eq (x : Nat) :
    let y1 := ((x &&& 71777214294589695) <<< 8) ||| ((x >>> 8) &&& 71777214294589695)
    let y2 := ((y1 &&& 281470681808895) <<< 16) ||| ((y1 >>> 16) &&& 281470681808895)
    (((y2 <<< 32) ||| (y2 >>> 32)) % 2 ^ 64) = rev8 x := by
  intro y1 y2
  have h255 : ∀ i, Nat.testBit 255 i = decide (i < 8) := fun i => Nat.testBit_two_pow_sub_one 8 i
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  by_cases hj : j < 64
  · interval_cases j <;> simp [y1, y2, rev8, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, h255] <;> simp [Nat.testBit]
  · simp only [show ¬ j < 64 from hj, decide_false, Bool.false_and]
    simp [rev8, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h255,
      show ¬ j - 56 < 8 by omega, show ¬ j - 48 < 8 by omega, show ¬ j - 40 < 8 by omega,
      show ¬ j - 32 < 8 by omega, show ¬ j - 24 < 8 by omega, show ¬ j - 16 < 8 by omega,
      show ¬ j - 8 < 8 by omega, show ¬ j < 8 by omega]

theorem rev8_lt (x : Nat) : rev8 x < 2 ^ 64 := by
  unfold rev8
  have h : ∀ y k, k ≤ 56 → (y &&& 255) <<< k < 2 ^ 64 := fun y k hk => by
    rw [Nat.shiftLeft_eq]
    have := Nat.and_le_right (n := y) (m := 255)
    calc (y &&& 255) * 2 ^ k ≤ 255 * 2 ^ 56 :=
          Nat.mul_le_mul this (Nat.pow_le_pow_right (by norm_num) hk)
      _ < 2 ^ 64 := by norm_num
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (h _ _ (by norm_num)) (h _ _ (by norm_num)))
      (h _ _ (by norm_num))) (h _ _ (by norm_num))) (h _ _ (by norm_num))) (h _ _ (by norm_num)))
      (h _ _ (by norm_num))) ?_
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- The chunk's word: `x`'s bytes reversed, at the top. -/
theorem u64Chunk_toNat (x : Nat) :
    (uInt256OfByteArray (u64Chunk x)).toNat = rev8 x * 2 ^ 192 := by
  have hl : (Precompiles.le8 x).toList = List.ofFn fun k : Fin 8 => UInt8.ofNat (x / 256 ^ k.val) := by
    rw [byteArray_toList_eq]; simp [Precompiles.le8]
  have hz : (zeros 24).toList = List.replicate 24 0 := by
    rw [byteArray_toList_eq]; simp [zeros]
  have hr := rev8_lt x
  have hz0 : fromByteArrayBigEndian (zeros 24) = 0 := by
    have := fromBytesBigEndian_append_zeros [] 24
    rw [List.nil_append] at this
    rw [fromByteArrayBigEndian, hz, this]; rfl
  rw [uInt256OfByteArray_eq, u64Chunk, fromByteArrayBigEndian_append, hz0, Nat.add_zero,
    fromByteArrayBigEndian, hl, Precompiles.fromBytesBigEndian_ofFn (fun n => x / 256 ^ n) 8,
    foldl_rev8, zeros_size',
    ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `u64_chunk(x)`: the chunk of the `uint64` `x`, its bytes little-endian then zeros. -/
theorem u64Chunk_exec (v : UInt256) (hv : v.toNat < 2 ^ 64) :
    (u64_chunk v).exec I w = some (.ok (uInt256OfByteArray (u64Chunk v.toNat), w)) := by
  have hdef : u64_chunk v = pure (((((((((v &&& UInt256.ofNat 71777214294589695) <<< UInt256.ofNat 8) |||
      ((v >>> UInt256.ofNat 8) &&& UInt256.ofNat 71777214294589695)) &&& UInt256.ofNat 281470681808895)
        <<< UInt256.ofNat 16) ||| (((((v &&& UInt256.ofNat 71777214294589695) <<< UInt256.ofNat 8) |||
      ((v >>> UInt256.ofNat 8) &&& UInt256.ofNat 71777214294589695)) >>> UInt256.ofNat 16) &&&
        UInt256.ofNat 281470681808895)) <<< UInt256.ofNat 32) |||
      (((((((v &&& UInt256.ofNat 71777214294589695) <<< UInt256.ofNat 8) |||
      ((v >>> UInt256.ofNat 8) &&& UInt256.ofNat 71777214294589695)) &&& UInt256.ofNat 281470681808895)
        <<< UInt256.ofNat 16) ||| (((((v &&& UInt256.ofNat 71777214294589695) <<< UInt256.ofNat 8) |||
      ((v >>> UInt256.ofNat 8) &&& UInt256.ofNat 71777214294589695)) >>> UInt256.ofNat 16) &&&
        UInt256.ofNat 281470681808895)) >>> UInt256.ofNat 32)) <<< UInt256.ofNat 192) := by
    dsimp only [u64_chunk, u64_chunk_k1]
  rw [hdef, Fe.M.exec_pure]
  refine congrArg (fun e => some (Except.ok (e, w))) ?_
  apply u256_inj
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have e1 : ∀ a b : UInt256, (a &&& b) = UInt256.land a b := fun _ _ => rfl
  have e2 : ∀ a b : UInt256, (a ||| b) = UInt256.lor a b := fun _ _ => rfl
  have e3 : ∀ a b : UInt256, (a <<< b) = UInt256.shiftLeft a b := fun _ _ => rfl
  have e4 : ∀ a b : UInt256, (a >>> b) = UInt256.shiftRight a b := fun _ _ => rfl
  have tl : ∀ c, c < 2 ^ 256 → (UInt256.ofNat c).toNat = c := fun c hc => ulit_toNat' c (by omega)
  have shr : ∀ (a : UInt256) (k : Nat), k < 256 →
      (UInt256.shiftRight a (UInt256.ofNat k)).toNat = a.toNat >>> k := fun a k hk => by
    rw [shiftRight_toNat_of_lt _ _ hk, Nat.shiftRight_eq_div_pow]
  have shl : ∀ (a : UInt256) (k : Nat), k < 256 → a.toNat * 2 ^ k < UInt256.size →
      (UInt256.shiftLeft a (UInt256.ofNat k)).toNat = a.toNat <<< k := fun a k hk hb => by
    rw [shiftLeft_toNat_of_lt _ _ hk hb, Nat.shiftLeft_eq]
  have shl192 : ∀ a : UInt256, (UInt256.shiftLeft a (UInt256.ofNat 192)).toNat =
      a.toNat % 2 ^ 64 * 2 ^ 192 := fun a => by
    unfold UInt256.shiftLeft
    rw [ite_eq_right (by show ¬ (UInt256.ofNat 192).toNat ≥ 256; rw [tl _ (by norm_num)]; omega)]
    show (a.toNat <<< (UInt256.ofNat 192).toNat) % UInt256.size = _
    rw [tl _ (by norm_num), Nat.shiftLeft_eq, hsz,
      show (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 192 by norm_num, Nat.mul_mod_mul_right]
  have land_le : ∀ a b : UInt256, (UInt256.land a b).toNat ≤ b.toNat := fun a b => by
    rw [uland_toNat]; exact Nat.and_le_right
  rw [u64Chunk_toNat]
  simp only [e1, e2, e3, e4]
  set x := v.toNat
  set A := v.land (UInt256.ofNat 71777214294589695)
  set B := A.shiftLeft (UInt256.ofNat 8)
  set C := (v.shiftRight (UInt256.ofNat 8)).land (UInt256.ofNat 71777214294589695)
  set Y1 := B.lor C
  set E := (Y1.land (UInt256.ofNat 281470681808895)).shiftLeft (UInt256.ofNat 16)
  set F := (Y1.shiftRight (UInt256.ofNat 16)).land (UInt256.ofNat 281470681808895)
  set Y2 := E.lor F
  have t8 := tl 71777214294589695 (by norm_num)
  have t16 := tl 281470681808895 (by norm_num)
  have hA : A.toNat = x &&& 71777214294589695 := by rw [uland_toNat, t8]
  have hB : B.toNat = (x &&& 71777214294589695) <<< 8 := by
    have := Nat.and_le_right (n := x) (m := 71777214294589695)
    rw [shl _ 8 (by norm_num) (by rw [hA]; omega), hA]
  have hC : C.toNat = (x >>> 8) &&& 71777214294589695 := by rw [uland_toNat, shr _ 8 (by norm_num), t8]
  have hY1 : Y1.toNat = ((x &&& 71777214294589695) <<< 8) ||| ((x >>> 8) &&& 71777214294589695) := by
    rw [u256_lor_toNat_exact, hB, hC]
  have hEle := land_le Y1 (UInt256.ofNat 281470681808895)
  rw [t16] at hEle
  have hE : E.toNat = (Y1.toNat &&& 281470681808895) <<< 16 := by
    rw [shl _ 16 (by norm_num) (by omega), uland_toNat, t16]
  have hF : F.toNat = (Y1.toNat >>> 16) &&& 281470681808895 := by
    rw [uland_toNat, shr _ 16 (by norm_num), t16]
  have hY2 : Y2.toNat = E.toNat ||| F.toNat := u256_lor_toNat_exact _ _
  have hY2lt : Y2.toNat < 2 ^ 64 := by
    rw [hY2]
    refine Nat.or_lt_two_pow ?_ ?_
    · rw [hE, Nat.shiftLeft_eq]
      have := Nat.and_le_right (n := Y1.toNat) (m := 281470681808895)
      calc (Y1.toNat &&& 281470681808895) * 2 ^ 16 ≤ 281470681808895 * 2 ^ 16 :=
            Nat.mul_le_mul_right _ this
        _ < 2 ^ 64 := by norm_num
    · rw [hF]; exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  rw [shl192, u256_lor_toNat_exact, shl _ 32 (by norm_num) (by omega), shr _ 32 (by norm_num), hY2,
    hE, hF, hY1]
  exact congrArg (· * 2 ^ 192) (byteSwap64_eq x)

/-! ## What a hash that returns gives -/

/-- A hash through the precompile that returns gives the digest of its input, whatever the
    feed, and keeps every account's storage and the logs. -/
theorem sha256To_ok {p r v : UInt256} {w' : World} (h : (sha256_64_to p r).exec I w = some (.ok (v, w')))
    (hr : r.toNat ≤ w.memory.size) :
    v = uInt256OfByteArray (SHA256.hash (w.memory.readWithPadding p.toNat 64)) ∧
      SameStorage w.accounts w'.accounts ∧ w'.logs = w.logs := by
  rcases hf : w.feed with _ | ⟨s1, _ | ⟨s2, rest⟩⟩
  · rw [sha256_64_to, Fe.M.exec_bind, gas_exec_nil hf] at h; cases h
  · rw [sha256_64_to, exec_bind_ok I w (gas_exec hf)] at h
    simp only [staticcallPrecompile] at h
    rw [Fe.M.exec_bind, staticcall_nil (w := { w with feed := [] }) rfl] at h; cases h
  · rw [sha256To_exec I w hf p r hr] at h
    split at h
    · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, staticR_sha256_storage _ _ _ _ _, ?_⟩
      simp [staticWorld, staticR_sha256_substate, appended_self]
    · cases h

/-- A `hash_pair` that returns gives `hashW a b`, whatever the feed, and keeps every account's
    storage and the logs. -/
theorem hashPair_ok {a b v : UInt256} {w' : World} (h : (hash_pair a b).exec I w = some (.ok (v, w'))) :
    v = hashW a b ∧ SameStorage w.accounts w'.accounts ∧ w'.logs = w.logs := by
  have tm : w.memory.size + 64 < UInt256.size := by
    by_contra hc
    rw [hashPair_eq, Fe.M.exec_bind] at h
    simp [alloc_bytes, toNatMax, show ¬ UInt256.size - 1 < 18446744073709551615 by decide,
      show (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 from rfl, alloc, hc,
      toNat64] at h
  have t0 : (UInt256.ofNat w.memory.size).toNat = w.memory.size := ulit_toNat' _ (by omega)
  have t32 : (UInt256.ofNat w.memory.size + UInt256.ofNat 32).toNat = w.memory.size + 32 := by
    rw [ofNat_add_ofNat (by omega), ulit_toNat' _ (by omega)]
  rw [hashPair_eq, exec_bind_ok I w (allocBytes_exec I w (by decide) tm)] at h
  simp only [Fe.M.exec_bind, mstore, Fe.M.exec_modify, t0, t32, pair_memory] at h
  have := sha256To_ok I _ h (by rw [t0, ByteArray.size_append]; omega)
  simp only [t0] at this
  rw [readWithPadding_tail _ _ 0 64 (Nat.add_zero _).symm (by decide)
      (by simp [ByteArray.size_append]), Nat.zero_add,
    show (64 : Nat) = (a.toByteArray ++ b.toByteArray).size by simp [ByteArray.size_append],
    byteArray_extract_self] at this
  exact this

/-! ## The length mix-in -/

theorem mixInLength_eq (root len : UInt256) :
    mix_in_length root len = (u64_chunk len >>= fun c => hash_pair root c) := by
  simp only [mix_in_length, bind_pure]

/-- `mix_in_length(root, len)` hashes the root with the length's chunk. -/
theorem mixInLength_exec (root len : UInt256) (hl : len.toNat < 2 ^ 64) :
    (mix_in_length root len).exec I w =
      (hash_pair root (uInt256OfByteArray (u64Chunk len.toNat))).exec I w := by
  rw [mixInLength_eq, exec_bind_ok I w (u64Chunk_exec I w len hl)]

theorem u64Chunk_size (x : Nat) : (u64Chunk x).size = 32 := by
  simp [u64Chunk, ByteArray.size_append, Precompiles.le8_size]

/-- The word of a mix-in: `mixInLength` of the root's chunk. -/
theorem hashW_mix (root : UInt256) (x : Nat) :
    (hashW root (uInt256OfByteArray (u64Chunk x))).toByteArray = mixInLength root.toByteArray x := by
  rw [hashW_bytes, toByteArray_uInt256OfByteArray_of_size32 (u64Chunk_size x)]; rfl

end FeProofs.Lib
