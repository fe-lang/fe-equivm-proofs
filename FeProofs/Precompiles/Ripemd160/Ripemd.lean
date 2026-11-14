import FeProofs.Precompiles.Ripemd160.Compress
import FeProofs.Precompiles.Ripemd160.Block
import FeProofs.Precompiles.Ripemd160.Digest

/-!
# Ripemd160: `ripemd160` on a buffer

On a buffer holding the message `d`, the exported `ripemd160_MemBuffer` returns, with the world
unchanged, the word whose big-endian bytes are EVMLean's 20-byte digest (`ripemd160_exec`): the
block loop runs `ripemd_compress` on each of the `blocksOf d.size` padded blocks (`block_loop`),
and the digest loop packs the five state words, byte-swapped (`digest_loop`).  Both loops are
bounded, so the run always returns.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Ripemd160

open FeProofs.Precompiles
open Precompiles.Exported.Ripemd160

/-- Word `k` of the state. -/
def sget (S : RIPEMD160.State) : ℕ → UInt32
  | 0 => S.h₀
  | 1 => S.h₁
  | 2 => S.h₂
  | 3 => S.h₃
  | _ => S.h₄

theorem toV5_get (S : RIPEMD160.State) {k : ℕ} (hk : k < 5) : (toV5 S)[k]! = lw32 (sget S k) := by
  interval_cases k <;> rfl

/-- The big-endian number of the little-endian bytes of the first `k` state words. -/
def digestN (S : RIPEMD160.State) : ℕ → ℕ
  | 0 => 0
  | k + 1 => digestN S k * 2 ^ 32 + fromBytesBigEndian (RIPEMD160.wordBytes (sget S k))

theorem be_lt (x : UInt32) : fromBytesBigEndian (RIPEMD160.wordBytes x) < 2 ^ 32 := by
  rw [wordBytes_be]; omega

theorem digestN_lt (S : RIPEMD160.State) : ∀ k, digestN S k < 2 ^ (32 * k)
  | 0 => by simp [digestN]
  | k + 1 => by
    have := digestN_lt S k; have := be_lt (sget S k)
    rw [digestN, show 32 * (k + 1) = 32 * k + 32 by ring, pow_add]
    nlinarith

/-- The digest loop, from word `k`. -/
theorem digest_loop (S : RIPEMD160.State) r2 r3 :
    ∀ n k, k + n = 5 →
      ripemd160_MemBuffer.b1.b5 (toV5 S) (UInt256.ofNat (digestN S k)) r2 r3 (UInt256.ofNat k) =
        pure (UInt256.ofNat (digestN S 5))
  | 0, k, h => by
    subst h
    rw [ripemd160_MemBuffer.b1.b5.eq_1]
    simp [Lib.array_has_u32_5]
  | n + 1, k, h => by
    have hd := digestN_lt S k
    have hd' : digestN S k < 2 ^ 128 := lt_of_lt_of_le hd (Nat.pow_le_pow_right (by decide) (by omega))
    have hs := be_lt (sget S k)
    rw [ripemd160_MemBuffer.b1.b5.eq_1]
    simp only [Lib.array_has_u32_5, Lib.array_at_ref_u32_5, Lib.array_next_u32_5,
      toNat_lit (show k < 2 ^ 256 by omega), toNat_lit (show 5 < 2 ^ 256 by decide),
      decide_eq_true (show k < 5 by omega), ↓reduceIte, pure_bind,
      checkIndex_lit (show k < 5 by omega) (by decide), toV5_get S (show k < 5 by omega), swap32,
      Lib.usize_wrapping_add, Fe.EVM.ofNat_add_ofNat (show k + 1 < UInt256.size by
        unfold UInt256.size; omega)]
    have hsh : UInt256.ofNat (digestN S k) <<< UInt256.ofNat 32 =
        UInt256.ofNat (digestN S k * 2 ^ 32) := by
      apply word_eq_of_toNat
      rw [shiftLeft_toNat _ (by decide) (by rw [toNat_lit (by omega)]; omega),
        toNat_lit (by omega), toNat_lit (by omega), Nat.mul_comm]
    rw [hsh, lor_eq (by omega) (by omega),
      show digestN S k * 2 ^ 32 ||| fromBytesBigEndian (RIPEMD160.wordBytes (sget S k)) =
        digestN S (k + 1) from by
        rw [digestN, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hs, Nat.add_comm]]
    exact digest_loop S r2 r3 n (k + 1) (by omega)

/-- The chaining words after the first `i` blocks. -/
def stateAt (d : ByteArray) (i : ℕ) : RIPEMD160.State :=
  (List.range i).foldl (fun h i => compressFe h (Xof (blockB d i))) RIPEMD160.initial

theorem holds_len_eq {b : Lib.MemBuffer} {d mem : ByteArray} (h : Holds b d mem) :
    b.len = UInt256.ofNat d.size :=
  word_eq_of_toNat (by
    rw [h.len, toNat_lit (by have := h.bound; have := h.small; unfold UInt256.size at *; omega)])

theorem stateAt_end (d : ByteArray) : stateAt d (blocksOf d.size) = hashState d := rfl

/-- The block loop, from block `i`, then the digest loop. -/
theorem block_loop {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) (hn : d.size < 2 ^ 64) r1 :
    ∀ m i r3, i + m = blocksOf d.size →
      (ripemd160_MemBuffer.b1 b (UInt256.ofNat (blocksOf d.size)) (toV5 (stateAt d i)) r1
          ⟨(), UInt256.ofNat (blocksOf d.size)⟩ r3 (UInt256.ofNat i)).exec I w =
        some (.ok (UInt256.ofNat (digestN (hashState d) 5), w)) := by
  intro m
  induction m with
  | zero =>
    intro i r3 hi
    have hB : blocksOf d.size < 2 ^ 256 := by unfold blocksOf; omega
    rw [ripemd160_MemBuffer.b1.eq_1]
    simp only [Lib.Range_has_0, range_has_eq (show i < 2 ^ 256 by omega) (show 0 < 2 ^ 256 by decide) hB,
      show ¬ (0 ≤ i ∧ i < blocksOf d.size) by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
      pure_bind, Lib.array_start_u32_5]
    have hl := digest_loop (stateAt d i) ⟨(), UInt256.ofNat (blocksOf d.size)⟩ r3 5 0 rfl
    rw [show digestN (stateAt d i) 0 = 0 from rfl] at hl
    rw [hl, Fe.M.exec_pure, show i = blocksOf d.size by omega, stateAt_end]
  | succ m ih =>
    intro i r3 hi
    have hB : blocksOf d.size < 2 ^ 256 := by unfold blocksOf; omega
    rw [ripemd160_MemBuffer.b1.eq_1]
    simp only [Lib.Range_has_0, range_has_eq (show i < 2 ^ 256 by omega) (show 0 < 2 ^ 256 by decide) hB,
      decide_eq_true (show 0 ≤ i ∧ i < blocksOf d.size from ⟨by omega, by omega⟩), ↓reduceIte,
      pure_bind, Lib.Range_at_0, Lib.Range_next_0, Fe.M.exec_bind, len_exec, holds_len_eq h,
      padded_block_exec h hn (show i < blocksOf d.size by omega)]
    rw [ripemd_compress_eq]
    simp only [Fe.M.exec_pure, Lib.usize_wrapping_add,
      Fe.EVM.ofNat_add_ofNat (show i + 1 < UInt256.size by unfold UInt256.size; omega)]
    have hs : stateAt d (i + 1) = compressFe (stateAt d i) (Xof (blockB d i)) := by
      rw [stateAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [← hs]
    exact ih (i + 1) _ (by omega)

/-- **`ripemd160`**: on a buffer holding the message `d`, the word of the 20-byte digest of
EVMLean's `RIPEMD160.hash d`, the world unchanged. -/
theorem ripemd160_exec {b : Lib.MemBuffer} {d : ByteArray} {I : Env} {w : World}
    (h : Holds b d w.memory) (hn : d.size < 2 ^ 64) :
    (ripemd160_MemBuffer b).exec I w =
      some (.ok (UInt256.ofNat (fromByteArrayBigEndian (RIPEMD160.hash d)), w)) := by
  have hB : blocksOf d.size < 2 ^ 256 := by unfold blocksOf; omega
  have hpb : padded_blocks (UInt256.ofNat d.size) = pure (UInt256.ofNat (blocksOf d.size)) := by
    simp only [padded_blocks, checkedAdd_small (show d.size + 9 < 2 ^ 256 by omega),
      checkedAdd_small (show d.size + 9 + 63 < 2 ^ 256 by omega), pure_bind,
      checkedDiv_lit (show d.size + 9 + 63 < 2 ^ 256 by omega) (show 64 < 2 ^ 256 by decide)
        (by decide)]
    rfl
  unfold ripemd160_MemBuffer
  simp only [RIPEMD_IV, pure_bind, Fe.M.exec_bind, len_exec, holds_len_eq h, hpb, Lib.Range_start_0]
  rw [show (#v[UInt256.ofNat 1732584193, UInt256.ofNat 4023233417, UInt256.ofNat 2562383102,
      UInt256.ofNat 271733878, UInt256.ofNat 3285377520] : Vector UInt256 5) =
      toV5 (stateAt d 0) from rfl, block_loop h hn _ (blocksOf d.size) 0 _ (by omega)]
  congr 4
  rw [hash_eq, fromByteArrayBigEndian, byteArray_toList_eq]
  simp only [fromBytesBigEndian_append, RIPEMD160.wordBytes, List.length_cons, List.length_nil]
  simp only [digestN, sget]
  norm_num
  rfl

end FeProofs.Ripemd160
