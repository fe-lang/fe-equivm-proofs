import Reasoning.Memory
import Reasoning.MemCascade

/-!
# Memory facts shared by the contracts
-/

open Ethereum Reasoning.Theory

namespace FeProofs

theorem small_gap (mem : ByteArray) (off : Nat) (h : off < 2 ^ 32) : off - mem.size < USize.size :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h USize.le_size)

/-- Two words stored at `s` and `t = s + 32` read back as their concatenation. The offsets and the
length are parameters so that they match the literals a block summary leaves (after `u256_lits`). -/
theorem pairWords_read (mem : ByteArray) (a b : UInt256) (s t n : Nat) (ht : t = s + 32)
    (hn : n = 64) (hs : s + 32 < 2 ^ 32) :
    (b.toByteArray.write 0 (a.toByteArray.write 0 mem s 32) t 32).readWithPadding s n =
      a.toByteArray ++ b.toByteArray := by
  subst ht hn
  have h0 := toByteArray_write_size_ge_off_add32 a mem s (small_gap mem s (by omega))
  have h1 := toByteArray_write_size_ge_off_add32 b (a.toByteArray.write 0 mem s 32) (s + 32)
    (small_gap _ (s + 32) hs)
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ s 32 32 (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega),
    toByteArray_write_read_below_of_gap b _ (s + 32) s (by omega) (by omega)
      (small_gap _ (s + 32) hs),
    toByteArray_write_read_back_of_gap a mem s (small_gap mem s (by omega)),
    toByteArray_write_read_back_of_gap b _ (s + 32) (small_gap _ (s + 32) hs)]

/-- The memory after storing two words at `s` and `t = s + 32` reaches `s + 64`. -/
theorem pairWords_size (mem : ByteArray) (a b : UInt256) (s t : Nat) (ht : t = s + 32)
    (hs : s + 32 < 2 ^ 32) :
    s + 64 ≤ (b.toByteArray.write 0 (a.toByteArray.write 0 mem s 32) t 32).size := by
  subst ht
  have := toByteArray_write_size_ge_off_add32 b (a.toByteArray.write 0 mem s 32) (s + 32)
    (small_gap _ (s + 32) hs)
  omega

end FeProofs
