import Reasoning.Memory

/-!
# Memory facts shared by the contracts
-/

open Ethereum Reasoning.Theory

namespace FeProofs

theorem small_gap (mem : ByteArray) (off : Nat) (h : off < 2 ^ 32) : off - mem.size < USize.size :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h USize.le_size)

end FeProofs
