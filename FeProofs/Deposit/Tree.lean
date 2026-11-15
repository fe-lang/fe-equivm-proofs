import FeProofs.Lib.Ssz

/-!
# The deposit tree: specification

The deposit contract's Merkle tree as plain Lean over 32-byte chunks: the depth-32 tree over a
list of leaves padded with zero chunks (`subtree`, `zeroHash`), its root with the count mixed in
(`depositRoot`), and the root of a deposit's data (`depositDataRoot`).

The EthLib definitions these are meant to be proved equal to (EthLib is not a dependency here):
`depositRoot` is `depositRootOf` (`EthLib/Consensus/Transition/Genesis.lean`), the root of the
list of `DepositData` roots with limit `2 ^ 32`, through `merkleizeFlat`
(`EthLib/Serialization/Proofs/Ssz/Flat/Walk.lean`); `depositDataRoot` is `hashTreeRoot` of
`DepositData` (`EthLib/Consensus/Containers/Misc.lean`).

`subtree_zero`, `subtree_congr`, `frontier_odd` and `frontier_even` are the facts the
incremental algorithm needs.
-/

namespace FeProofs.Deposit

open FeProofs.Lib

/-- The zero chunk. -/
def zeroChunk : ByteArray := zeros 32

/-- The root of a complete tree of height `h` over zero chunks. -/
def zeroHash : Nat → ByteArray
  | 0 => zeroChunk
  | h + 1 => hashPair (zeroHash h) (zeroHash h)

/-- The `i`-th leaf of the list `L` padded with zero chunks. -/
def leafAt (L : List ByteArray) (i : Nat) : ByteArray := L.getD i zeroChunk

/-- The root of the complete subtree of height `h` whose leaves are `f (i * 2 ^ h)`, …,
    `f ((i + 1) * 2 ^ h - 1)`. -/
def subtree (f : Nat → ByteArray) : Nat → Nat → ByteArray
  | 0, i => f i
  | h + 1, i => hashPair (subtree f h (2 * i)) (subtree f h (2 * i + 1))

/-- The deposit root of the leaves `L`: the depth-32 tree over them, with their count mixed in. -/
def depositRoot (L : List ByteArray) : ByteArray :=
  mixInLength (subtree (leafAt L) 32 0) L.length

/-- The root of a 48-byte public key: its two chunks, the second padded with zeros. -/
def pubkeyRoot (pk : ByteArray) : ByteArray :=
  hashPair (pk.extract 0 32) (pk.extract 32 48 ++ zeros 16)

/-- The root of a 96-byte signature: its three chunks and a zero chunk. -/
def signatureRoot (sig : ByteArray) : ByteArray :=
  hashPair (hashPair (sig.extract 0 32) (sig.extract 32 64)) (hashPair (sig.extract 64 96) zeroChunk)

/-- The root of a deposit's data: public key, withdrawal credentials, amount (in gwei) and
    signature, four chunks. -/
def depositDataRoot (pk wc sig : ByteArray) (amount : Nat) : ByteArray :=
  hashPair (hashPair (pubkeyRoot pk) wc) (hashPair (u64Chunk amount) (signatureRoot sig))

/-! ## Facts for the incremental algorithm -/

/-- A subtree past the leaves is a zero tree. -/
theorem subtree_zero (L : List ByteArray) (h i : Nat) (hi : L.length ≤ i * 2 ^ h) :
    subtree (leafAt L) h i = zeroHash h := by
  induction h generalizing i with
  | zero =>
    simp only [subtree, zeroHash, leafAt]
    rw [List.getD_eq_default _ _ (by simpa using hi)]
  | succ h ih =>
    simp only [subtree, zeroHash]
    rw [ih (2 * i) (by rw [pow_succ] at hi; nlinarith),
      ih (2 * i + 1) (by rw [pow_succ] at hi; have := Nat.zero_le (2 ^ h); nlinarith)]

/-- A subtree over leaves that agree below its end. -/
theorem subtree_congr {f g : Nat → ByteArray} (h i : Nat)
    (hfg : ∀ j, j < (i + 1) * 2 ^ h → f j = g j) : subtree f h i = subtree g h i := by
  induction h generalizing i with
  | zero => simp only [subtree]; exact hfg i (by simp)
  | succ h ih =>
    simp only [subtree]
    rw [ih (2 * i) (fun j hj => hfg j (by rw [pow_succ]; nlinarith)),
      ih (2 * i + 1) (fun j hj => hfg j (by rw [pow_succ]; nlinarith))]

theorem div_two_pow_succ (c h : Nat) : c / 2 ^ (h + 1) = c / 2 ^ h / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- The frontier node at height `h + 1` over a count whose bit `h` is set: the left sibling, a
    complete subtree, hashed with the frontier node at `h`. -/
theorem frontier_odd (f : Nat → ByteArray) (c h : Nat) (hc : c / 2 ^ h % 2 = 1) :
    subtree f (h + 1) (c / 2 ^ (h + 1)) =
      hashPair (subtree f h (c / 2 ^ h - 1)) (subtree f h (c / 2 ^ h)) := by
  rw [subtree, div_two_pow_succ]
  generalize c / 2 ^ h = q at hc ⊢
  rw [show 2 * (q / 2) = q - 1 by omega, show q - 1 + 1 = q by omega]

/-- The frontier node at height `h + 1` over a count whose bit `h` is clear: the frontier node
    at `h` hashed with a zero tree. -/
theorem frontier_even (L : List ByteArray) (h : Nat) (hc : L.length / 2 ^ h % 2 = 0) :
    subtree (leafAt L) (h + 1) (L.length / 2 ^ (h + 1)) =
      hashPair (subtree (leafAt L) h (L.length / 2 ^ h)) (zeroHash h) := by
  have hp := Nat.two_pow_pos h
  have hz := subtree_zero L h (L.length / 2 ^ h + 1) (by
      have := Nat.lt_div_mul_add (a := L.length) hp
      rw [Nat.succ_mul]; omega)
  rw [subtree, div_two_pow_succ]
  generalize hq : L.length / 2 ^ h = q at hc hz ⊢
  rw [show 2 * (q / 2) = q by omega, hz]

end FeProofs.Deposit
