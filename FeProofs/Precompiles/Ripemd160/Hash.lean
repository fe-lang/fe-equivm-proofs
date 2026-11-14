import FeProofs.Precompiles.Ripemd160.CompressSpec
import FeProofs.Precompiles.Ripemd160.Pad

/-!
# Ripemd160: the hash block by block

EVMLean's `RIPEMD160.hash d` is the digest of `compressFe` folded over the blocks of the padded
message, block `i` read as the bytes `padByte d (64 i + k)` (`hash_eq`).
-/

namespace FeProofs.Ripemd160

open Ethereum

/-- The little-endian word `j` of a block of bytes, as `ripemd_compress` assembles it. -/
def Xof (B : Nat → UInt8) (j : Nat) : UInt32 :=
  (B (4 * j)).toUInt32 ||| (B (4 * j + 1)).toUInt32 <<< UInt32.ofNat 8 |||
    (B (4 * j + 2)).toUInt32 <<< UInt32.ofNat 16 ||| (B (4 * j + 3)).toUInt32 <<< UInt32.ofNat 24

/-- Block `i` of the padded message. -/
def blockB (d : ByteArray) (i : Nat) (k : Nat) : UInt8 := padByte d (64 * i + k)

theorem compressFe_congr (S : RIPEMD160.State) {X Y : Nat → UInt32} (h : ∀ k < 16, X k = Y k) :
    compressFe S X = compressFe S Y := by
  unfold compressFe
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
    h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
    h 15 (by decide)]

theorem word_blockB (d : ByteArray) {i k : Nat} (hi : i < blocksOf d.size) (hk : k < 16) :
    (Array.ofFn fun j : Fin 16 => RIPEMD160.word (RIPEMD160.pad d) (64 * i + 4 * j.val))[k]! =
      Xof (blockB d i) k := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp only [Array.getElem_ofFn, RIPEMD160.word, Xof, blockB]
  rw [pad_get d (by omega), pad_get d (by omega), pad_get d (by omega), pad_get d (by omega),
    show 64 * i + 4 * k + 1 = 64 * i + (4 * k + 1) by omega,
    show 64 * i + 4 * k + 2 = 64 * i + (4 * k + 2) by omega,
    show 64 * i + 4 * k + 3 = 64 * i + (4 * k + 3) by omega]
  rfl

/-- The chaining words after the blocks of the padded message. -/
def hashState (d : ByteArray) : RIPEMD160.State :=
  (List.range (blocksOf d.size)).foldl (fun h i => compressFe h (Xof (blockB d i)))
    RIPEMD160.initial

theorem fold_congr {α : Type} (f g : α → Nat → α) (l : List Nat) (hl : ∀ i ∈ l, ∀ a, f a i = g a i)
    (a : α) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [hl i (by simp) a]
    exact ih (fun j hj b => hl j (by simp [hj]) b) _

/-- **The hash** is the digest of `hashState`. -/
theorem hash_eq (d : ByteArray) :
    RIPEMD160.hash d = ⟨(RIPEMD160.wordBytes (hashState d).h₀ ++
      RIPEMD160.wordBytes (hashState d).h₁ ++ RIPEMD160.wordBytes (hashState d).h₂ ++
      RIPEMD160.wordBytes (hashState d).h₃ ++ RIPEMD160.wordBytes (hashState d).h₄).toArray⟩ := by
  have hf : (List.range ((RIPEMD160.pad d).size / 64)).foldl (fun h i => RIPEMD160.compress h
      (Array.ofFn fun j : Fin 16 => RIPEMD160.word (RIPEMD160.pad d) (64 * i + 4 * j.val)))
      RIPEMD160.initial = hashState d := by
    rw [pad_size, Nat.mul_div_cancel_left _ (by decide), hashState]
    apply fold_congr
    intro i hi S
    rw [← compressFe_eq, compressFe_congr S (fun k hk => word_blockB d (List.mem_range.mp hi) hk)]
  unfold RIPEMD160.hash
  simp only
  rw [hf]

end FeProofs.Ripemd160
