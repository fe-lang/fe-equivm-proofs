import FeProofs.Deposit.ExportedStd
import FeProofs.Deposit.Tree

/-!
# FeDeposit's tree, as exported

`TreeInv I σ L`: the contract's storage in the accounts `σ` holds the incremental Merkle tree of
the leaves `L`: `deposit_count` (slot 32) is their count, `zero_hashes[h]` (slot `33 + h`) the
zero tree of height `h`, and `branch[h]` (slot `h`), wherever bit `h` of the count is set, the
complete subtree of height `h` left of the frontier.

`getDepositRoot_correct`: under `TreeInv`, `get_deposit_root`'s arm, whenever it returns,
returns the word of `depositRoot L`, whatever the feed.
-/

namespace FeProofs.Deposit.Exported

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory
open FeProofs.Lib (SameStorage hashW hashW_bytes hashPair_ok mixInLength_exec u64Chunk)
open FeProofs.Deposit (subtree leafAt zeroHash depositRoot zeroChunk)

/-- The storage of the contract `I` runs holds, in the accounts `σ`, the tree of the leaves `L`. -/
structure TreeInv (I : ExecutionEnv) (σ : AccountMap) (L : List ByteArray) : Prop where
  len : L.length < 2 ^ 32
  count : slotWord I σ (UInt256.ofNat 32) = UInt256.ofNat L.length
  zero : ∀ h, h < 32 → (slotWord I σ (UInt256.ofNat (33 + h))).toByteArray = zeroHash h
  branch : ∀ h, h < 32 → L.length / 2 ^ h % 2 = 1 →
    (slotWord I σ (UInt256.ofNat h)).toByteArray = subtree (leafAt L) h (L.length / 2 ^ h - 1)

theorem TreeInv.same {I : ExecutionEnv} {σ σ' : AccountMap} {L : List ByteArray}
    (h : TreeInv I σ L) (hs : SameStorage σ σ') : TreeInv I σ' L :=
  ⟨h.len, by rw [hs.slotWord]; exact h.count, fun k hk => by rw [hs.slotWord]; exact h.zero k hk,
    fun k hk hb => by rw [hs.slotWord]; exact h.branch k hk hb⟩

private theorem bind_ok_inv {I : ExecutionEnv} {w w' : World} {α β : Type} {m : FeM α}
    {k : α → FeM β} {b : β} (h : (m >>= k).exec I w = some (.ok (b, w'))) :
    ∃ a w₁, m.exec I w = some (.ok (a, w₁)) ∧ (k a).exec I w₁ = some (.ok (b, w')) := by
  rw [Fe.M.exec_bind] at h
  rcases hm : m.exec I w with _ | f | ⟨a, w₁⟩ <;> rw [hm] at h
  · cases h
  · cases h
  · exact ⟨a, w₁, rfl, h⟩

theorem mul_one_word (h : Nat) (hh : h < 2 ^ 64) : UInt256.ofNat h * UInt256.ofNat 1 = UInt256.ofNat h := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  rw [ofNat_mul_ofNat (by omega) (by decide) (by omega), Nat.mul_one]

/-- `branch[h]` is slot `h`. -/
theorem branchPlace (h : Nat) (hh : h < 2 ^ 64) :
    Field.store.branch.index 1 (UInt256.ofNat h) = .storage (UInt256.ofNat h) := by
  simp only [Place.index, Place.field, Field.store, Layout.DepositStore, Place.storage,
    mul_one_word h hh, List.getD_cons_zero]
  rw [show UInt256.ofNat 0 + UInt256.ofNat 0 = UInt256.ofNat 0 from rfl, ofNat_add_ofNat (by
    rw [show UInt256.size = 2 ^ 256 from rfl]; omega), Nat.zero_add]

/-- `zero_hashes[h]` is slot `33 + h`. -/
theorem zeroPlace (h : Nat) (hh : h < 2 ^ 64) :
    Field.store.zero_hashes.index 1 (UInt256.ofNat h) =
      .storage (UInt256.ofNat (33 + h)) := by
  simp only [Place.index, Place.field, Field.store, Layout.DepositStore, Place.storage,
    mul_one_word h hh]
  rw [show UInt256.ofNat 0 + UInt256.ofNat ([0, 32, 33].getD 2 0) = UInt256.ofNat 33 from rfl,
    ofNat_add_ofNat (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]

/-- `deposit_count` is slot 32. -/
theorem countPlace : Field.store.deposit_count = .storage (UInt256.ofNat 32) := rfl

variable (I : ExecutionEnv)

theorem rangeHas_exec (w : World) {h : Nat} (hh : h ≤ 32) :
    (Range_has_0 ⟨(), UInt256.ofNat 32⟩ (UInt256.ofNat h)).exec I w =
      some (.ok (decide (h < 32), w)) := by
  have th : (UInt256.ofNat h).toNat = h := ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  by_cases h32 : h < 32 <;> simp [Range_has_0, range_has, th, h32, toNat0, toNat32]

theorem truncate64_exec (w : World) {c : Nat} (hc : c < 2 ^ 64) :
    (downcast_truncate_u256_u64 (UInt256.ofNat c)).exec I w = some (.ok (UInt256.ofNat c, w)) := by
  have hm : UInt256.ofNat c &&& UInt256.ofNat 18446744073709551615 = UInt256.ofNat c := by
    apply u256_inj
    rw [show ∀ a b : UInt256, (a &&& b) = UInt256.land a b from fun _ _ => rfl, uland_toNat,
      ulit_toNat' c (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega),
      show (UInt256.ofNat 18446744073709551615).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  have ht : truncate 64 (UInt256.ofNat c) = UInt256.ofNat c := by
    unfold truncate
    rw [ulit_toNat' c (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega), Nat.mod_eq_of_lt hc]
  simp [downcast_truncate_u256_u64, u256_to_word, u64_IS_SIGNED, u64_MASK, U64_MASK, u64_from_word,
    hm, ht]

theorem land_one_eq_one {q : Nat} (hq : q < 2 ^ 64) :
    (UInt256.ofNat q &&& UInt256.ofNat 1 = UInt256.ofNat 1) ↔ q % 2 = 1 := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  rw [word_eq_iff, show ∀ a b : UInt256, (a &&& b) = UInt256.land a b from fun _ _ => rfl,
    uland_toNat, ulit_toNat' q (by omega), show (UInt256.ofNat 1).toNat = 1 from rfl,
    Nat.and_one_is_mod]

theorem div2_exec (w : World) {q : Nat} (hq : q < 2 ^ 64) :
    (checkedDiv (UInt256.ofNat q) (UInt256.ofNat 2)).exec I w =
      some (.ok (UInt256.ofNat (q / 2), w)) := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  have hd : UInt256.ofNat q / UInt256.ofNat 2 = UInt256.ofNat (q / 2) := by
    apply u256_inj
    change (UInt256.div _ _).toNat = _
    rw [udiv_toNat, ulit_toNat' q (by omega), show (UInt256.ofNat 2).toNat = 2 from rfl,
      ulit_toNat' _ (by omega)]
  simp [checkedDiv, hd, show UInt256.ofNat 2 ≠ ⟨0⟩ by decide]

theorem rootLoop {L : List ByteArray} {σ0 : AccountMap} (hinv : TreeInv I σ0 L) :
    ∀ k h (r1 : UInt256) (w w' : World) (v : UInt256), h + k = 32 →
      SameStorage σ0 w.accounts → r1.toByteArray = subtree (leafAt L) h (L.length / 2 ^ h) →
      (recv_GetDepositRoot.loop r1 (UInt256.ofNat (L.length / 2 ^ h)) ⟨(), UInt256.ofNat 32⟩
          (UInt256.ofNat h)).exec I w = some (.ok (v, w')) →
      v.toByteArray = depositRoot L := by
  intro k
  induction k with
  | zero =>
    intro h r1 w w' v hk hs hr hx
    obtain rfl : h = 32 := by omega
    have hl := hinv.len
    rw [recv_GetDepositRoot.loop.eq_1, Lib.exec_bind_ok I w (rangeHas_exec I w (le_refl _)),
      if_neg (by decide), countPlace, load_storage, Lib.exec_bind_ok I w (exec_sload _ I w),
      hs.slotWord, hinv.count, Lib.exec_bind_ok I w (truncate64_exec I w (by omega))] at hx
    simp only [bind_pure] at hx
    rw [mixInLength_exec I w _ _ (by rw [ulit_toNat' _ (by
      rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]; omega)] at hx
    obtain ⟨rfl, -, -⟩ := hashPair_ok I w hx
    rw [Lib.hashW_mix, hr, ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega),
      Nat.div_eq_of_lt (by omega)]
    rfl
  | succ k ih =>
    intro h r1 w w' v hk hs hr hx
    rw [recv_GetDepositRoot.loop.eq_1, Lib.exec_bind_ok I w (rangeHas_exec I w (by omega))] at hx
    simp only [show h < 32 by omega, decide_true, if_true] at hx
    have hl := hinv.len
    have hsz : UInt256.size = 2 ^ 256 := rfl
    have hq : L.length / 2 ^ h < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hck : (checkIndex (UInt256.ofNat h) 32).exec I w = some (.ok ((), w)) := by
      simp [checkIndex, ulit_toNat' h (by omega), show h < 32 by omega]
    have hnext : (Range_next_0 ⟨(), UInt256.ofNat 32⟩ (UInt256.ofNat h)) =
        pure (UInt256.ofNat (h + 1)) := by
      simp [Range_next_0, usize_wrapping_add, ofNat_add_ofNat (show h + 1 < UInt256.size by omega)]
    rw [Lib.exec_bind_ok I w (show (Range_at_0 ⟨(), UInt256.ofNat 32⟩ (UInt256.ofNat h)).exec I w =
      some (.ok (UInt256.ofNat h, w)) from rfl)] at hx
    by_cases hb : L.length / 2 ^ h % 2 = 1
    · rw [if_pos (by simpa [land_one_eq_one hq] using hb), Lib.exec_bind_ok I w hck, branchPlace h
        (by omega), load_storage, Lib.exec_bind_ok I w (exec_sload _ I w), hs.slotWord] at hx
      obtain ⟨v26, w1, hp, hx⟩ := bind_ok_inv hx
      obtain ⟨rfl, hs1, -⟩ := hashPair_ok I w hp
      rw [Lib.exec_bind_ok I w1 (div2_exec I w1 hq), hnext, Fe.M.exec_bind, Fe.M.exec_pure,
        ← FeProofs.Deposit.div_two_pow_succ] at hx
      refine ih (h + 1) _ w1 w' v (by omega) (hs.trans hs1) ?_ hx
      rw [hashW_bytes, hinv.branch h (by omega) hb, hr, FeProofs.Deposit.frontier_odd _ _ _ hb]
    · rw [if_neg (by simpa [land_one_eq_one hq] using hb), Lib.exec_bind_ok I w hck, zeroPlace h
        (by omega), load_storage, Lib.exec_bind_ok I w (exec_sload _ I w), hs.slotWord] at hx
      obtain ⟨v26, w1, hp, hx⟩ := bind_ok_inv hx
      obtain ⟨rfl, hs1, -⟩ := hashPair_ok I w hp
      rw [Lib.exec_bind_ok I w1 (div2_exec I w1 hq), hnext, Fe.M.exec_bind, Fe.M.exec_pure,
        ← FeProofs.Deposit.div_two_pow_succ] at hx
      refine ih (h + 1) _ w1 w' v (by omega) (hs.trans hs1) ?_ hx
      rw [hashW_bytes, hinv.zero h (by omega), hr, FeProofs.Deposit.frontier_even _ _ (by omega)]

/-- **`get_deposit_root`'s arm returns the deposit root.**  Under `TreeInv`, whenever the arm
    returns, whatever the feed supplied, its word is the root of the leaves with their count
    mixed in.  A hash call that fails reverts; a feed too short, or memory full, does not end. -/
theorem getDepositRoot_correct {L : List ByteArray} {w w' : World} {v : UInt256}
    (hinv : TreeInv I w.accounts L) (hx : recv_GetDepositRoot.exec I w = some (.ok (v, w'))) :
    v.toByteArray = depositRoot L := by
  have hl := hinv.len
  have hd : DEPOSIT_CONTRACT_TREE_DEPTH = pure (UInt256.ofNat 32) := rfl
  simp only [recv_GetDepositRoot, hd, Range_start_0, pure_bind, countPlace, load_storage] at hx
  rw [Lib.exec_bind_ok I w (exec_sload _ I w), hinv.count] at hx
  refine rootLoop I hinv 32 0 _ w w' v rfl (SameStorage.refl _) ?_
    (by simpa only [pow_zero, Nat.div_one] using hx)
  rw [Lib.word0_bytes, pow_zero, Nat.div_one]
  simp [subtree, leafAt, zeroChunk]

end FeProofs.Deposit.Exported
