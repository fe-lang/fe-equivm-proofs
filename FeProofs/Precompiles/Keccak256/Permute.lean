import FeProofs.Precompiles.Keccak256.Round
import FeProofs.Precompiles.Blake2F.Mix
import FeProofs.Precompiles.Exported.EcrecoverPrecompile
import FeProofs.Precompiles.Field.Checked

/-!
# Keccak: fevm's permutation is EVMLean's

fevm's Keccak keeps its state as `[u64; 25]`, which the exporter prints as `Vector UInt256 25` of
words below `2 ^ 64`: `toL s` for EVMLean's `Vector UInt64 25`, each lane as a word (`lw`).  On
it the exported `keccak_round` (in 20 pieces), whatever the state it writes into, is `pure` of
`roundK` (`keccak_round_eq`), and `permute`, whose rounds alternate between the state and a
scratch state, is `pure` of EVMLean's `Keccak256.permute` (`permute_spec`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Keccak

open FeProofs.Precompiles
open FeProofs.Blake2F (lw lw_lt lw_toNat xor_lw sub64)
open Precompiles.Exported.EcrecoverPrecompile

/-! ## Lanes -/

theorem not_lw (x : UInt64) : IntTy.not (.u 64) (lw x) = lw (~~~x) := by
  apply word_eq_of_toNat
  have hx := x.toNat_lt
  simp only [IntTy.not, IntTy.val, IntTy.wrap, lw_toNat, UInt64.toNat_not]
  rw [toNat_lit (by omega)]
  change _ = 2 ^ 64 - 1 - x.toNat
  omega

theorem and_lw (x y : UInt64) : lw x &&& lw y = lw (x &&& y) := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, lw_toNat, lw_toNat, lw_toNat, UInt64.toNat_and]

theorem rotl_toNat (x : UInt64) {k : ℕ} (hk0 : 0 < k) (hk : k < 64) :
    (rotl x k).toNat = x.toNat * 2 ^ k % 2 ^ 64 ||| x.toNat / 2 ^ (64 - k) := by
  have hko : k.toUInt64.toNat = k := by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have hsub : (64 - k).toUInt64.toNat = 64 - k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  simp only [rotl, show k ≠ 0 by omega, ite_false]
  change (x <<< k.toUInt64 ||| x >>> (64 - k).toUInt64).toNat = _
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hko, hsub,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show 64 - k < 64 by omega), Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]

/-- fevm's `rotate` is EVMLean's rotation. -/
theorem rotate_lw (x : UInt64) {k : ℕ} (hk0 : 0 < k) (hk : k < 64) :
    rotate (lw x) (UInt256.ofNat k) = pure (lw (rotl x k)) := by
  simp only [rotate, sub64 (show k ≤ 64 by omega), pure_bind, lw,
    shl_u64 (lw_lt x) (show k < 256 by omega), ushr_eq (lw_lt x) (show 64 - k < 256 by omega)]
  rw [lor_eq (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
      (lt_of_le_of_lt (Nat.div_le_self _ _) (lw_lt x)), rotl_toNat x hk0 hk]

/-! ## The state -/

/-- The 25 lanes, as the exported `[u64; 25]`. -/
def toL (s : Vector UInt64 25) : Vector UInt256 25 := s.map lw

theorem toL_get (s : Vector UInt64 25) {k : ℕ} (hk : k < 25) : (toL s)[k]! = lw s[k] := by
  simp [toL, getElem!_pos, hk]

theorem checkIndex_lit {k n : ℕ} (h : k < n) (hn : n < 2 ^ 256) :
    checkIndex (UInt256.ofNat k) n = pure () := FeProofs.Blake2F.checkIndex_lt h hn

theorem set!_eq {α : Type} {n : ℕ} (xs : Vector α n) {i : ℕ} (x : α) (h : i < n) :
    xs.set! i x = xs.set i x h := by
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_set!, Vector.toArray_set, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds, dite_eq_left (by simpa using h)]

theorem rotate_lit (x : UInt64) (k : ℕ) (hk0 : 0 < k) (hk : k < 64) :
    rotate (lw x) (UInt256.ofNat k) = pure (lw (rotl x k)) := rotate_lw x hk0 hk

set_option maxRecDepth 100000 in
/-- **A round**: `keccak_round a e rc` writes `roundK a rc` over `e`. -/
theorem keccak_round_eq (a : Vector UInt64 25) (e : Vector UInt256 25) (rc : UInt64) :
    keccak_round (toL a) e (lw rc) = pure ((), toL (roundK a rc)) := by
  simp (config := { decide := true }) only [keccak_round, keccak_round_k1, keccak_round_k2, keccak_round_k3, keccak_round_k4, keccak_round_k5, keccak_round_k6, keccak_round_k7, keccak_round_k8, keccak_round_k9, keccak_round_k10, keccak_round_k11, keccak_round_k12, keccak_round_k13, keccak_round_k14, keccak_round_k15, keccak_round_k16, keccak_round_k17, keccak_round_k18, keccak_round_k19, checkIndex_lit, toNat_lit, toL_get, xor_lw, not_lw, and_lw, rotate_lit, pure_bind]
  refine congrArg (fun v => (pure ((), v) : FeM (Unit × Vector UInt256 25))) ?_
  apply Vector.ext
  intro i hi
  simp (disch := decide) only [set!_eq]
  interval_cases i <;> simp only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, toL, roundK,
    Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]

/-! ## The permutation -/

/-- The round constants, as the exported `[u64; 24]`. -/
def RCW : Vector UInt256 24 := ⟨(RC.map lw).toArray, rfl⟩

theorem ROUND_CONSTANTS_eq : ROUND_CONSTANTS = pure RCW := rfl

theorem rc_get {m : ℕ} (hm : m < 24) : RCW[m]! = lw (RC[m]'(by simpa [RC] using hm)) := by
  simp only [RCW, getElem!_pos, hm]
  exact List.getElem_map ..

/-- The state after the first `m` rounds. -/
def st (s : Vector UInt64 25) (m : ℕ) : Vector UInt64 25 := (RC.take m).foldl roundK s

theorem st_succ (s : Vector UInt64 25) {m : ℕ} (hm : m < 24) :
    st s (m + 1) = roundK (st s m) (RC[m]'(by simpa [RC] using hm)) := by
  simp only [st]
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa [RC] using hm)]
  rfl

/-- The rounds from `m` on: the state is in `v0` after an even number of rounds and in the
scratch state `r0` after an odd one. -/
theorem permute_loop (s : Vector UInt64 25) :
    ∀ k ≤ 24, ∀ r0 r2 v0 : Vector UInt256 25,
      ((24 - k) % 2 = 0 → v0 = toL (st s (24 - k))) →
      ((24 - k) % 2 = 1 → r0 = toL (st s (24 - k))) →
      permute.loop r0 (UInt256.ofNat (24 - k)) r2 v0 = pure ((), toL (st s 24))
  | 0, _, r0, r2, v0, h0, _ => by
    rw [permute.loop.eq_1]
    simp only [Nat.sub_zero, toNat_lit (show 24 < 2 ^ 256 by decide), Nat.lt_irrefl, decide_false,
      Bool.false_eq_true, ite_false]
    rw [h0 rfl]
  | k + 1, hk, r0, r2, v0, h0, h1 => by
    have hm : 24 - (k + 1) < 24 := by omega
    have hn : 24 - (k + 1) + 1 = 24 - k := by omega
    have IH := permute_loop s k (by omega)
    rw [permute.loop.eq_1]
    simp only [toNat_lit (show 24 - (k + 1) < 2 ^ 256 by omega),
      toNat_lit (show 24 < 2 ^ 256 by decide), hm, decide_true, ite_true,
      checkedRem_lit _ (show 2 < 2 ^ 256 by decide) (show 0 < 2 by decide), pure_bind,
      ROUND_CONSTANTS_eq, checkIndex_lit hm (by decide), rc_get hm,
      checkedAdd_small (show 24 - (k + 1) + 1 < 2 ^ 256 by omega), hn]
    rcases Nat.mod_two_eq_zero_or_one (24 - (k + 1)) with he | ho
    · rw [h0 he, keccak_round_eq]
      simp only [he, decide_true, ite_true, pure_bind]
      exact IH _ _ _ (fun h => by omega) (fun _ => by rw [← hn, st_succ s hm])
    · have h10 : ¬ UInt256.ofNat 1 = UInt256.ofNat 0 := by decide
      simp only [ho, h1 ho, h10, decide_false, Bool.false_eq_true, ite_false, keccak_round_eq,
        pure_bind]
      exact IH _ _ _ (fun _ => by rw [← hn, st_succ s hm]) (fun h => by omega)

/-- **The permutation**: fevm's `permute` is EVMLean's. -/
theorem permute_spec (s : Vector UInt64 25) :
    permute (toL s) = pure ((), toL (Keccak256.permute s)) := by
  rw [permute, permute_eq]
  have := permute_loop s 24 le_rfl (Vector.replicate 25 (UInt256.ofNat 0)) default (toL s)
    (fun _ => rfl) (fun h => absurd h (by decide))
  rw [show st s 24 = RC.foldl roundK s from rfl] at this
  exact this

end FeProofs.Keccak
