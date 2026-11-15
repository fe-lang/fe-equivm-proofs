import FeProofs.Precompiles.Modexp.R2Exec
import FeProofs.Precompiles.Modexp.Exponent
import FeProofs.Precompiles.Modexp.Newton

/-!
# Modexp: what `small_power` reads and builds

- `wideOf`, `wide_of_exec`: `Wide::of(limbs, L)` reads the first `L` limbs of an array
  (`nat4_wideOf`: their number); `checkIndex_ok`, `set!_ofFn'`: the table's index checks and
  updates.
- `tbl`, `tbl_rep`, `mrep_base`: the table of odd powers in Montgomery form.
- `store8_append`: a limb stored into memory grown by an allocation stays in the new part.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- The first `L` (at most four) limbs, the others zero. -/
def wideOf (ls : List Limb) (L : ℕ) : L4 :=
  ⟨ls.getD 0 0, if 1 < L then ls.getD 1 0 else 0, if 2 < L then ls.getD 2 0 else 0,
    if 3 < L then ls.getD 3 0 else 0⟩

theorem nat4_wideOf (ls : List Limb) (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (hl : L ≤ ls.length) :
    nat4 (wideOf ls L) = val (ls.take L) := by
  obtain ⟨h1, h4⟩ := hL
  rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp at hl <;>
    interval_cases L <;> simp_all [wideOf, nat4, val] <;> ring

theorem load_at {w : World} {a : Lib.MemArray_u64} {ls : List Limb} (h : ArrayAt a ls w.memory)
    {i : ℕ} (hi : i < ls.length) (I : Env) :
    (do let p ← Lib.MemArray_index_ref_u64 a (UInt256.ofNat i); mloadInt (.u 64) p).exec I w =
      some (.ok ((ls.getD i 0).w, w)) := by
  have hb := h.addr_lt hi
  have hs := h.small
  rw [index_ref_eq (by rw [h.len]; exact hi) (by omega), pure_bind,
    load_exec h.limbs hi hs I, List.getD_eq_getElem _ _ hi]

/-- **`Wide::of(limbs, L)`** of an array of at least `L` limbs. -/
theorem wide_of_exec {w : World} {a : Lib.MemArray_u64} {ls : List Limb} (h : ArrayAt a ls w.memory)
    {L : ℕ} (hL : 1 ≤ L ∧ L ≤ 4) (hl : L ≤ ls.length) (I : Env) :
    (Wide_of a (UInt256.ofNat L)).exec I w = some (.ok (toW (wideOf ls L), w)) := by
  have e : ∀ i, i < ls.length → Lib.MemArray_index_ref_u64 a (UInt256.ofNat i) =
      pure (UInt256.ofNat (a.ptr.toNat + 8 * i)) := fun i hi =>
    index_ref_eq (by rw [h.len]; exact hi) (by have := h.addr_lt hi; have := h.small; omega)
  have ld : ∀ i (hi : i < ls.length), (mloadInt (.u 64) (UInt256.ofNat (a.ptr.toNat + 8 * i))).exec I w =
      some (.ok (ls[i].w, w)) := fun i hi => load_exec h.limbs hi h.small I
  have t : ∀ k : ℕ, k < 5 → (UInt256.ofNat k).toNat = k := fun k hk => toNat_lit (by omega)
  obtain ⟨h1, h4⟩ := hL
  interval_cases L
  · simp only [Wide_of, e 0 (by omega), pure_bind, t 1 (by omega), t 2 (by omega),
      t 3 (by omega), Nat.lt_irrefl, decide_false, Bool.false_eq_true, ite_false,
      show ¬ (2 < 1) by omega, show ¬ (3 < 1) by omega, Fe.M.exec_bind, ld 0 (by omega),
      Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), pure_bind, t 1 (by omega), t 2 (by omega),
      t 3 (by omega), Nat.lt_irrefl, decide_false, decide_true, Bool.false_eq_true, ite_false,
      ite_true, show (1 < 2) = True by simp, show ¬ (3 < 2) by omega, Fe.M.exec_bind,
      ld 0 (by omega), ld 1 (by omega), Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega),
      List.getElem?_eq_getElem (show 1 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), e 2 (by omega), pure_bind, t 1 (by omega),
      t 2 (by omega), t 3 (by omega), Nat.lt_irrefl, decide_false, decide_true,
      Bool.false_eq_true, ite_false, ite_true, show (1 < 3) = True by simp,
      show (2 < 3) = True by simp, Fe.M.exec_bind, ld 0 (by omega), ld 1 (by omega),
      ld 2 (by omega), Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega),
      List.getElem?_eq_getElem (show 1 < ls.length by omega),
      List.getElem?_eq_getElem (show 2 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), pure_bind,
      t 1 (by omega), t 2 (by omega), t 3 (by omega), t 4 (by omega), decide_true, ite_true,
      show (1 < 4) = True by simp, show (2 < 4) = True by simp, show (3 < 4) = True by simp,
      Fe.M.exec_bind, ld 0 (by omega), ld 1 (by omega), ld 2 (by omega), ld 3 (by omega),
      Fe.M.exec_pure]
    simp [wideOf, toW, List.getElem?_eq_getElem (show 0 < ls.length by omega),
      List.getElem?_eq_getElem (show 1 < ls.length by omega),
      List.getElem?_eq_getElem (show 2 < ls.length by omega),
      List.getElem?_eq_getElem (show 3 < ls.length by omega)]

theorem checkIndex_ok {k n : ℕ} (h : k < n) (hn : n < 2 ^ 256) :
    checkIndex (UInt256.ofNat k) n = pure () := by
  simp [checkIndex, toNat_lit (show k < 2 ^ 256 by omega), h]

theorem set!_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (x : α) :
    (Vector.ofFn f).set! i x = Vector.ofFn (fun j => if j.val = i then x else f j) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.set!, Vector.getElem_mk, Vector.toArray_ofFn, Array.set!, Vector.getElem_ofFn]
  rw [Array.getElem_setIfInBounds]
  · by_cases hji : i = j
    · subst hji; simp
    · have : ¬ j = i := fun e => hji e.symm
      simp only [hji, this, ↓reduceIte]
      exact Array.getElem_ofFn ..
  · simpa using hj

/-! ## The table of odd powers -/

/-- The table: `t0`, then each entry times `t0 ^ 2`, in Montgomery form. -/
def tbl (L : ℕ) (m : L4) (inv : Limb) (t0 : L4) : ℕ → L4
  | 0 => t0
  | k + 1 => smul L m inv (tbl L m inv t0 k) (smul L m inv t0 t0)

/-- Entry `k` of the table stands for `b ^ (2 k + 1)`. -/
theorem tbl_rep (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hm : nat4 m < 2 ^ (64 * L)) (hcop : Nat.Coprime (2 ^ (64 * L)) (nat4 m)) (t0 : L4) (b : ℕ)
    (h0 : MRep (2 ^ (64 * L)) m t0 b) :
    ∀ k, MRep (2 ^ (64 * L)) m (tbl L m inv t0 k) (b ^ (2 * k + 1))
  | 0 => by simpa [tbl] using h0
  | k + 1 => by
    rw [tbl, show b ^ (2 * (k + 1) + 1) = b ^ (2 * k + 1) * (b * b) by ring]
    exact mrep_mul L hL m _ _ inv _ _ hinv hm hcop (tbl_rep L hL m inv hinv hm hcop t0 b h0 k)
      (mrep_mul L hL m _ _ inv _ _ hinv hm hcop h0 h0)

/-- The base times `R² mod m` stands for the base. -/
theorem mrep_base (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (m bw r : L4) (inv : Limb) (hinv : InvOk m.l0 inv)
    (hm : nat4 m < 2 ^ (64 * L)) (hcop : Nat.Coprime (2 ^ (64 * L)) (nat4 m))
    (hb : nat4 bw < 2 ^ (64 * L)) (hr : nat4 r = 2 ^ (64 * L) * 2 ^ (64 * L) % nat4 m) :
    MRep (2 ^ (64 * L)) m (smul L m inv bw r) (nat4 bw) := by
  have hpos : 0 < nat4 m := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, Nat.coprime_zero_right] at hcop
    exact absurd hcop (Nat.one_lt_pow (by omega) (by norm_num)).ne')
  have hrl : nat4 r < nat4 m := by rw [hr]; exact Nat.mod_lt _ hpos
  obtain ⟨hc, hcr⟩ := smul_spec L hL m bw r inv hinv hm hb (by omega)
    (lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hb hrl.le (by positivity)) le_rfl)
  refine ⟨hc, ?_⟩
  have h1 : nat4 (smul L m inv bw r) * 2 ^ (64 * L) ≡ (nat4 bw * 2 ^ (64 * L)) * 2 ^ (64 * L)
      [MOD nat4 m] := by
    calc _ ≡ nat4 bw * nat4 r [MOD nat4 m] := hcr
      _ ≡ nat4 bw * (2 ^ (64 * L) * 2 ^ (64 * L)) [MOD nat4 m] :=
        Nat.ModEq.mul_left _ (by rw [hr]; exact Nat.mod_modEq _ _)
      _ = _ := by ring
  exact Nat.ModEq.cancel_right_of_coprime (by
    rw [Nat.coprime_comm] at hcop; exact Nat.Coprime.gcd_eq_one hcop) h1

/-! ## The result -/

/-- A limb stored past the old end of memory changes only the new part. -/
theorem store8_append (A B : ByteArray) (q : ℕ) (x : Limb) (h : q + 8 ≤ B.size) :
    store8 (A ++ B) (A.size + q) x = A ++ store8 B q x := by
  have hs : A.size + q + 8 ≤ (A ++ B).size := by rw [ByteArray.size_append]; omega
  apply ext_byteAt (by rw [store8_size x hs, ByteArray.size_append, ByteArray.size_append,
    store8_size x h])
  intro j _
  rw [byteAt_store8 x hs, byteAt_append, byteAt_append, byteAt_store8 x h]
  by_cases hj : j < A.size
  · rw [ite_eq_right (by omega), ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj]
    by_cases hk : A.size + q ≤ j ∧ j < A.size + q + 8
    · rw [ite_eq_left hk, ite_eq_left (by omega), show j - (A.size + q) = j - A.size - q by omega]
    · rw [ite_eq_right hk, ite_eq_right (by omega)]

end FeProofs.Modexp
