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
      t 3 (by omega), Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false,
      show ¬ (2 < 1) by omega, show ¬ (3 < 1) by omega, Fe.M.exec_bind, ld 0 (by omega),
      Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), pure_bind, t 1 (by omega), t 2 (by omega),
      t 3 (by omega), Nat.lt_irrefl, decide_false, decide_true, Bool.false_eq_true, if_false,
      if_true, show (1 < 2) = True by simp, show ¬ (3 < 2) by omega, Fe.M.exec_bind,
      ld 0 (by omega), ld 1 (by omega), Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega),
      List.getElem?_eq_getElem (show 1 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), e 2 (by omega), pure_bind, t 1 (by omega),
      t 2 (by omega), t 3 (by omega), Nat.lt_irrefl, decide_false, decide_true,
      Bool.false_eq_true, if_false, if_true, show (1 < 3) = True by simp,
      show (2 < 3) = True by simp, Fe.M.exec_bind, ld 0 (by omega), ld 1 (by omega),
      ld 2 (by omega), Fe.M.exec_pure]
    simp [wideOf, toW, zero_w, List.getElem?_eq_getElem (show 0 < ls.length by omega),
      List.getElem?_eq_getElem (show 1 < ls.length by omega),
      List.getElem?_eq_getElem (show 2 < ls.length by omega)]
  · simp only [Wide_of, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), pure_bind,
      t 1 (by omega), t 2 (by omega), t 3 (by omega), t 4 (by omega), decide_true, if_true,
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

theorem has05_eq (r : Lib.Range_Known_0_Known_5) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_0_5 r (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < 5)) := by
  simp only [Lib.Range_has_0_5, range_has_eq (lo := 0) (hi := 5) hk (by norm_num) (by norm_num),
    bind_pure]

theorem has1_eq (N : ℕ) (hN : N < 2 ^ 256) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_1 ⟨(), UInt256.ofNat N⟩ (UInt256.ofNat k) = pure (decide (1 ≤ k ∧ k < N)) := by
  simp only [Lib.Range_has_1, range_has_eq (lo := 1) hk (by norm_num) hN, bind_pure]

theorem two_w : UInt256.ofNat 2 = Limb.w ⟨2, by norm_num⟩ := rfl

/-! ## The table as a vector, the walk invariant -/

/-- An empty entry. -/
def W0 : Wide := ⟨UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩

/-- The table with its first `c` entries filled. -/
def tabV (t : ℕ → L4) (c : ℕ) : Vector Wide 64 :=
  Vector.ofFn fun j => if j.val < c then toW (t j.val) else W0

theorem tabV_get (t : ℕ → L4) {c k : ℕ} (hk : k < c) (h64 : k < 64) : (tabV t c)[k]! = toW (t k) := by
  simp [tabV, getElem!_pos, h64, hk]

theorem tabV_set (t : ℕ → L4) (c : ℕ) : (tabV t c).set! c (toW (t c)) = tabV t (c + 1) := by
  rw [tabV, set!_ofFn', tabV]
  congr 1
  funext j
  by_cases h : j.val = c
  · simp [h]
  · by_cases h' : j.val < c
    · simp [h, h', show j.val < c + 1 by omega]
    · simp [h, h', show ¬ j.val < c + 1 by omega]

theorem tabV_zero (t : ℕ → L4) : Vector.replicate 64 W0 = tabV t 0 := by
  apply Vector.ext; intro j hj; simp [tabV]

/-- The walk's invariant at bit `i`: once started, the power stands for `b` to the prefix up to
    `i`; before, that prefix is zero. -/
def WInv (L : ℕ) (m : L4) (e total b i : ℕ) : Bool → L4 → Prop
  | true, p => MRep (2 ^ (64 * L)) m p (b ^ prefixOf e total i)
  | false, _ => prefixOf e total i = 0

theorem entry_lt {e total i width : ℕ} (hi : i < total) (hw : 1 ≤ width)
    (hb : bitOf e total i = 1) :
    (digitOf e total i (winEnd e total i width) - 1) / 2 < 2 ^ (width - 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := winEnd_bounds e total i width hi hw hb
  have hd := digit_lt e total i (winEnd e total i width)
  have hp : 2 ^ (winEnd e total i width - i) ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2w : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hw]
  omega

theorem entry_digit {e total i width : ℕ} (hi : i < total) (hw : 1 ≤ width)
    (hb : bitOf e total i = 1) :
    2 * ((digitOf e total i (winEnd e total i width) - 1) / 2) + 1 =
      digitOf e total i (winEnd e total i width) := by
  obtain ⟨h1, h2, h3, h4⟩ := winEnd_bounds e total i width hi hw hb
  have := digit_odd e total i _ h1 h2 h4
  omega

theorem one4_w : (Wide.mk (UInt256.ofNat 1) (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0)) = toW one4 := rfl

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
  · rw [if_neg (by omega), if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    by_cases hk : A.size + q ≤ j ∧ j < A.size + q + 8
    · rw [if_pos hk, if_pos (by omega), show j - (A.size + q) = j - A.size - q by omega]
    · rw [if_neg hk, if_neg (by omega)]

/-! ## The result, `L` limbs in a fresh array -/

/-- The first `L` limbs of `x`. -/
def limbsL (L : ℕ) (x : L4) : List Limb := [x.l0, x.l1, x.l2, x.l3].take L

theorem limbsL_length {L : ℕ} (hL : L ≤ 4) (x : L4) : (limbsL L x).length = L := by
  simp [limbsL]; omega

theorem val_limbsL {L : ℕ} (hL : 1 ≤ L ∧ L ≤ 4) (x : L4) (h : nat4 x < 2 ^ (64 * L)) :
    val (limbsL L x) = nat4 x := by
  have := x.l0.isLt; have := x.l1.isLt; have := x.l2.isLt; have := x.l3.isLt
  obtain ⟨h1, h4⟩ := hL
  interval_cases L <;> simp only [limbsL, List.take, val, nat4] at h ⊢ <;> omega

theorem nat4_mod2 (m : L4) : nat4 m % 2 = m.l0.val % 2 := by
  unfold nat4; omega

theorem topLimb_pos {L : ℕ} (hL : 1 ≤ L ∧ L ≤ 4) (m : L4) (hm : nat4 m < 2 ^ (64 * L))
    (h1 : 0 < nat4 m) (ht : 2 ^ (64 * (L - 1)) ≤ nat4 m) : 0 < (topLimb L m).val := by
  have := m.l0.isLt; have := m.l1.isLt; have := m.l2.isLt; have := m.l3.isLt
  obtain ⟨hl1, hl4⟩ := hL
  interval_cases L <;> simp only [topLimb, nat4, if_true, if_false, Nat.reduceEqDiff] at hm h1 ht ⊢ <;> omega

/-- The stores of `small_power<L>`'s exit: limb `k < L` of `x` at `q + 8 k`. -/
def storeL (L : ℕ) (mem : ByteArray) (q : ℕ) (x : L4) : ByteArray :=
  let m := store8 mem q x.l0
  let m := if 1 < L then store8 m (q + 8) x.l1 else m
  let m := if 2 < L then store8 m (q + 16) x.l2 else m
  if 3 < L then store8 m (q + 24) x.l3 else m

theorem storeL_eq (L : ℕ) (hL : 1 ≤ L ∧ L ≤ 4) (A : ByteArray) (x : L4) :
    storeL L (A ++ zeros (8 * L)) A.size x = A ++ limbBytes (limbsL L x) := by
  obtain ⟨h1, h4⟩ := hL
  interval_cases L <;> simp only [storeL, limbsL, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, List.take,
    limbBytes, ByteArray.append_empty]
  · rw [store8_zeros A _ 0 _ rfl, zeros_zero, ByteArray.append_empty]
  · rw [store8_zeros A _ 8 _ rfl, store8_zeros _ _ 0 _ (by simp), zeros_zero, ByteArray.append_empty,
      ByteArray.append_assoc]
  · rw [store8_zeros A _ 16 _ rfl, store8_zeros _ _ 8 _ (by simp), store8_zeros _ _ 0 _ (by simp),
      zeros_zero, ByteArray.append_empty, ByteArray.append_assoc, ByteArray.append_assoc]
  · rw [store8_zeros A _ 24 _ rfl, store8_zeros _ _ 16 _ (by simp), store8_zeros _ _ 8 _ (by simp),
      store8_zeros _ _ 0 _ (by simp), zeros_zero, ByteArray.append_empty, ByteArray.append_assoc,
      ByteArray.append_assoc, ByteArray.append_assoc]

/-- Element `k < L` of a fresh array of `L` limbs. -/
theorem idx_fresh {sz L k : ℕ} (hk : k < L) (hroom : sz + 8 * L < UInt256.size) :
    Lib.MemArray_index_mut_u64 ⟨UInt256.ofNat sz, UInt256.ofNat L⟩ (UInt256.ofNat k) =
      pure (UInt256.ofNat (sz + 8 * k), fun _ => pure ⟨UInt256.ofNat sz, UInt256.ofNat L⟩) := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  have h := index_mut_eq (a := ⟨UInt256.ofNat sz, UInt256.ofNat L⟩) (i := k)
    (by rw [toNat_lit (by omega)]; exact hk) (by rw [toNat_lit (show sz < 2 ^ 256 by omega)]; omega)
  rwa [toNat_lit (show sz < 2 ^ 256 by omega)] at h


theorem sub0_minv (a : Limb) :
    IntTy.subW (.u 64) (UInt256.ofNat 0) ((newton a)^[5] a).w = (minv a).w := subW64_eq 0 _

theorem tabV_set0 (L : ℕ) (m : L4) (inv : Limb) (t0 : L4) :
    (tabV (tbl L m inv t0) 0).set! 0 (toW t0) = tabV (tbl L m inv t0) 1 := tabV_set _ 0

theorem tabV_get0 (L : ℕ) (m : L4) (inv : Limb) (t0 : L4) {c : ℕ} (hc : 0 < c) :
    (tabV (tbl L m inv t0) c)[0]! = toW t0 := tabV_get _ hc (by omega)

theorem w0_eq : Wide.mk (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) = W0 := rfl

end FeProofs.Modexp
