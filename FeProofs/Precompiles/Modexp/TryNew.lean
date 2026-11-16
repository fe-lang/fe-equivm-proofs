import FeProofs.Precompiles.Modexp.Work

/-!
# Modexp: `Modulus::try_new`

`Modulus::try_new(value, len)` normalises the first `len` limbs of `value`, a modulus `M` whose
limb `len - 1` is nonzero, for Knuth division: it shifts `M` left by `s = 64 len - 1 - log2 M`
(the leading zeros of its top limb) into a fresh array, so that the top limb has its high bit
set, and computes the Möller–Granlund reciprocal of the top limb (`len = 1`) or of the top two
(`len ≥ 2`).  `ModAt md M n s mem` says what the `Modulus` it returns holds; `try_new_exec` is
the run.  The asserts fail, with a trap, for `len = 0` (`try_new_zero`), `len` past the array
(`try_new_long`) and a zero limb `len - 1` (`try_new_top_zero`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- The reciprocal `try_new` computes for the normalised `N` of `n` limbs: of its top limb when
    `n = 1`, of its top two otherwise. -/
def recipOf (N n : ℕ) : ℕ :=
  if n = 1 then recip21 N else (2 ^ 192 - 1) / (N / 2 ^ (64 * (n - 2))) - 2 ^ 64

/-- The shift that normalises `M` as a number of `n` limbs. -/
def normShift (M n : ℕ) : ℕ := 64 * n - 1 - M.log2

/-- **A normalised modulus**: `md` holds `M` of `n` limbs shifted left by `s`, in the array
    `md.limbs`, with the top bit of its top limb set, and the reciprocal of its top limbs. -/
structure ModAt (md : Exported.Modexp.Modulus) (M n s : ℕ) (mem : ByteArray) : Prop where
  arr : ArrayAt md.limbs (limbsOf (M * 2 ^ s) n) mem
  len_eq : md.len = UInt256.ofNat n
  shift_eq : md.shift = UInt256.ofNat s
  pos : 0 < n
  n_lt : 8 * n < 2 ^ 64
  s_lt : s < 64
  lt : M * 2 ^ s < 2 ^ (64 * n)
  top : 2 ^ (64 * n - 1) ≤ M * 2 ^ s
  recip : md.reciprocal = UInt256.ofNat (recipOf (M * 2 ^ s) n)

/-! ## Limbs of a normalised number -/

/-- The top limb of `N`, with `2 ^ (64 n - 1) ≤ N < 2 ^ (64 n)`, has its high bit set. -/
theorem limbAt_top {N n : ℕ} (hn : 1 ≤ n) (hN : N < 2 ^ (64 * n)) (ht : 2 ^ (64 * n - 1) ≤ N) :
    2 ^ 63 ≤ (limbAt N (n - 1)).val := by
  have he : 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * (n - 1)) := by
    rw [← pow_add]; congr 1; omega
  have he' : 2 ^ (64 * n - 1) = 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [← pow_add]; congr 1; omega
  simp only [limbAt]
  rw [Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [he] at hN; exact hN)]
  rw [Nat.le_div_iff_mul_le (by positivity)]
  rw [he'] at ht; exact ht

/-- The top two limbs of `N < 2 ^ (64 n)`. -/
theorem top_limbs {N n : ℕ} (hn : 2 ≤ n) (hN : N < 2 ^ (64 * n)) :
    (limbAt N (n - 1)).val * 2 ^ 64 + (limbAt N (n - 2)).val = N / 2 ^ (64 * (n - 2)) := by
  have h := wv_limbAt N (n - 2) 2
  rw [wv_low, wv_one, show n - 2 + 1 = n - 1 by omega] at h
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  rw [← h]; ring

/-- The normalising shift: `M * 2 ^ s` has `n` limbs and the top bit of the top one set. -/
theorem normShift_spec {M n : ℕ} (hM : 0 < M) (hlo : 64 * (n - 1) ≤ M.log2) (hhi : M.log2 < 64 * n) :
    normShift M n < 64 ∧ M * 2 ^ normShift M n < 2 ^ (64 * n) ∧
      2 ^ (64 * n - 1) ≤ M * 2 ^ normShift M n := by
  have h1 : 2 ^ M.log2 ≤ M := Nat.log2_self_le (by omega)
  have h2 : M < 2 ^ (M.log2 + 1) := Nat.lt_log2_self
  refine ⟨by unfold normShift; omega, ?_, ?_⟩
  · calc M * 2 ^ normShift M n < 2 ^ (M.log2 + 1) * 2 ^ normShift M n :=
          Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = 2 ^ (64 * n) := by rw [← pow_add]; unfold normShift; congr 1; omega
  · calc 2 ^ (64 * n - 1) = 2 ^ M.log2 * 2 ^ normShift M n := by
          rw [← pow_add]; unfold normShift; congr 1; omega
      _ ≤ M * 2 ^ normShift M n := Nat.mul_le_mul_right _ h1

/-- The limbs a list holds are those of its number. -/
theorem getElem_limbAt (ls : List Limb) {k : ℕ} (hk : k < ls.length) : ls[k] = limbAt (val ls) k :=
  Fin.ext (by rw [← val_limb ls k hk]; rfl)

/-! ## The normalising loop -/

/-- Element `k < L` of a fresh array of `L` limbs, read. -/
theorem idx_ref_fresh {sz L k : ℕ} (hk : k < L) (hroom : sz + 8 * L < UInt256.size) :
    Lib.MemArray_index_ref_u64 ⟨UInt256.ofNat sz, UInt256.ofNat L⟩ (UInt256.ofNat k) =
      pure (UInt256.ofNat (sz + 8 * k)) := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  have h := index_ref_eq (a := ⟨UInt256.ofNat sz, UInt256.ofNat L⟩) (i := k)
    (by rw [toNat_lit (by omega)]; exact hk) (by rw [toNat_lit (show sz < 2 ^ 256 by omega)]; omega)
  rwa [toNat_lit (show sz < 2 ^ 256 by omega)] at h

theorem limbsMem_full (mem : ByteArray) (N n : ℕ) :
    limbsMem mem N n n = mem ++ limbBytes (limbsOf N n) := by
  simp [limbsMem, zeros_zero, ByteArray.append_empty, List.take_of_length_le]

/-- Limb `k` of the normalised modulus, as the loop of `try_new` computes it. -/
theorem norm_limb (M : ℕ) {s k : ℕ} (hs : s < 64) :
    IntTy.shl (.u 64) (limbAt M k).w (UInt256.ofNat s) |||
        (if s = 0 ∨ k = 0 then UInt256.ofNat 0
          else UInt256.ofNat ((limbAt M (k - 1)).val / 2 ^ (64 - s))) =
      (limbAt (M * 2 ^ s) k).w := by
  have hx := (limbAt M k).isLt
  rw [shl64_lit _ (by omega)]
  split_ifs with h
  · rw [lor_lit (by omega) (by norm_num), Nat.or_zero]
    rcases h with rfl | rfl
    · simp only [pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx]; rfl
    · rw [limbAt_shl_zero]; rfl
  · have hy := (limbAt M (k - 1)).isLt
    rw [lor_lit (by omega) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
      limbAt_shl M (by omega) hs (by omega)]
    rfl

/-- The exit of the loop: the reciprocal of the top limbs. -/
theorem try_new_exit {value : Lib.MemArray_u64} {w : World} {N n s : ℕ} (hn : 0 < n)
    (hN : N < 2 ^ (64 * n)) (htop : 2 ^ (64 * n - 1) ≤ N) (hn64 : 8 * n < 2 ^ 64)
    (hroom : w.memory.size + 8 * n < UInt256.size) (I : Env) :
    (Modulus_try_new.loop value (UInt256.ofNat n) (UInt256.ofNat n) (UInt256.ofNat s)
        ⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩ ⟨(), UInt256.ofNat n⟩ (UInt256.ofNat n)).exec I
        { w with memory := w.memory ++ limbBytes (limbsOf N n) } =
      some (.ok (.Some ⟨⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩, UInt256.ofNat n,
          UInt256.ofNat s, UInt256.ofNat (recipOf N n)⟩,
        { w with memory := w.memory ++ limbBytes (limbsOf N n) })) := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hL : LimbsAt (w.memory ++ limbBytes (limbsOf N n)) w.memory.size (limbsOf N n) :=
    limbsAt_limbBytes _ _
  have hsz : (w.memory ++ limbBytes (limbsOf N n)).size < UInt256.size := by
    simp [ByteArray.size_append]; omega
  rw [Modulus_try_new.loop.eq_1]
  simp only [has0_eq' n (by omega) (show n < 2 ^ 256 by omega),
    show (0 ≤ n ∧ n < n) = False from eq_false (by omega), decide_false, pure_bind,
    Bool.false_eq_true, ite_false, ofNat_eq_iff (show n < 2 ^ 256 by omega) (show 1 < 2 ^ 256 by norm_num)]
  by_cases h1 : n = 1
  · subst h1
    have hd : 2 ^ 63 ≤ (limbAt N 0).val := limbAt_top (n := 1) le_rfl hN htop
    have hl := load_exec (w := { w with memory := w.memory ++ limbBytes (limbsOf N 1) }) hL
      (i := 0) (by simp) hsz I
    rw [limbsOf_get N 1 0 (by omega)] at hl
    simp only [decide_true, ite_true, idx_ref_fresh (show 0 < 1 by omega) hroom, pure_bind,
      Fe.M.exec_bind, hl, reciprocal_2by1_eq _ hd, Fe.M.exec_pure]
    have hv : (limbAt N 0).val = N := by
      simp only [limbAt, Nat.mul_zero, pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt hN
    simp only [recipOf, ite_true, Limb.w, recip21L, hv]
  · have h2 : 2 ≤ n := by omega
    have hd : 2 ^ 63 ≤ (limbAt N (n - 1)).val := limbAt_top (by omega) hN htop
    have hl1 := load_exec (w := { w with memory := w.memory ++ limbBytes (limbsOf N n) }) hL
      (i := n - 1) (by simp; omega) hsz I
    have hl2 := load_exec (w := { w with memory := w.memory ++ limbBytes (limbsOf N n) }) hL
      (i := n - 2) (by simp; omega) hsz I
    rw [limbsOf_get N n _ (by omega)] at hl1 hl2
    simp only [h1, decide_false, Bool.false_eq_true, ite_false,
      checkedSub_lit (show n < 2 ^ 256 by omega) (show 1 ≤ n by omega),
      checkedSub_lit (show n < 2 ^ 256 by omega) (show 2 ≤ n by omega),
      idx_ref_fresh (show n - 1 < n by omega) hroom, idx_ref_fresh (show n - 2 < n by omega) hroom,
      pure_bind, Fe.M.exec_bind, hl1, hl2, reciprocal_3by2_eq _ _ hd, Fe.M.exec_pure]
    have hv := recip32_val _ (limbAt N (n - 2)) hd
    rw [top_limbs h2 hN] at hv
    simp only [recipOf, h1, ite_false, ← hv]
    rfl

/-- **The normalising loop of `try_new`**, from limb `k`: limb `k` of `M * 2 ^ s` into the fresh
    array, then on; at the end the exit. -/
theorem try_new_loop {value : Lib.MemArray_u64} {vs : List Limb} {w : World}
    (hv : ArrayAt value vs w.memory) {M n s : ℕ} (hnl : n ≤ vs.length) (hM : val (vs.take n) = M)
    (hs : s < 64) (hn : 0 < n) (hN : M * 2 ^ s < 2 ^ (64 * n)) (htop : 2 ^ (64 * n - 1) ≤ M * 2 ^ s)
    (hn64 : 8 * n < 2 ^ 64) (hroom : w.memory.size + 8 * n < UInt256.size) (I : Env) :
    ∀ m k, k + m = n →
      (Modulus_try_new.loop value (UInt256.ofNat n) (UInt256.ofNat n) (UInt256.ofNat s)
          ⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩ ⟨(), UInt256.ofNat n⟩ (UInt256.ofNat k)).exec I
          { w with memory := limbsMem w.memory (M * 2 ^ s) n k } =
        some (.ok (.Some ⟨⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩, UInt256.ofNat n,
            UInt256.ofNat s, UInt256.ofNat (recipOf (M * 2 ^ s) n)⟩,
          { w with memory := w.memory ++ limbBytes (limbsOf (M * 2 ^ s) n) }))
  | 0, k, hk => by
    rw [show k = n by omega, limbsMem_full]
    exact try_new_exit hn hN htop hn64 hroom I
  | m + 1, k, hk => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hkn : k < n := by omega
    have hvk : ArrayAt value vs (limbsMem w.memory (M * 2 ^ s) n k) := by
      rw [limbsMem, ByteArray.append_assoc]
      exact hv.append _ (by simp [ByteArray.size_append, Nat.min_eq_left hkn.le]; omega)
    have hg : ∀ i (hi : i < n), vs[i]'(by omega) = limbAt M i := fun i hi => by
      have := getElem_limbAt (vs.take n) (k := i) (by simp; omega)
      rwa [List.getElem_take, hM] at this
    have hb := hvk.addr_lt (i := k) (by omega)
    have hsm := hvk.small
    have hl := load_exec (w := { w with memory := limbsMem w.memory (M * 2 ^ s) n k }) hvk.limbs
      (i := k) (by omega) hvk.small I
    rw [hg k hkn] at hl
    have e := norm_limb M (k := k) hs
    rw [Modulus_try_new.loop.eq_1]
    simp only [has0_eq' n (by omega) (show k < 2 ^ 256 by omega), show (0 ≤ k ∧ k < n) = True from
      eq_true (by omega), decide_true, ite_true, Lib.Range_at_0, Lib.Range_next_0,
      next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind,
      index_ref_eq (a := value) (i := k) (by rw [hvk.len]; omega) (by omega), hl,
      ofNat_eq_iff (show s < 2 ^ 256 by omega) (show 0 < 2 ^ 256 by norm_num),
      ofNat_eq_iff (show k < 2 ^ 256 by omega) (show 0 < 2 ^ 256 by norm_num)]
    by_cases hlow : s = 0 ∨ k = 0
    · rw [ite_eq_left hlow] at e
      have hc : (decide (s = 0) = true ∨ (decide (s = 0) = false ∧ decide (k = 0) = true)) := by
        by_cases h : s = 0
        · left; simp [h]
        · right; rcases hlow with h' | h'
          · exact absurd h' h
          · simp [h, h']
      rcases hc with hc | ⟨hc1, hc2⟩
      · simp only [hc, ite_true, idx_fresh hkn hroom, e, Fe.M.exec_bind,
          store_exec (show w.memory.size + 8 * k < UInt256.size by omega),
          limbsMem_store _ _ _ _ hkn, pure_bind]
        exact try_new_loop hv hnl hM hs hn hN htop hn64 hroom I m (k + 1) (by omega)
      · simp only [hc1, hc2, Bool.false_eq_true, ite_false, ite_true, idx_fresh hkn hroom, e,
          Fe.M.exec_bind,
          store_exec (show w.memory.size + 8 * k < UInt256.size by omega),
          limbsMem_store _ _ _ _ hkn, pure_bind]
        exact try_new_loop hv hnl hM hs hn hN htop hn64 hroom I m (k + 1) (by omega)
    · rw [ite_eq_right hlow] at e
      have hl' := load_exec (w := { w with memory := limbsMem w.memory (M * 2 ^ s) n k }) hvk.limbs
        (i := k - 1) (by omega) hvk.small I
      rw [hg (k - 1) (by omega)] at hl'
      simp only [show decide (s = 0) = false from decide_eq_false (by omega),
        show decide (k = 0) = false from decide_eq_false (by omega), Bool.false_eq_true, ite_false,
        checkedSub_lit (show k < 2 ^ 256 by omega) (show 1 ≤ k by omega),
        index_ref_eq (a := value) (i := k - 1) (by rw [hvk.len]; omega) (by omega), hl',
        sub64_checked (show 64 < 2 ^ 64 by norm_num) (show s ≤ 64 by omega),
        limb_shr _ (show 64 - s < 256 by omega), idx_fresh hkn hroom, e, Fe.M.exec_bind,
        pure_bind, store_exec (show w.memory.size + 8 * k < UInt256.size by omega),
        limbsMem_store _ _ _ _ hkn]
      exact try_new_loop hv hnl hM hs hn hN htop hn64 hroom I m (k + 1) (by omega)

/-! ## `try_new` -/

/-- **`Modulus::try_new(value, n)`** for `0 < n` limbs of `value` with a nonzero top one: a
    fresh array at the end of memory holding `M * 2 ^ s`, `M` the first `n` limbs and `s` the
    normalising shift, and the `Modulus` of it. -/
theorem try_new_exec {value : Lib.MemArray_u64} {vs : List Limb} {w : World}
    (hv : ArrayAt value vs w.memory) {n : ℕ} (hn : 0 < n) (hnl : n ≤ vs.length)
    (htop : vs[n - 1]'(by omega) ≠ 0) (hn64 : 8 * n < 2 ^ 64) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * n < UInt256.size) (I : Env) :
    ∃ md : Exported.Modexp.Modulus, md.limbs = ⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩ ∧
      ModAt md (val (vs.take n)) n (normShift (val (vs.take n)) n)
        (w.memory ++ limbBytes (limbsOf (val (vs.take n) * 2 ^ normShift (val (vs.take n)) n) n)) ∧
      (Modulus_try_new value (UInt256.ofNat n)).exec I w =
        some (.ok (.Some md, { w with memory := (w.memory ++
          limbBytes (limbsOf (val (vs.take n) * 2 ^ normShift (val (vs.take n)) n) n)) })) := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  obtain ⟨M, hM⟩ : ∃ M, val (vs.take n) = M := ⟨_, rfl⟩
  have htl : (vs.take n).length = n := by simp; omega
  have hne : (vs.take n)[n - 1]'(by omega) ≠ 0 := by rwa [List.getElem_take]
  obtain ⟨hV, hlog⟩ := log2_val (vs.take n) (n - 1) (by omega)
    (fun j hj hj' => absurd hj (by omega)) hne
  rw [List.getElem_take, hM] at hlog
  rw [hM] at hV
  have hl63 := log2_lt64 (vs[n - 1]'(by omega))
  obtain ⟨hs64, hN, htopN⟩ := normShift_spec (M := M) (n := n) (by omega) (by omega) (by omega)
  have hsv : normShift M n = 63 - (vs[n - 1]'(by omega)).val.log2 := by
    unfold normShift; omega
  rw [hM]
  generalize normShift M n = s at hs64 hN htopN hsv
  have hpos : 0 < (vs[n - 1]'(by omega)).val :=
    Nat.pos_of_ne_zero (fun e => htop (Fin.ext e))
  have hb := hv.addr_lt (i := n - 1) (by omega)
  have hsm := hv.small
  have hl := load_exec (w := w) hv.limbs (i := n - 1) (by omega) hsm I
  have hal := try_new_zeroed_exec (n := n) I w h0 hroom hn64
  rw [show w.memory ++ zeros (8 * n) = limbsMem w.memory (M * 2 ^ s) n 0 by
    simp [limbsMem, limbBytes]] at hal
  have hloop := try_new_loop hv hnl hM hs64 hn hN htopN hn64 hroom I n 0 (by omega)
  refine ⟨⟨⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩, UInt256.ofNat n, UInt256.ofNat s,
    UInt256.ofNat (recipOf (M * 2 ^ s) n)⟩, rfl, ⟨?_, rfl, rfl, hn, hn64, hs64, hN, htopN, rfl⟩, ?_⟩
  · refine ⟨by simp; exact toNat_lit (by omega), ?_, by simp [ByteArray.size_append]; omega⟩
    rw [toNat_lit (show w.memory.size < 2 ^ 256 by omega)]
    exact limbsAt_limbBytes _ _
  · simp only [Modulus_try_new, downcast_u64_usize, pure_bind, toNat_lit (show 0 < 2 ^ 256 by norm_num),
      toNat_lit (show n < 2 ^ 256 by omega), hn, decide_true, ite_true, Lib.MemArray_len_u64,
      hv.len, show (n ≤ vs.length) = True from eq_true hnl,
      sub64_checked (show n < 2 ^ 64 by omega) (show 1 ≤ n by omega),
      index_ref_eq (a := value) (i := n - 1) (by rw [hv.len]; omega) (by omega), Fe.M.exec_bind, hl,
      ne_eq, limb_eq_zero_w, show (vs[n - 1]'(by omega) = 0) = False from eq_false htop,
      not_false_eq_true, Lib.assert, Bool.not_true, Bool.false_eq_true,
      ite_false, lz_limb _ hpos,
      checkedSub_lit (show 255 - (vs[n - 1]'(by omega)).val.log2 < 2 ^ 256 by omega)
        (show 192 ≤ 255 - (vs[n - 1]'(by omega)).val.log2 by omega),
      downcast_truncate_u256_u64_eq, toNat_lit (show s < 2 ^ 256 by omega),
      Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
      show 255 - (vs[n - 1]'(by omega)).val.log2 - 192 = s by omega, hal,
      Lib.Option_MemArray_u64.Some_0, Lib.Range_start_0]
    exact hloop

/-! ## The asserts -/

/-- `try_new(value, 0)` traps. -/
theorem try_new_zero (value : Lib.MemArray_u64) (I : Env) (w : World) :
    (Modulus_try_new value (UInt256.ofNat 0)).exec I w = some (.error .trap) := by
  simp [Modulus_try_new, downcast_u64_usize, Lib.assert, trap]

/-- `try_new(value, n)` traps for `n` past the array. -/
theorem try_new_long {value : Lib.MemArray_u64} {n : ℕ} (hn : 0 < n) (hn64 : n < 2 ^ 64)
    (hl : value.len.toNat < n) (I : Env) (w : World) :
    (Modulus_try_new value (UInt256.ofNat n)).exec I w = some (.error .trap) := by
  simp [Modulus_try_new, downcast_u64_usize, Lib.assert, trap, Lib.MemArray_len_u64,
    toNat_lit (show n < 2 ^ 256 by omega), show ¬ (n ≤ value.len.toNat) by omega]

/-- `try_new(value, n)` traps when limb `n - 1` of `value` is zero. -/
theorem try_new_top_zero {value : Lib.MemArray_u64} {vs : List Limb} {w : World}
    (hv : ArrayAt value vs w.memory) {n : ℕ} (hn : 0 < n) (hnl : n ≤ vs.length)
    (htop : vs[n - 1]'(by omega) = 0) (hn64 : n < 2 ^ 64) (I : Env) :
    (Modulus_try_new value (UInt256.ofNat n)).exec I w = some (.error .trap) := by
  have hb := hv.addr_lt (i := n - 1) (by omega)
  have hsm := hv.small
  have hl := load_exec (w := w) hv.limbs (i := n - 1) (by omega) hsm I
  simp only [Modulus_try_new, downcast_u64_usize, pure_bind, toNat_lit (show 0 < 2 ^ 256 by norm_num),
    toNat_lit (show n < 2 ^ 256 by omega), hn, decide_true, ite_true, Lib.MemArray_len_u64,
    hv.len, show (n ≤ vs.length) = True from eq_true hnl,
    sub64_checked (show n < 2 ^ 64 by omega) (show 1 ≤ n by omega),
    index_ref_eq (a := value) (i := n - 1) (by rw [hv.len]; omega) (by omega), Fe.M.exec_bind, hl,
    ne_eq, limb_eq_zero_w, htop, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
    Lib.assert, Bool.not_false, trap, Fe.M.exec_fail]

end FeProofs.Modexp
