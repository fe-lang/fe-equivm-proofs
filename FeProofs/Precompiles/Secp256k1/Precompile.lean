import FeProofs.Precompiles.Secp256k1.Recover
import FeProofs.Precompiles.Keccak256.Sponge

/-!
# EcrecoverPrecompile: ECRECOVER in the precompile's format

- `recover_signer_spec`: `recover_signer` on a recovery id `≤ 1` and `0 < r, s < n` diverges (in
  the inversions of `recover_spec`) or returns, the world unchanged, `addrOf` of the key
  `Spec.recover` gives: the low 160 bits of the Keccak-256 word of `x ‖ y` (`hashWord`, from
  `keccak_two_words`), or none.
- `ecrecover_spec`: `ecrecover` reads the input only through `word_at_MemBuffer`, at offsets 0,
  32, 64 and 96.  Given the four words `e, v, r, s` there (the world unchanged), it diverges or
  returns an output whose bytes in memory are `ecrecOut e v r s`: the 32-byte address word when
  `v` is 27 or 28 (the full word, compared exactly) and `Spec.recover e (v − 27) r s` gives a key,
  otherwise nothing.  fevm's check of `v`, `r = 0`, `r ≥ n`, `s = 0`, `s ≥ n` before
  `recover_signer` is the specification's: out-of-range `r` or `s` recover no key.
- The empty output, `MemBuffer::empty()`, allocates nothing (`empty_out`).  The address goes
  through `words`, whose `MemBuffer::try_new(32)` fails when memory is empty (the allocator's
  pointer is then 0); `words_out` needs memory nonempty, and `ecrecover_spec` gets that only when
  `v` is 27 or 28 (`hpos`), the one case that reaches `words`.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory
open scoped FeProofs.Lib

namespace FeProofs.EcrecoverPrecompile

open FeProofs.Precompiles FeProofs.Keccak
open Precompiles.Exported.Shared Precompiles.Exported.EcrecoverPrecompile
open FeProofs.Ecrecover (keyOf Fp)

/-! ## `recover_signer` -/

/-- The address `recover_signer` returns for a key: the low 160 bits of the hash of `x ‖ y`. -/
def addrOf : Option (Fp × Fp) → Option_u256
  | none => .None
  | some (x, y) => .Some (UInt256.ofNat (hashWord x.val y.val % 2 ^ 160))

theorem mask160 (a : ℕ) (ha : a < 2 ^ 256) :
    UInt256.ofNat a &&& UInt256.ofNat 1461501637330902918203684832716283019655932542975 =
      UInt256.ofNat (a % 2 ^ 160) := by
  apply word_eq_of_toNat
  change (UInt256.land _ _).toNat = _
  rw [uland_toNat, toNat_lit ha, toNat_lit (by decide), toNat_lit (by omega),
    show (1461501637330902918203684832716283019655932542975 : ℕ) = 2 ^ 160 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem hashWord_lt (x y : ℕ) : hashWord x y < 2 ^ 256 := by
  unfold hashWord wordOf
  have h0 := sw_lt (Keccak256.permute (state2 x y))[0]
  have h1 := sw_lt (Keccak256.permute (state2 x y))[1]
  have h2 := sw_lt (Keccak256.permute (state2 x y))[2]
  have h3 := sw_lt (Keccak256.permute (state2 x y))[3]
  omega

/-- **`recover_signer`**: for a recovery id `≤ 1` and `0 < r, s < n`, diverges (in the
inversions) or returns, the world unchanged, the address of the key `Spec.recover` gives. -/
theorem recover_signer_spec (e v r s : UInt256) (hv : v.toNat ≤ 1) (hr0 : 0 < r.toNat)
    (hr : r.toNat < Secp256k1.n) (hs0 : 0 < s.toNat) (hs : s.toNat < Secp256k1.n) (env : Env)
    (w : World) :
    (recover_signer e v r s).exec env w = none ∨
      (recover_signer e v r s).exec env w =
        some (.ok (addrOf (Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat), w)) := by
  unfold recover_signer
  rw [Fe.M.exec_bind]
  rcases FeProofs.Ecrecover.recover_spec e v r s hv hr0 hr hs0 hs env w with h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; right
    rcases Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat with _ | ⟨x, y⟩
    · rfl
    · have hx : (UInt256.ofNat x.val).toNat = x.val := toNat_lit (lt_trans (ZMod.val_lt x) (by decide))
      have hy : (UInt256.ofNat y.val).toNat = y.val := toNat_lit (lt_trans (ZMod.val_lt y) (by decide))
      simp only [keyOf, Option_PublicKey.Some_0, new_eq, pure_bind, update_first, update_second,
        hx, hy, finish_two, mask160 _ (hashWord_lt _ _), Fe.M.exec_pure, addrOf]

/-! ## The two outputs -/

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

/-- The empty output at the end of memory. -/
def emptyOut (w : World) : Output :=
  ⟨UInt256.ofNat 0, UInt256.ofNat 3000, ⟨UInt256.ofNat w.memory.size, UInt256.ofNat 0, UInt256.ofNat 0⟩⟩

/-- The empty output: `MemBuffer::empty()` allocates nothing. -/
theorem empty_out (env : Env) (w : World) (hroom : w.memory.size < UInt256.size) :
    (do
        let v47 ← SUCCESS
        let v49 ← MemBuffer_empty
        pure ({ status := v47, gas_used := UInt256.ofNat 3000, output := v49 } : Output)).exec env w =
      some (.ok (emptyOut w, w)) := by
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have h : w.memory ++ ({ data := #[] } : ByteArray) = w.memory := ByteArray.append_empty
  simp [SUCCESS, MemBuffer_empty, alloc, toNatMax, toNatU64, toNat0, hmax, hroom, h, emptyOut]

/-- The output of one word, in a buffer allocated at the end of memory. -/
def wordsOut (w : World) : Output :=
  ⟨UInt256.ofNat 0, UInt256.ofNat 3000,
    ⟨UInt256.ofNat w.memory.size, UInt256.ofNat 32, UInt256.ofNat 32⟩⟩

/-- `words([a])`: on nonempty memory `MemBuffer::try_new(32)` succeeds, and the output buffer
holds the 32 bytes of `a`. -/
theorem words_out (env : Env) (w : World) (a : UInt256) (hpos : 0 < w.memory.size)
    (hroom : w.memory.size + 32 < UInt256.size) :
    ∃ mem, (words_1 #v[a] (UInt256.ofNat 3000)).exec env w =
        some (.ok (wordsOut w, { w with memory := mem })) ∧
      mem.readWithPadding w.memory.size 32 = a.toByteArray := by
  have hmax : ¬ UInt256.size - 1 < 18446744073709551615 := by unfold UInt256.size; norm_num
  have hmul : checkedMul (UInt256.ofNat 1) (UInt256.ofNat 32) = pure (UInt256.ofNat 32) :=
    checkedMul_small (by decide) (by decide) (by decide)
  have hmul0 : checkedMul (UInt256.ofNat 0) (UInt256.ofNat 32) = pure (UInt256.ofNat 0) :=
    checkedMul_small (by decide) (by decide) (by decide)
  have hne : ¬ UInt256.ofNat w.memory.size = UInt256.ofNat 0 := by
    intro h
    have := congrArg UInt256.toNat h
    rw [toNat_lit (by unfold UInt256.size at hroom; omega), toNat_lit (by decide)] at this
    omega
  rw [words_1]
  simp [alloc, toNatMax, toNatU64, toNat0, toNat32, hmax, hroom, hmul, hne]
  have s32 : (UInt256.ofNat 32 - UInt256.ofNat 0).toNat = 32 := rfl
  have a32 : (UInt256.ofNat 0 + UInt256.ofNat 32).toNat = 32 := rfl
  have t1 : (UInt256.ofNat 1).toNat = 1 := rfl
  have hm : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
    toNat_lit (by unfold UInt256.size at hroom; omega)
  have n1 : UInt256.ofNat 0 + UInt256.ofNat 1 = UInt256.ofNat 1 := rfl
  rw [words_1.loop.eq_1]
  simp [Lib.Range_has_0, Lib.range_has, Lib.Range_at_0, Lib.Range_next_0, Lib.usize_wrapping_add,
    hmul0, checkIndex, toNat0, Lib.Option_u8.Some_0, Lib.Option_MemBuffer.Some_0, zeroMem, mstore,
    s32, a32, t1, n1, Fe.EVM.add_zero, toNat32, hm]
  rw [words_1.loop.eq_1]
  simp [Lib.Range_has_0, Lib.range_has, t1, SUCCESS, wordsOut]
  have hz : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  apply toByteArray_write32_read_back
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hz]) (by rw [ByteArray.size_append, hz]),
    ByteArray.size_append]
  omega

/-! ## `ecrecover` on the words of the input -/

/-- The output of ECRECOVER on the words `e, v, r, s`: the address word for a recovered key, empty
for `v ∉ {27, 28}` or no key. -/
noncomputable def ecrecOut (e v r s : ℕ) : ByteArray :=
  if v = 27 ∨ v = 28 then
    match Secp256k1.Spec.recover e (v - 27) r s with
    | some (x, y) => Weierstrass.toBytes32 (hashWord x.val y.val % 2 ^ 160)
    | none => .empty
  else .empty

theorem ecrecover_spec (input : MemBuffer) (e v r s : UInt256) (env : Env) (w : World)
    (h0 : (word_at_MemBuffer input (UInt256.ofNat 0)).exec env w = some (.ok (e, w)))
    (h32 : (word_at_MemBuffer input (UInt256.ofNat 32)).exec env w = some (.ok (v, w)))
    (h64 : (word_at_MemBuffer input (UInt256.ofNat 64)).exec env w = some (.ok (r, w)))
    (h96 : (word_at_MemBuffer input (UInt256.ofNat 96)).exec env w = some (.ok (s, w)))
    (hpos : v.toNat = 27 ∨ v.toNat = 28 → 0 < w.memory.size)
    (hroom : w.memory.size + 32 < UInt256.size) :
    (ecrecover_MemBuffer input).exec env w = none ∨
      ∃ o mem, (ecrecover_MemBuffer input).exec env w = some (.ok (o, { w with memory := mem })) ∧
        mem.readWithPadding o.output.ptr.toNat o.output.len.toNat =
          ecrecOut e.toNat v.toNat r.toNat s.toNat := by
  have lit : ∀ (x : UInt256) {k : ℕ}, k < 2 ^ 256 → (x = UInt256.ofNat k ↔ x.toNat = k) :=
    fun x k hk => ⟨fun h => by rw [h, toNat_lit hk], fun h => word_eq_of_toNat (by rw [h, toNat_lit hk])⟩
  have hroom0 : w.memory.size < UInt256.size := by omega
  have hemp : (emptyOut w).output.len.toNat = 0 := rfl
  -- the specification's guard: out-of-range `r` or `s` recover nothing
  have hnone : ∀ k, (r.toNat = 0 ∨ Secp256k1.n ≤ r.toNat ∨ s.toNat = 0 ∨ Secp256k1.n ≤ s.toNat) →
      Secp256k1.Spec.recover e.toNat k r.toNat s.toNat = none := by
    intro k h
    unfold Secp256k1.Spec.recover
    rw [if_neg (by omega)]
  unfold ecrecover_MemBuffer
  simp only [Fe.M.exec_bind, h0, h32, h64, h96, FeProofs.Ecrecover.N_eq,
    toNat_lit (show Secp256k1.n < 2 ^ 256 by decide), pure_bind]
  by_cases hv : v.toNat = 27 ∨ v.toNat = 28
  swap
  · have h1 : v ≠ UInt256.ofNat 27 := fun h => hv (Or.inl ((lit v (by decide)).mp h))
    have h2 : v ≠ UInt256.ofNat 28 := fun h => hv (Or.inr ((lit v (by decide)).mp h))
    simp only [h1, h2, ne_eq, not_false_eq_true, decide_true, if_true, empty_out env w hroom0]
    exact Or.inr ⟨_, _, rfl, by rw [hemp, byteArray_readWithPadding_zero, ecrecOut, if_neg hv]⟩
  have hempty : ecrecOut e.toNat v.toNat r.toNat s.toNat = .empty →
      (do
        let v47 ← SUCCESS
        let v49 ← MemBuffer_empty
        pure ({ status := v47, gas_used := UInt256.ofNat 3000, output := v49 } : Output)).exec env w =
        none ∨ ∃ o mem, (do
          let v47 ← SUCCESS
          let v49 ← MemBuffer_empty
          pure ({ status := v47, gas_used := UInt256.ofNat 3000, output := v49 } : Output)).exec env w =
          some (.ok (o, { w with memory := mem })) ∧
        mem.readWithPadding o.output.ptr.toNat o.output.len.toNat =
          ecrecOut e.toNat v.toNat r.toNat s.toNat := fun he =>
    Or.inr ⟨_, _, empty_out env w hroom0, by rw [hemp, byteArray_readWithPadding_zero, he]⟩
  have hbad : (r.toNat = 0 ∨ Secp256k1.n ≤ r.toNat ∨ s.toNat = 0 ∨ Secp256k1.n ≤ s.toNat) →
      ecrecOut e.toNat v.toNat r.toNat s.toNat = .empty := fun h => by
    rw [ecrecOut, if_pos hv, hnone _ h]
  have hv' : decide (v ≠ UInt256.ofNat 27) = true → decide (v ≠ UInt256.ofNat 28) = false := by
    intro h; simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h ⊢
    rcases hv with h' | h'
    · exact absurd ((lit v (by decide)).mpr h') h
    · exact (lit v (by decide)).mpr h'
  rcases Bool.eq_false_or_eq_true (decide (v ≠ UInt256.ofNat 27)) with c1 | c1
  on_goal 1 => simp only [c1, hv' c1, if_true, Bool.false_eq_true, if_false]
  on_goal 2 => simp only [c1, Bool.false_eq_true, if_false]
  all_goals
    simp only [decide_eq_true_eq]
    split_ifs with c3 c4 c5 c6
    · exact hempty (hbad (Or.inl ((lit r (by decide)).mp c3)))
    · exact hempty (hbad (Or.inr (Or.inl c4)))
    · exact hempty (hbad (Or.inr (Or.inr (Or.inl ((lit s (by decide)).mp c5)))))
    · exact hempty (hbad (Or.inr (Or.inr (Or.inr c6))))
    have h27 : 27 ≤ v.toNat := by omega
    have hsub : checkedSub v (UInt256.ofNat 27) = pure (UInt256.ofNat (v.toNat - 27)) := by
      unfold checkedSub
      rw [toNat_lit (by decide), if_neg (by omega)]
      congr 1
      apply word_eq_of_toNat
      change (UInt256.sub _ _).toNat = _
      rw [usub_toNat (by rw [toNat_lit (by decide)]; omega), toNat_lit (by decide),
        toNat_lit (by have := v.val.isLt; change v.toNat < 2 ^ 256 at this; omega)]
    have hid : (UInt256.ofNat (v.toNat - 27)).toNat = v.toNat - 27 :=
      toNat_lit (by have := v.val.isLt; change v.toNat < 2 ^ 256 at this; omega)
    have hr0 : 0 < r.toNat := Nat.pos_of_ne_zero fun h => c3 ((lit r (by decide)).mpr h)
    have hs0 : 0 < s.toNat := Nat.pos_of_ne_zero fun h => c5 ((lit s (by decide)).mpr h)
    simp only [hsub, pure_bind]
    rw [Fe.M.exec_bind]
    rcases recover_signer_spec e _ r s (by rw [hid]; omega) hr0 (by omega) hs0 (by omega) env w
      with hd | hd
    · rw [hd]; exact Or.inl rfl
    rw [hd, hid]
    have hO : ecrecOut e.toNat v.toNat r.toNat s.toNat =
        match Secp256k1.Spec.recover e.toNat (v.toNat - 27) r.toNat s.toNat with
        | some (x, y) => Weierstrass.toBytes32 (hashWord x.val y.val % 2 ^ 160)
        | none => .empty := by rw [ecrecOut, if_pos hv]
    rw [hO]
    rcases Secp256k1.Spec.recover e.toNat (v.toNat - 27) r.toNat s.toNat with _ | ⟨x, y⟩
    · exact Or.inr ⟨_, _, empty_out env w hroom0, by rw [hemp, byteArray_readWithPadding_zero]⟩
    · right
      obtain ⟨mem, he, hrd⟩ := words_out env w
        (UInt256.ofNat (hashWord x.val y.val % 2 ^ 160)) (hpos hv) hroom
      refine ⟨wordsOut w, mem, ?_, ?_⟩
      · simp only [addrOf, FeProofs.Lib.Option_u256.Some_0, Fe.M.exec_bind, he, Fe.M.exec_pure]
      · have hm : (UInt256.ofNat w.memory.size).toNat = w.memory.size :=
          toNat_lit (by unfold UInt256.size at hroom; omega)
        simp only [wordsOut, hm, toNat32, hrd]
        exact (toBytes32_eq (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

end FeProofs.EcrecoverPrecompile
