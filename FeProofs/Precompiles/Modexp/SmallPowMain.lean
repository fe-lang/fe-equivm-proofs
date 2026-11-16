import FeProofs.Precompiles.Modexp.SmallPowLoops

/-!
# Modexp: `small_power<L>`

`small_power_ℓ_exec`, for `L = 1 … 4` (`ℓ` stands for `L`, see `limb_family`): for an odd
modulus `M > 1` of `L` limbs (the first `L` of `value`, the top one nonzero), a base `b` (the
first `L` limbs of `base`) and an exponent `e > 0`, `small_power_L` returns a fresh array of `L`
limbs at the end of memory, which holds `b ^ e mod M`; memory before it is unchanged.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

limb_family [1, 2, 3, 4]

/-- **The end of the walk**: out of Montgomery form, into a fresh array of `L` limbs. -/
theorem walk_exitℓ {x : Exponent} {e total top : ℕ} {w : World} (hx : ExpAt x e total top w.memory)
    (I : Env) (m : L4) (inv : Limb) (p : L4) (wd : UInt256) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * ℓ < UInt256.size) r0 r2 r3 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
    r18 r19 r20 r21 :
    (small_power_ℓ.loop.loop_1 x wd r0 ⟨toW m, inv.w⟩ r2 r3 (toW p) (UInt256.ofNat total) true r7 r8 r9
        r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21).exec I w =
      some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat ℓ⟩,
        { w with memory := storeL ℓ (w.memory ++ zeros (8 * ℓ)) w.memory.size (smul ℓ m inv p one4) })) := by
  have ht := hx.total_lt
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hal := try_new_zeroed_exec (n := ℓ) I w h0 hroom (by norm_num)
  have hq : ∀ k, k < ℓ → w.memory.size + 8 * k < UInt256.size := fun k hk => by omega
  rw [small_power_ℓ.loop.loop_1.eq_1]
  simp only [hx.total_eq, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ite_false, one4_w,
    smulℓ_eq, pure_bind, Fe.M.exec_bind, hal]
  simp only [ite_true, Lib.Option_MemArray_u64.Some_0]
  simp (disch := first | omega | norm_num) only [idx_fresh (sz := w.memory.size) (L := ℓ) (hroom := hroom), pure_bind,
    Fe.M.exec_bind, Fe.M.exec_pure, toW, store_exec, toNat_lit, decide_true, decide_false,
    Bool.false_eq_true, storeL, Nat.reduceLT, ↓reduceIte,
    Nat.reduceMul, Nat.add_zero]


/-- The walk from the top bit, then out of Montgomery form into a fresh array. -/
theorem walk_fullℓ {x : Exponent} {e total top : ℕ} {w : World} (hx : ExpAt x e total top w.memory)
    (I : Env) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ (64 * ℓ))
    (hcop : Nat.Coprime (2 ^ (64 * ℓ)) (nat4 m)) (t0 : L4) (b : ℕ)
    (h0r : MRep (2 ^ (64 * ℓ)) m t0 b) (width c : ℕ) (hw : 1 ≤ width ∧ width ≤ 7)
    (hc : c = 2 ^ (width - 1)) (he : e ≠ 0) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * ℓ < UInt256.size) r0 r3 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    r19 r20 r21 :
    ∃ p' : L4, MRep (2 ^ (64 * ℓ)) m p' (b ^ e) ∧
      (small_power_ℓ.loop.loop_1 x (UInt256.ofNat width) r0 ⟨toW m, inv.w⟩ (tabV (tbl ℓ m inv t0) c) r3
          (toW t0) (UInt256.ofNat top) false r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
          r21).exec I w =
        some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat ℓ⟩,
          { w with memory := storeL ℓ (w.memory ++ zeros (8 * ℓ)) w.memory.size (smul ℓ m inv p' one4) })) := by
  subst hc
  obtain ⟨p', r15', r16', r17', r18', r19', hp', hex⟩ := walkℓ hx I m inv hinv hm hcop t0 b h0r width
    hw he r0 r3 r7 r8 r9 r10 r11 r12 r13 r14 r20 r21 (total - top) top false t0 r15 r16 r17 r18 r19
    le_rfl hx.top_le hx.prefix_top
  exact ⟨p', hp', hex.trans (walk_exitℓ hx I m inv p' _ h0 hroom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)⟩

/-- **`small_power<L>` computes `b ^ e mod M`** into a fresh array of `L` limbs. -/
theorem small_power_ℓ_exec {x : Exponent} {e total top : ℕ} {base value : Lib.MemArray_u64}
    {bs vs : List Limb} {w : World} (I : Env) (hx : ExpAt x e total top w.memory) (he : e ≠ 0)
    (hb : ArrayAt base bs w.memory) (hbl : ℓ ≤ bs.length) (hv : ArrayAt value vs w.memory)
    (hvl : ℓ ≤ vs.length) (hodd : val (vs.take ℓ) % 2 = 1) (hM : 1 < val (vs.take ℓ))
    (hMtop : 2 ^ (64 * (ℓ - 1)) ≤ val (vs.take ℓ)) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * ℓ < UInt256.size) :
    ∃ out : List Limb, out.length = ℓ ∧ val out = val (bs.take ℓ) ^ e % val (vs.take ℓ) ∧
      (small_power_ℓ x base value).exec I w =
        some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat ℓ⟩,
          { w with memory := w.memory ++ limbBytes out })) := by
  have ht := hx.total_lt
  have htop := hx.top_le
  have hS : UInt256.size = 2 ^ 256 := rfl
  obtain ⟨m, hmdef⟩ : ∃ m, m = wideOf vs ℓ := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : Limb, a = vs[0]'(by omega) := ⟨_, rfl⟩
  have hnm : nat4 m = val (vs.take ℓ) := by rw [hmdef]; exact nat4_wideOf vs ℓ (by omega) hvl
  have hm0 : m.l0 = a := by
    simp [hmdef, hadef, wideOf, List.getElem?_eq_getElem (show 0 < vs.length by omega)]
  have hm64 : nat4 m < 2 ^ (64 * ℓ) := by
    rw [hnm]; have := val_lt (vs.take ℓ); rwa [List.length_take, Nat.min_eq_left hvl] at this
  have hinv : InvOk m.l0 (minv a) := by
    rw [hm0]; exact newton_inv a (by rw [← hm0, ← nat4_mod2, hnm]; exact hodd)
  have htop1 : 0 < (topLimb ℓ m).val :=
    topLimb_pos (by omega) m hm64 (by omega) (by rw [hnm]; exact hMtop)
  have hcop := coprime_R ℓ m (by rw [hnm]; exact hodd)
  obtain ⟨bw, hbwdef⟩ : ∃ bw, bw = wideOf bs ℓ := ⟨_, rfl⟩
  have hnb : nat4 bw = val (bs.take ℓ) := by rw [hbwdef]; exact nat4_wideOf bs ℓ (by omega) hbl
  have hbw : nat4 bw < 2 ^ (64 * ℓ) := by
    rw [hnb]; have := val_lt (bs.take ℓ); rwa [List.length_take, Nat.min_eq_left hbl] at this
  have hr2 := r2_spec ℓ (by omega) m (minv a) hinv hm64 (by rw [hnm]; exact hodd) (by rw [hnm]; exact hM)
    htop1
  have h0rep := mrep_base ℓ (by omega) m bw (r2 ℓ m (minv a)) (minv a) hinv hm64 hcop hbw hr2
  have hwb := ww_bounds (total - top)
  have hE64 : 2 ^ (ww (total - top) - 1) ≤ 64 := le_trans (Nat.pow_le_pow_right (by norm_num) (show ww (total - top) - 1 ≤ 6 by omega)) (by norm_num)
  have hld := load_exec hv.limbs (i := 0) (by omega) hv.small I
  rw [small_power_ℓ]
  simp only [index_ref_eq (a := value) (i := 0) (by rw [hv.len]; omega)
    (by have := hv.addr_lt (i := 0) (by omega); omega), pure_bind, Lib.Range_start_0_5]
  simp only [Fe.M.exec_bind, hld]
  rw [← hadef, newton_loopℓ x base value a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 5 0 a rfl,
    small_power_ℓ.loop.eq_1]
  have hwlt : total - top < 2 ^ 64 := by omega
  have hww1 : ww (total - top) - 1 < 255 := by omega
  simp only [has05_eq _ (show 5 < 2 ^ 256 by norm_num), show (0 ≤ 5 ∧ 5 < 5) = False from
      eq_false (by omega), decide_false, Bool.false_eq_true, ite_false, Fe.M.exec_bind,
    wide_of_exec hv (L := ℓ) (by omega) hvl I, wide_of_exec hb (L := ℓ) (by omega) hbl I, ← hmdef,
    ← hbwdef, sub0_minv, hx.total_eq, hx.top_eq, sub_lit (show total < 2 ^ 256 by omega) htop,
    window_width_eq _ hwlt, pure_bind, sub_lit (show ww (total - top) < 2 ^ 256 by omega) hwb.1,
    shl_one_lit hww1, downcast_usize_usize, w0_eq, tabV_zero (tbl ℓ m (minv a) (smul ℓ m (minv a) bw (r2 ℓ m (minv a)))),
    r2_ℓ_eq m (minv a) htop1, smulℓ_eq, checkIndex_ok (show 0 < 64 by norm_num) (by norm_num),
    toNat_lit (show 0 < 2 ^ 256 by norm_num)]
  have hE1 : 1 ≤ 2 ^ (ww (total - top) - 1) := Nat.one_le_two_pow
  have hw7 : 1 ≤ ww (total - top) ∧ ww (total - top) ≤ 7 := hwb
  simp only [tabV_set0, tabV_get0 ℓ m (minv a) _ (show 0 < 1 by norm_num),
    toNat_lit (show 1 < 2 ^ 256 by norm_num),
    toNat_lit (show 2 ^ (ww (total - top) - 1) < 2 ^ 256 by omega)]
  have hout : ∀ p' : L4, MRep (2 ^ (64 * ℓ)) m p' (nat4 bw ^ e) →
      val (limbsL ℓ (smul ℓ m (minv a) p' one4)) = val (bs.take ℓ) ^ e % val (vs.take ℓ) := by
    intro p' hp'
    have ho := mrep_out ℓ (by omega) m p' (minv a) _ hinv hm64 (by rw [hnm]; exact hM) hcop hp'
    have hlt' : nat4 (smul ℓ m (minv a) p' one4) < 2 ^ (64 * ℓ) := by
      rw [ho]; exact lt_trans (Nat.mod_lt _ (by omega)) hm64
    rw [val_limbsL (by omega) _ hlt', ho, hnb, hnm]
  by_cases hE : 1 < 2 ^ (ww (total - top) - 1)
  · simp only [hE, decide_true, ite_true, smulℓ_eq, pure_bind, Lib.Range_start_1]
    obtain ⟨r14', h8⟩ := table_loopℓ (fun r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
        r17 r18 r19 r20 r21 => small_power_ℓ.loop.loop_1 x (UInt256.ofNat (ww (total - top))) r0 r1 r2
        r3 r2[0]! (UInt256.ofNat top) false r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
      m (minv a) (smul ℓ m (minv a) bw (r2 ℓ m (minv a))) _ hE64 ((newton a)^[5] a).w default default
      default default ⟨(), ()⟩ (toW bw) (toW (r2 ℓ m (minv a)))
      (toW (smul ℓ m (minv a) bw (r2 ℓ m (minv a)))) (toW (smul ℓ m (minv a) bw (r2 ℓ m (minv a))))
      default default default default default default default (2 ^ (ww (total - top) - 1) - 1) 1
      default (by omega) le_rfl
    rw [h8]
    simp only [tabV_get0 ℓ m (minv a) _ (show 0 < 2 ^ (ww (total - top) - 1) by omega)]
    obtain ⟨p', hp', hex⟩ := walk_fullℓ hx I m (minv a) hinv hm64 hcop _ _ h0rep _ _ hw7 rfl he h0
      hroom ((newton a)^[5] a).w (toW (smul ℓ m (minv a) (smul ℓ m (minv a) bw (r2 ℓ m (minv a)))
        (smul ℓ m (minv a) bw (r2 ℓ m (minv a))))) default ⟨(), ()⟩ (toW bw) (toW (r2 ℓ m (minv a)))
      (toW (smul ℓ m (minv a) bw (r2 ℓ m (minv a)))) (toW (smul ℓ m (minv a) bw (r2 ℓ m (minv a))))
      ⟨(), UInt256.ofNat (2 ^ (ww (total - top) - 1))⟩ r14' default default default default default
      default default
    exact ⟨_, limbsL_length (by omega) _, hout p' hp', by rw [hex, storeL_eq ℓ (by omega)]⟩
  · simp only [hE, decide_false, Bool.false_eq_true, ite_false]
    obtain ⟨p', hp', hex⟩ := walk_fullℓ hx I m (minv a) hinv hm64 hcop _ _ h0rep _ 1 hw7 (by omega)
      he h0 hroom ((newton a)^[5] a).w default default ⟨(), ()⟩ (toW bw) (toW (r2 ℓ m (minv a)))
      default default default default default default default default default default default
    exact ⟨_, limbsL_length (by omega) _, hout p' hp', by rw [hex, storeL_eq ℓ (by omega)]⟩

end_limb_family

end FeProofs.Modexp
