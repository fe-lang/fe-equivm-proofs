import FeProofs.Precompiles.Modexp.SmallPow1

/-!
# Modexp: `small_power<1>`

`small_power_1_exec`: for an odd modulus `M > 1` of one limb (limb 0 of `value`), a base `b`
(limb 0 of `base`) and an exponent `e > 0`, `small_power_1` returns a fresh array of one limb at
the end of memory, which holds `b ^ e mod M`; memory before it is unchanged.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- The walk from the top bit, then out of Montgomery form into a fresh array. -/
theorem walk_full1 {x : Exponent} {e total top : ℕ} {w : World} (hx : ExpAt x e total top w.memory)
    (I : Env) (m : L4) (inv : Limb) (hinv : InvOk m.l0 inv) (hm : nat4 m < 2 ^ (64 * 1))
    (hcop : Nat.Coprime (2 ^ (64 * 1)) (nat4 m)) (t0 : L4) (b : ℕ)
    (h0r : MRep (2 ^ (64 * 1)) m t0 b) (width c : ℕ) (hw : 1 ≤ width ∧ width ≤ 7)
    (hc : c = 2 ^ (width - 1)) (he : e ≠ 0) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 < UInt256.size) r0 r3 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
    r19 r20 r21 :
    ∃ p' : L4, MRep (2 ^ (64 * 1)) m p' (b ^ e) ∧
      (small_power_1.b1.b12 x (UInt256.ofNat width) r0 ⟨toW m, inv.w⟩ (tabV (tbl 1 m inv t0) c) r3
          (toW t0) (UInt256.ofNat top) false r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
          r21).exec I w =
        some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat 1⟩,
          { w with memory := store8 (w.memory ++ zeros 8) w.memory.size (smul 1 m inv p' one4).l0 })) := by
  subst hc
  obtain ⟨p', r15', r16', r17', r18', r19', hp', hex⟩ := walk1 hx I m inv hinv hm hcop t0 b h0r width
    hw he r0 r3 r7 r8 r9 r10 r11 r12 r13 r14 r20 r21 (total - top) top false t0 r15 r16 r17 r18 r19
    le_rfl hx.top_le hx.prefix_top
  exact ⟨p', hp', hex.trans (walk_exit1 hx I m inv p' _ h0 hroom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)⟩

theorem sub0_minv (a : Limb) :
    IntTy.subW (.u 64) (UInt256.ofNat 0) ((newton a)^[5] a).w = (minv a).w := subW64_eq 0 _

theorem tabV_set0 (L : ℕ) (m : L4) (inv : Limb) (t0 : L4) :
    (tabV (tbl L m inv t0) 0).set! 0 (toW t0) = tabV (tbl L m inv t0) 1 := tabV_set _ 0

theorem tabV_get0 (L : ℕ) (m : L4) (inv : Limb) (t0 : L4) {c : ℕ} (hc : 0 < c) :
    (tabV (tbl L m inv t0) c)[0]! = toW t0 := tabV_get _ hc (by omega)

theorem w0_eq : Wide.mk (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) = W0 := rfl

theorem small_power_1_exec {x : Exponent} {e total top : ℕ} {base value : Lib.MemArray_u64}
    {bs vs : List Limb} {w : World} (I : Env) (hx : ExpAt x e total top w.memory) (he : e ≠ 0)
    (hb : ArrayAt base bs w.memory) (hbl : 1 ≤ bs.length) (hv : ArrayAt value vs w.memory)
    (hvl : 1 ≤ vs.length) (hodd : val (vs.take 1) % 2 = 1) (hM : 1 < val (vs.take 1))
    (h0 : 0 < w.memory.size) (hroom : w.memory.size + 8 < UInt256.size) :
    ∃ out : Limb, out.val = val (bs.take 1) ^ e % val (vs.take 1) ∧
      (small_power_1 x base value).exec I w =
        some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat 1⟩,
          { w with memory := store8 (w.memory ++ zeros 8) w.memory.size out })) := by
  have ht := hx.total_lt
  have htop := hx.top_le
  have hS : UInt256.size = 2 ^ 256 := rfl
  obtain ⟨m, hmdef⟩ : ∃ m, m = wideOf vs 1 := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : Limb, a = vs[0]'(by omega) := ⟨_, rfl⟩
  have hnm : nat4 m = val (vs.take 1) := by rw [hmdef]; exact nat4_wideOf vs 1 (by omega) hvl
  have hm0 : m.l0 = a := by
    simp [hmdef, hadef, wideOf, List.getElem?_eq_getElem (show 0 < vs.length by omega)]
  have hlt : nat4 m < 2 ^ 64 := by
    rw [hnm]; have := val_lt (vs.take 1); rwa [List.length_take, Nat.min_eq_left hvl] at this
  have hma : nat4 m = a.val := by rw [nat4_one hlt, hm0]
  have hinv : InvOk m.l0 (minv a) := by rw [hm0]; exact newton_inv a (by rw [← hma, hnm]; exact hodd)
  have hm64 : nat4 m < 2 ^ (64 * 1) := by rw [hma]; exact a.isLt
  have hcop := coprime_R 1 m (by rw [hnm]; exact hodd)
  obtain ⟨bw, hbwdef⟩ : ∃ bw, bw = wideOf bs 1 := ⟨_, rfl⟩
  have hnb : nat4 bw = val (bs.take 1) := by rw [hbwdef]; exact nat4_wideOf bs 1 (by omega) hbl
  have hbw : nat4 bw < 2 ^ (64 * 1) := by
    rw [hnb]; exact lt_of_lt_of_le (val_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
  have hr2 := r2_spec 1 (by omega) m (minv a) hinv hm64 (by rw [hnm]; exact hodd) (by rw [hnm]; exact hM)
    (by simp only [topLimb, if_true]; rw [hm0, ← hma, hnm]; omega)
  have h0rep := mrep_base 1 (by omega) m bw (r2 1 m (minv a)) (minv a) hinv hm64 hcop hbw hr2
  have hwb := ww_bounds (total - top)
  have hE64 : 2 ^ (ww (total - top) - 1) ≤ 64 := le_trans (Nat.pow_le_pow_right (by norm_num) (show ww (total - top) - 1 ≤ 6 by omega)) (by norm_num)
  have hld := load_exec hv.limbs (i := 0) (by omega) hv.small I
  rw [small_power_1]
  simp only [index_ref_eq (a := value) (i := 0) (by rw [hv.len]; omega)
    (by have := hv.addr_lt (i := 0) (by omega); omega), pure_bind, Lib.Range_start_0_5]
  simp only [Fe.M.exec_bind, hld]
  rw [← hadef, newton_loop1 x base value a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 5 0 a rfl,
    small_power_1.b1.eq_1]
  have hwlt : total - top < 2 ^ 64 := by omega
  have hww1 : ww (total - top) - 1 < 255 := by omega
  have htop1 : 0 < (topLimb 1 m).val := by simp only [topLimb, if_true]; rw [hm0, ← hma, hnm]; omega
  simp only [has05_eq _ (show 5 < 2 ^ 256 by norm_num), show (0 ≤ 5 ∧ 5 < 5) = False from
      eq_false (by omega), decide_false, Bool.false_eq_true, if_false, Fe.M.exec_bind,
    wide_of_exec hv (L := 1) (by omega) hvl I, wide_of_exec hb (L := 1) (by omega) hbl I, ← hmdef,
    ← hbwdef, sub0_minv, hx.total_eq, hx.top_eq, sub_lit (show total < 2 ^ 256 by omega) htop,
    window_width_eq _ hwlt, pure_bind, sub_lit (show ww (total - top) < 2 ^ 256 by omega) hwb.1,
    shl_one_lit hww1, downcast_usize_usize, w0_eq, tabV_zero (tbl 1 m (minv a) (smul 1 m (minv a) bw (r2 1 m (minv a)))),
    r2_1_eq m (minv a) htop1, smul1_eq, checkIndex_ok (show 0 < 64 by norm_num) (by norm_num),
    toNat_lit (show 0 < 2 ^ 256 by norm_num)]
  have hE1 : 1 ≤ 2 ^ (ww (total - top) - 1) := Nat.one_le_two_pow
  have hw7 : 1 ≤ ww (total - top) ∧ ww (total - top) ≤ 7 := hwb
  simp only [tabV_set0, tabV_get0 1 m (minv a) _ (show 0 < 1 by norm_num),
    toNat_lit (show 1 < 2 ^ 256 by norm_num),
    toNat_lit (show 2 ^ (ww (total - top) - 1) < 2 ^ 256 by omega)]
  have hout : ∀ p' : L4, MRep (2 ^ (64 * 1)) m p' (nat4 bw ^ e) →
      (smul 1 m (minv a) p' one4).l0.val = val (bs.take 1) ^ e % val (vs.take 1) := by
    intro p' hp'
    have ho := mrep_out 1 (by omega) m p' (minv a) _ hinv hm64 (by rw [hnm]; exact hM) hcop hp'
    have hlt' : nat4 (smul 1 m (minv a) p' one4) < 2 ^ 64 := by
      rw [ho]; exact lt_trans (Nat.mod_lt _ (by omega)) hlt
    rw [← nat4_one hlt', ho, hnb, hnm]
  by_cases hE : 1 < 2 ^ (ww (total - top) - 1)
  · simp only [hE, decide_true, if_true, smul1_eq, pure_bind, Lib.Range_start_1]
    obtain ⟨r14', h8⟩ := table_loop1 (fun r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
        r17 r18 r19 r20 r21 => small_power_1.b1.b12 x (UInt256.ofNat (ww (total - top))) r0 r1 r2
        r3 r2[0]! (UInt256.ofNat top) false r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21)
      m (minv a) (smul 1 m (minv a) bw (r2 1 m (minv a))) _ hE64 ((newton a)^[5] a).w default default
      default default ⟨(), ()⟩ (toW bw) (toW (r2 1 m (minv a)))
      (toW (smul 1 m (minv a) bw (r2 1 m (minv a)))) (toW (smul 1 m (minv a) bw (r2 1 m (minv a))))
      default default default default default default default (2 ^ (ww (total - top) - 1) - 1) 1
      default (by omega) le_rfl
    rw [h8]
    simp only [tabV_get0 1 m (minv a) _ (show 0 < 2 ^ (ww (total - top) - 1) by omega)]
    obtain ⟨p', hp', hex⟩ := walk_full1 hx I m (minv a) hinv hm64 hcop _ _ h0rep _ _ hw7 rfl he h0
      hroom ((newton a)^[5] a).w (toW (smul 1 m (minv a) (smul 1 m (minv a) bw (r2 1 m (minv a)))
        (smul 1 m (minv a) bw (r2 1 m (minv a))))) default ⟨(), ()⟩ (toW bw) (toW (r2 1 m (minv a)))
      (toW (smul 1 m (minv a) bw (r2 1 m (minv a)))) (toW (smul 1 m (minv a) bw (r2 1 m (minv a))))
      ⟨(), UInt256.ofNat (2 ^ (ww (total - top) - 1))⟩ r14' default default default default default
      default default
    exact ⟨_, hout p' hp', hex⟩
  · simp only [hE, decide_false, Bool.false_eq_true, if_false]
    obtain ⟨p', hp', hex⟩ := walk_full1 hx I m (minv a) hinv hm64 hcop _ _ h0rep _ 1 hw7 (by omega)
      he h0 hroom ((newton a)^[5] a).w default default ⟨(), ()⟩ (toW bw) (toW (r2 1 m (minv a)))
      default default default default default default default default default default default
    exact ⟨_, hout p' hp', hex⟩

end FeProofs.Modexp
