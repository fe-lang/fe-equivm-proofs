import FeProofs.Precompiles.Modexp.Input

/-!
# Modexp: `Exponent::try_read`

`try_read_exec`: `Exponent::try_read(input, start, len)` reads the exponent `e`, the number of
`len` bytes at `start` of the bytes `d` the input buffer holds, into a fresh array of
`(len + 7) / 8` limbs at the end of memory, and returns an `Exponent` with `ExpAt` of `e`, its
`8 len` bits and its top bit.  The scan (`scan_loop`) counts down past the zero top limbs; the top
bit is then `64 (c - 1) + log2` of the last nonzero limb `c - 1` (`log2_val`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- The top bit of `e` from the most significant end of `total` bits, as `ExpAt` has it. -/
def topOf (e total : ℕ) : ℕ := if e = 0 then total else total - 1 - e.log2

theorem lz_limb (x : Limb) (hx : 0 < x.val) :
    IntTy.leadingZeros (.u 256) x.w = UInt256.ofNat (255 - x.val.log2) := by
  rw [leadingZeros_eq_clz, UInt256.clz, Limb.toNat_w, ite_eq_right (by omega)]

theorem limb_eq_zero_w (x : Limb) : (x.w = UInt256.ofNat 0) = (x = 0) := by
  rw [zero_w]; exact propext Limb.w_inj

/-- **The scan of `try_read`**, from `c` limbs whose higher ones are zero. -/
theorem scan_loop {w : World} {a : Lib.MemArray_u64} {ls : List Limb} (h : ArrayAt a ls w.memory)
    {total : ℕ} (htot : total < 2 ^ 64) (hv : val ls < 2 ^ total) (I : Env) :
    ∀ c, c ≤ ls.length → (∀ j (hj : j < ls.length), c ≤ j → ls[j] = 0) →
      (Exponent_try_read_MemBuffer.loop (UInt256.ofNat total) a (UInt256.ofNat c)).exec I w =
        some (.ok (.Some ⟨a, UInt256.ofNat (topOf (val ls) total), UInt256.ofNat total⟩, w))
  | 0, _, hz => by
    have h0 : val ls = 0 := by rw [val_take_of_zero ls 0 hz]; simp [val]
    rw [Exponent_try_read_MemBuffer.loop.eq_1]
    simp [topOf, h0]
  | c + 1, hc, hz => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hcl : c < ls.length := by omega
    have hb := h.addr_lt hcl
    have hs := h.small
    rw [Exponent_try_read_MemBuffer.loop.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), toNat_lit (show c + 1 < 2 ^ 256 by omega),
      show 0 < c + 1 by omega, decide_true, ite_true,
      checkedSub_lit (show c + 1 < 2 ^ 256 by omega) (show 1 ≤ c + 1 by omega), Nat.add_sub_cancel,
      pure_bind, Fe.M.exec_bind, index_ref_eq (a := a) (i := c) (by rw [h.len]; omega) (by omega),
      load_exec h.limbs hcl hs I, limb_eq_zero_w]
    by_cases h0 : ls[c] = 0
    · rw [show decide (ls[c] = 0) = true from decide_eq_true h0]
      simp only [ite_true]
      exact scan_loop h htot hv I c (by omega) (fun j hj hcj => by
        rcases Nat.lt_or_eq_of_le hcj with hlt | rfl
        · exact hz j hj hlt
        · exact h0)
    · obtain ⟨hV, hlog⟩ := log2_val ls c hcl (fun j hj hcj => hz j hj hcj) h0
      have hpos : 0 < ls[c].val := Nat.pos_of_ne_zero (fun e => h0 (Fin.ext e))
      have hl64 := log2_lt64 ls[c]
      have hlt : (val ls).log2 < total := (Nat.log2_lt hV).mpr hv
      rw [show decide (ls[c] = 0) = false from decide_eq_false h0]
      simp only [Bool.false_eq_true, ite_false, Fe.M.exec_bind, load_exec h.limbs hcl hs I,
        show (UInt256.ofNat (c + 1) = UInt256.ofNat 0) = False from
          eq_false (ofNat_ne_ofNat_zero (by omega) (by omega)), decide_false]
      rw [lz_limb _ hpos]
      simp only [checkedSub_lit (show 255 < 2 ^ 256 by norm_num)
          (show 255 - ls[c].val.log2 ≤ 255 by omega),
        show 255 - (255 - ls[c].val.log2) = ls[c].val.log2 by omega, downcast_u256_usize,
        checkedSub_lit (show total < 2 ^ 256 by omega) (show 1 ≤ total by omega),
        checkedMul_small (show c < 2 ^ 256 by omega) (show 64 < 2 ^ 256 by norm_num)
          (show c * 64 < 2 ^ 256 by omega),
        checkedAdd_small (show c * 64 + ls[c].val.log2 < 2 ^ 256 by omega),
        checkedSub_lit (show total - 1 < 2 ^ 256 by omega)
          (show c * 64 + ls[c].val.log2 ≤ total - 1 by omega), Fe.M.exec_pure]
      rw [topOf, ite_eq_right hV, hlog, show 64 * c = c * 64 by ring]

/-- **`Exponent::try_read(input, start, len)`**: the exponent of `len` bytes at `start`, its
    limbs in a fresh array at the end of memory. -/
theorem try_read_exec {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {start len : ℕ} (hoff : start + len < 2 ^ 64) (hlen : 8 * len < 2 ^ 64)
    (h0 : 0 < w.memory.size) (hroom : w.memory.size + 8 * ((len + 7) / 8) < UInt256.size) (I : Env) :
    ∃ x : Exponent, ExpAt x (beAt d start len) (8 * len) (topOf (beAt d start len) (8 * len))
        (w.memory ++ limbBytes (limbsOf (beAt d start len) ((len + 7) / 8))) ∧
      (Exponent_try_read_MemBuffer b (UInt256.ofNat start) (UInt256.ofNat len)).exec I w =
        some (.ok (.Some x,
          { w with memory := w.memory ++ limbBytes (limbsOf (beAt d start len) ((len + 7) / 8)) })) := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  obtain ⟨N, hN⟩ : ∃ N, N = beAt d start len := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (len + 7) / 8 := ⟨_, rfl⟩
  have hNlt : N < 2 ^ (8 * len) := hN ▸ beAt_lt d start len
  have hval : val (limbsOf N n) = N := by
    rw [val_limbsOf, Nat.mod_eq_of_lt (lt_of_lt_of_le hNlt (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
  have hA : ArrayAt ⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩ (limbsOf N n)
      (w.memory ++ limbBytes (limbsOf N n)) := by
    refine ⟨by rw [limbsOf_length]; exact toNat_lit (by omega), ?_, by
      rw [ByteArray.size_append, limbBytes_size, limbsOf_length]; omega⟩
    rw [toNat_lit (show w.memory.size < 2 ^ 256 by omega)]
    exact limbsAt_limbBytes _ _
  have hl := input_limbs_exec h (count := n) hoff h0 (by omega) (by omega) I
  have hsc := scan_loop (w := { w with memory := w.memory ++ limbBytes (limbsOf N n) }) hA
    (total := 8 * len) hlen (by rw [hval]; exact hNlt) I n (by simp) (fun j hj hnj => by simp at hj; omega)
  rw [hval] at hsc
  rw [← hN, ← hn]
  refine ⟨⟨⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩, UInt256.ofNat (topOf N (8 * len)),
    UInt256.ofNat (8 * len)⟩, ⟨⟨limbsOf N n, hA, hval, by rw [limbsOf_length]; omega⟩, rfl, rfl, hlen,
    hNlt, rfl⟩, ?_⟩
  simp only [Exponent_try_read_MemBuffer, checkedMul_small (show len < 2 ^ 256 by omega)
      (show 8 < 2 ^ 256 by norm_num) (show len * 8 < 2 ^ 256 by omega),
    checkedAdd_small (show len + 7 < 2 ^ 256 by omega),
    checkedDiv_lit (show len + 7 < 2 ^ 256 by omega) (show 8 < 2 ^ 256 by norm_num) (by norm_num),
    pure_bind, Fe.M.exec_bind, ← hn, ← hN, hl, ite_true,
    Lib.Option_MemArray_u64.Some_0, Lib.MemArray_len_u64, show len * 8 = 8 * len by ring]
  exact hsc

end FeProofs.Modexp
