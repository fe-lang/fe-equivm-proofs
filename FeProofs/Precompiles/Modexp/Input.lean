import FeProofs.Precompiles.Modexp.Exponent
import FeProofs.Precompiles.Field.Checked
import FeProofs.Precompiles.Modexp.SmallPowMem
import Ethereum.Modexp.Spec

/-!
# Modexp: reading the numbers from the input

The base, exponent and modulus are big-endian numbers of given lengths at given offsets of the
call data, read as if extended with zeros: `beAt d off len` of the bytes `d` a buffer holds
(`field_eq`: this is EVMLean's `Ethereum.Modexp.field`).  Here:

- `beAt_digit`: byte `p` of that number, from the least significant end;
- `input_byte_exec`: `input_byte(input, j)`, the byte at `j` or zero past the end;
- `input_limb_exec`: `input_limb(input, off, len, i)`, limb `i` of the number, by one lane read
  when its eight bytes lie inside the input and by a loop over its bytes otherwise.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-- **EVMLean's reading of a field of the call data** is `beAt`. -/
theorem field_eq (d : ByteArray) (off n : ℕ) : Ethereum.Modexp.field d off n = beAt d off n :=
  readWithPadding_be d off n

theorem pow_8_eq (p : ℕ) : (2 : ℕ) ^ (8 * (p + 1)) = 2 ^ (8 * p) * 256 := by
  rw [show 8 * (p + 1) = 8 * p + 8 by ring, pow_add]; norm_num

/-- **Byte `p` of the number** of `len` bytes at `off`, from its least significant end. -/
theorem beAt_digit (d : ByteArray) (off len p : ℕ) :
    beAt d off len / 2 ^ (8 * p) % 256 = if p < len then byteAt d (off + len - 1 - p) else 0 := by
  split_ifs with hp
  · have e1 := beAt_add d off (len - (p + 1)) (p + 1)
    have e2 := beAt_add d (off + (len - (p + 1))) 1 p
    rw [Nat.sub_add_cancel hp] at e1
    rw [Nat.add_comm 1 p] at e2
    have hy := beAt_lt d (off + (len - (p + 1)) + 1) p
    have hb : beAt d (off + (len - (p + 1))) 1 = byteAt d (off + len - 1 - p) := by
      simp only [beAt, Nat.zero_mul, Nat.zero_add, Nat.add_zero]; congr 1; omega
    have hbl := byteAt_lt d (off + len - 1 - p)
    rw [e1, e2, hb, pow_8_eq p]
    rw [show beAt d off (len - (p + 1)) * (2 ^ (8 * p) * 256) +
        (byteAt d (off + len - 1 - p) * 2 ^ (8 * p) + beAt d (off + (len - (p + 1)) + 1) p) =
        2 ^ (8 * p) * (beAt d off (len - (p + 1)) * 256 + byteAt d (off + len - 1 - p)) +
          beAt d (off + (len - (p + 1)) + 1) p by ring,
      Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hy, Nat.add_zero, Nat.mul_comm,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hbl]
  · have h := beAt_lt d off len
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **`input_byte(input, j)`**: the byte at `j`, zero past the end. -/
theorem input_byte_exec {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {j : ℕ} (hj : j < 2 ^ 256) (I : Env) :
    (input_byte_MemBuffer b (UInt256.ofNat j)).exec I w =
      some (.ok (UInt256.ofNat (byteAt d j), w)) := by
  by_cases hd : j < d.size
  · simp [input_byte_MemBuffer, len_exec, toNat_lit hj, h.len, hd, byte_exec h hd]
  · simp [input_byte_MemBuffer, len_exec, toNat_lit hj, h.len, hd, byteAt_of_ge (not_lt.mp hd)]

theorem shl8_lit {r : ℕ} (hr : r < 2 ^ 56) :
    IntTy.shl (.u 64) (UInt256.ofNat r) (UInt256.ofNat 8) = UInt256.ofNat (r * 256) := by
  simp only [IntTy.shl, IntTy.val, IntTy.wrap, toNat_lit (show r < 2 ^ 256 by omega),
    toNat_lit (show 8 < 2 ^ 256 by norm_num), show ¬ 256 ≤ 8 by omega, if_false]
  congr 1
  rw [show ((r : ℤ) * 2 ^ 8 % 2 ^ 64) = ((r * 256 : ℕ) : ℤ) by
    rw [Int.emod_eq_of_lt (by positivity) (by push_cast; omega)]; push_cast; ring, Int.toNat_natCast]

theorem lor_byte {a c : ℕ} (ha : a < 2 ^ 56) (hc : c < 256) :
    UInt256.ofNat (a * 256) ||| UInt256.ofNat c = UInt256.ofNat (a * 256 + c) := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, toNat_lit (show a * 256 < 2 ^ 256 by omega),
    toNat_lit (show c < 2 ^ 256 by omega),
    toNat_lit (show a * 256 + c < 2 ^ 256 by omega), show a * 256 = 2 ^ 8 * a by ring,
    ← Nat.two_pow_add_eq_or_of_lt (show c < 2 ^ 8 by omega)]

/-- The bytes `[k, 8)` of limb `i` of `N`, as the byte loop of `input_limb` has gathered them. -/
def partLimb (N i k : ℕ) : ℕ := N / 2 ^ (8 * (8 * i + k)) % 2 ^ (8 * (8 - k))

theorem partLimb_step (N i k : ℕ) (hk : k < 8) :
    partLimb N i (k + 1) * 256 + N / 2 ^ (8 * (8 * i + k)) % 256 = partLimb N i k := by
  unfold partLimb
  rw [show 8 * (8 * i + (k + 1)) = 8 * (8 * i + k) + 8 by ring, pow_add, ← Nat.div_div_eq_div_mul,
    show 8 * (8 - k) = 8 + 8 * (8 - (k + 1)) by omega, pow_add, Nat.mod_mul]
  norm_num; ring

theorem partLimb_lt (N i k : ℕ) : partLimb N i k < 2 ^ (8 * (8 - k)) :=
  Nat.mod_lt _ (by positivity)

/-- The byte loop of `input_limb`, from byte `k` down. -/
theorem byte_loop {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {off len i : ℕ} (hoff : off + len < 2 ^ 64) (hi : 8 * i < len) (I : Env) :
    ∀ k, k ≤ 8 →
      (input_limb_MemBuffer.b5 b (UInt256.ofNat off) (UInt256.ofNat len) (UInt256.ofNat i)
          (UInt256.ofNat (partLimb (beAt d off len) i k)) (UInt256.ofNat k)).exec I w =
        some (.ok (UInt256.ofNat (partLimb (beAt d off len) i 0), w))
  | 0, _ => by
    rw [input_limb_MemBuffer.b5.eq_1]
    simp
  | k + 1, hk => by
    have hp := partLimb_lt (beAt d off len) i (k + 1)
    have hp56 : partLimb (beAt d off len) i (k + 1) < 2 ^ 56 :=
      lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hdig := beAt_digit d off len (8 * i + k)
    have hstep := partLimb_step (beAt d off len) i k (by omega)
    rw [input_limb_MemBuffer.b5.eq_1]
    simp only [toNat_lit (show 0 < 2 ^ 256 by norm_num), toNat_lit (show k + 1 < 2 ^ 256 by omega),
      show 0 < k + 1 by omega, decide_true, if_true,
      ofNat_sub_ofNat (show k + 1 < UInt256.size by unfold UInt256.size; omega) (show 1 ≤ k + 1 by omega),
      Nat.add_sub_cancel, ofNat_mul_ofNat (show i < UInt256.size by unfold UInt256.size; omega)
        (show 8 < UInt256.size by unfold UInt256.size; omega)
        (show i * 8 < UInt256.size by unfold UInt256.size; omega),
      ofNat_add_ofNat (show i * 8 + k < UInt256.size by unfold UInt256.size; omega), shl8_lit hp56,
      toNat_lit (show i * 8 + k < 2 ^ 256 by omega), toNat_lit (show len < 2 ^ 256 by omega)]
    by_cases hpos : i * 8 + k < len
    · rw [if_pos (show 8 * i + k < len by omega)] at hdig
      simp only [hpos, decide_true, if_true,
        ofNat_add_ofNat (show off + len < UInt256.size by unfold UInt256.size; omega),
        ofNat_sub_ofNat (show off + len < UInt256.size by unfold UInt256.size; omega)
          (show 1 ≤ off + len by omega),
        ofNat_sub_ofNat (show off + len - 1 < UInt256.size by unfold UInt256.size; omega)
          (show i * 8 + k ≤ off + len - 1 by omega), Fe.M.exec_bind,
        input_byte_exec h (show off + len - 1 - (i * 8 + k) < 2 ^ 256 by omega),
        lor_byte hp56 (byteAt_lt _ _)]
      rw [show off + len - 1 - (i * 8 + k) = off + len - 1 - (8 * i + k) by ring_nf, ← hdig, hstep]
      exact byte_loop h hoff hi I k (by omega)
    · rw [if_neg (show ¬ 8 * i + k < len by omega)] at hdig
      simp only [hpos, decide_false, Bool.false_eq_true, if_false]
      rw [show partLimb (beAt d off len) i (k + 1) * 256 = partLimb (beAt d off len) i k by
        rw [← hstep, hdig]; simp]
      exact byte_loop h hoff hi I k (by omega)

/-- Limb `i` of the number `N`. -/
def limbAt (N i : ℕ) : Limb := ⟨N / 2 ^ (64 * i) % 2 ^ 64, Nat.mod_lt _ (by norm_num)⟩

theorem partLimb_zero (N i : ℕ) : partLimb N i 0 = (limbAt N i).val := by
  simp only [partLimb, limbAt, Nat.add_zero, Nat.sub_zero]
  rw [show 8 * (8 * i) = 64 * i by ring]

/-- Eight bytes inside the number are its limb. -/
theorem lane_limb (d : ByteArray) {off len i : ℕ} (hi : 8 * i + 8 ≤ len) :
    beAt d (off + len - 8 * i - 8) 8 = (limbAt (beAt d off len) i).val := by
  have e1 := beAt_add d off (len - (8 * i + 8)) (8 * i + 8)
  have e2 := beAt_add d (off + (len - (8 * i + 8))) 8 (8 * i)
  rw [Nat.sub_add_cancel hi] at e1
  rw [Nat.add_comm 8 (8 * i)] at e2
  have hy := beAt_lt d (off + (len - (8 * i + 8)) + 8) (8 * i)
  have hx := beAt_lt d (off + (len - (8 * i + 8))) 8
  rw [show off + len - 8 * i - 8 = off + (len - (8 * i + 8)) by omega]
  simp only [limbAt]
  rw [e1, e2, show 8 * (8 * i) = 64 * i by ring, show 8 * (8 * i + 8) = 64 * i + 64 by ring, pow_add,
    show beAt d off (len - (8 * i + 8)) * (2 ^ (64 * i) * 2 ^ 64) +
        (beAt d (off + (len - (8 * i + 8))) 8 * 2 ^ (64 * i) +
          beAt d (off + (len - (8 * i + 8)) + 8) (8 * i)) =
      2 ^ (64 * i) * (beAt d off (len - (8 * i + 8)) * 2 ^ 64 + beAt d (off + (len - (8 * i + 8))) 8) +
        beAt d (off + (len - (8 * i + 8)) + 8) (8 * i) by ring,
    Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (by rw [show 64 * i = 8 * (8 * i) by ring]; exact hy)]
  have hx' : beAt d (off + (len - (8 * i + 8))) 8 < 2 ^ 64 := by simpa using hx
  generalize beAt d (off + (len - (8 * i + 8))) 8 = B at hx' ⊢
  generalize beAt d off (len - (8 * i + 8)) = A
  simp only [Nat.add_zero]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx']

/-- **`input_limb(input, off, len, i)`**, `8 i < len`: limb `i` of the number of `len` bytes at
    `off`. -/
theorem input_limb_exec {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {off len i : ℕ} (hoff : off + len < 2 ^ 64) (hi : 8 * i < len) (I : Env) :
    (input_limb_MemBuffer b (UInt256.ofNat off) (UInt256.ofNat len) (UInt256.ofNat i)).exec I w =
      some (.ok ((limbAt (beAt d off len) i).w, w)) := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hloop := byte_loop h hoff hi I 8 le_rfl
  rw [partLimb_zero] at hloop
  have h8 : partLimb (beAt d off len) i 8 = 0 := by simp [partLimb, Nat.mod_one]
  rw [h8] at hloop
  simp only [input_limb_MemBuffer, ofNat_add_ofNat (show off + len < UInt256.size by omega),
    ofNat_mul_ofNat (show i < UInt256.size by omega) (show 8 < UInt256.size by omega)
      (show i * 8 < UInt256.size by omega),
    ofNat_sub_ofNat (show off + len < UInt256.size by omega) (show i * 8 ≤ off + len by omega),
    ofNat_add_ofNat (show i * 8 + 8 < UInt256.size by omega),
    toNat_lit (show i * 8 + 8 < 2 ^ 256 by omega), toNat_lit (show len < 2 ^ 256 by omega)]
  by_cases hf : i * 8 + 8 ≤ len
  · simp only [hf, decide_true, if_true, Fe.M.exec_bind, len_exec, h.len,
      toNat_lit (show off + len - i * 8 < 2 ^ 256 by omega)]
    by_cases hd : off + len - i * 8 ≤ d.size
    · simp only [hd, decide_true, if_true,
        ofNat_sub_ofNat (show off + len - i * 8 < UInt256.size by omega) (show 8 ≤ off + len - i * 8 by omega)]
      rw [Fe.M.exec_bind, show off + len - i * 8 - 8 = off + len - 8 * i - 8 by omega,
        lane_exec h (j := off + len - 8 * i - 8) (by omega)]
      simp only [Fe.M.exec_pure]
      rw [swap_swap_beAt, lane_limb d (show 8 * i + 8 ≤ len by omega)]
      rfl
    · simp only [hd, decide_false, Bool.false_eq_true, if_false]
      exact hloop
  · simp only [hf, decide_false, Bool.false_eq_true, if_false]
    exact hloop

/-! ## The limbs of a number -/

theorem limbsOf_get (N n k : ℕ) (hk : k < n) :
    (limbsOf N n)[k]'(by simpa using hk) = limbAt N k :=
  Fin.ext (limbsOf_getElem N n k _)

/-- Past the limbs that hold `N`, its limbs are zero. -/
theorem limbsOf_take (N n m : ℕ) (hN : N < 2 ^ (64 * m)) (hm : m ≤ n) :
    limbsOf N n = (limbsOf N n).take m ++ List.replicate (n - m) 0 := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  by_cases hj : j < m
  · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
    apply Fin.ext
    rw [limbsOf_getElem, Nat.div_eq_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.zero_mod]
    rfl

theorem take_succ_limbsOf (N n k : ℕ) (hk : k < n) :
    (limbsOf N n).take (k + 1) = (limbsOf N n).take k ++ [limbAt N k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk), limbsOf_get N n k hk]
  rfl

theorem has0_eq' (N : ℕ) (hN : N < 2 ^ 256) {k : ℕ} (hk : k < 2 ^ 256) :
    Lib.Range_has_0 ⟨(), UInt256.ofNat N⟩ (UInt256.ofNat k) = pure (decide (0 ≤ k ∧ k < N)) := by
  simp only [Lib.Range_has_0, range_has_eq (lo := 0) hk (by norm_num) hN, bind_pure]

/-- The memory of `input_limbs` after `k` of its `count` limbs. -/
def limbsMem (mem : ByteArray) (N count k : ℕ) : ByteArray :=
  mem ++ limbBytes ((limbsOf N count).take k) ++ zeros (8 * (count - k))

theorem limbsMem_store (mem : ByteArray) (N count k : ℕ) (hk : k < count) :
    store8 (limbsMem mem N count k) (mem.size + 8 * k) (limbAt N k) = limbsMem mem N count (k + 1) := by
  rw [limbsMem, show 8 * (count - k) = 8 * (count - (k + 1)) + 8 by omega,
    store8_zeros _ _ _ _ (by simp [ByteArray.size_append, Nat.min_eq_left hk.le]), limbsMem,
    take_succ_limbsOf N count k hk, limbBytes_append, ByteArray.append_assoc, ByteArray.append_assoc,
    ByteArray.append_assoc]
  simp only [limbBytes, ByteArray.append_empty, ByteArray.append_assoc]

theorem limbsMem_holds {b : Lib.MemBuffer} {d mem : ByteArray} (h : Holds b d mem) (N count k : ℕ)
    (hk : k ≤ count) (hroom : mem.size + 8 * count < UInt256.size) :
    Holds b d (limbsMem mem N count k) := by
  rw [limbsMem, ByteArray.append_assoc]
  exact h.append _ (by simp [ByteArray.size_append, Nat.min_eq_left hk]; omega)

/-- The loop of `input_limbs`, from limb `k` to `R`. -/
theorem limbs_loop {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {off len count R : ℕ} (hoff : off + len < 2 ^ 64) (hR : R ≤ (len + 7) / 8) (hRc : R ≤ count)
    (hroom : w.memory.size + 8 * count < UInt256.size) (I : Env) :
    ∀ n k, k + n = R →
      (input_limbs_MemBuffer.b6 b (UInt256.ofNat off) (UInt256.ofNat len)
          ⟨UInt256.ofNat w.memory.size, UInt256.ofNat count⟩ ⟨(), UInt256.ofNat R⟩
          (UInt256.ofNat k)).exec I { w with memory := limbsMem w.memory (beAt d off len) count k } =
        some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat count⟩,
          { w with memory := limbsMem w.memory (beAt d off len) count R }))
  | 0, k, hk => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    rw [show k = R by omega, input_limbs_MemBuffer.b6.eq_1]
    simp [has0_eq' R (by omega) (show R < 2 ^ 256 by omega)]
  | n + 1, k, hk => by
    have hS : UInt256.size = 2 ^ 256 := rfl
    have hH := limbsMem_holds h (beAt d off len) count k (by omega) hroom
    have hl := input_limb_exec (w := { w with memory := limbsMem w.memory (beAt d off len) count k })
      hH hoff (i := k) (by omega) I
    rw [input_limbs_MemBuffer.b6.eq_1]
    simp only [has0_eq' R (by omega) (show k < 2 ^ 256 by omega), show (0 ≤ k ∧ k < R) = True from
      eq_true (by omega), decide_true, if_true, Lib.Range_at_0, Lib.Range_next_0,
      next_eq (show k + 1 < 2 ^ 256 by omega), pure_bind, Fe.M.exec_bind, hl,
      idx_fresh (show k < count by omega) hroom,
      store_exec (show w.memory.size + 8 * k < UInt256.size by omega), limbsMem_store _ _ _ _
        (show k < count by omega)]
    exact limbs_loop h hoff hR hRc hroom I n (k + 1) (by omega)

/-- **`input_limbs(input, off, len, count)`**: a fresh array of `count` limbs at the end of memory,
    the first `count` limbs of the number of `len` bytes at `off`. -/
theorem input_limbs_exec {b : Lib.MemBuffer} {d : ByteArray} {w : World} (h : Holds b d w.memory)
    {off len count : ℕ} (hoff : off + len < 2 ^ 64) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * count < UInt256.size) (hc : 8 * count < 2 ^ 64) (I : Env) :
    (input_limbs_MemBuffer b (UInt256.ofNat off) (UInt256.ofNat len) (UInt256.ofNat count)).exec I w =
      some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat count⟩,
        { w with memory := w.memory ++ limbBytes (limbsOf (beAt d off len) count) })) := by
  have hS : UInt256.size = 2 ^ 256 := rfl
  have hal := try_new_zeroed_exec (n := count) I w h0 hroom hc
  have hz : w.memory ++ zeros (8 * count) = limbsMem w.memory (beAt d off len) count 0 := by
    simp [limbsMem, limbBytes]
  rw [hz] at hal
  have hend : ∀ R, R ≤ count → (R = count ∨ R = (len + 7) / 8) →
      limbsMem w.memory (beAt d off len) count R = w.memory ++ limbBytes (limbsOf (beAt d off len) count) := by
    intro R hRc hR
    rcases hR with rfl | rfl
    · simp [limbsMem, zeros_zero, ByteArray.append_empty, List.take_of_length_le]
    · rw [limbsMem, limbsOf_take (beAt d off len) count ((len + 7) / 8)
        (lt_of_lt_of_le (beAt_lt d off len) (Nat.pow_le_pow_right (by norm_num) (by omega))) hRc,
        List.take_append_of_le_length (by simp; omega),
        List.take_of_length_le (by simp), limbBytes_append, limbBytes_replicate_zero,
        ByteArray.append_assoc]
  simp only [input_limbs_MemBuffer, Fe.M.exec_bind, hal, if_true, Lib.Option_MemArray_u64.Some_0,
    checkedAdd_small (show len + 7 < 2 ^ 256 by omega),
    checkedDiv_lit (show len + 7 < 2 ^ 256 by omega) (show 8 < 2 ^ 256 by norm_num) (by norm_num),
    pure_bind, toNat_lit (show (len + 7) / 8 < 2 ^ 256 by omega),
    toNat_lit (show count < 2 ^ 256 by omega), Lib.Range_start_0]
  by_cases hp : (len + 7) / 8 < count
  · simp only [hp, decide_true, if_true]
    rw [limbs_loop h hoff le_rfl hp.le hroom I _ 0 (Nat.zero_add _), hend _ hp.le (Or.inr rfl)]
  · simp only [hp, decide_false, Bool.false_eq_true, if_false]
    rw [limbs_loop h hoff (by omega) le_rfl hroom I _ 0 (Nat.zero_add _), hend _ le_rfl (Or.inl rfl)]

end FeProofs.Modexp
