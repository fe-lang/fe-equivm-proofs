import FeProofs.Precompiles.Limbs
import FeProofs.Precompiles.Field.Checked

/-!
# Precompiles: `MemArray<u64>`

What the exported std functions on `MemArray<u64>` do, on an array that holds given limbs
(`ArrayAt`):

- `index_ref_eq`, `index_mut_eq`: the address of element `i`, `ptr + 8 i`, for `i` below the
  length; `index_ref_oob`, `index_mut_oob`: at or past the length both panic with code 50
  (`PANIC_INDEX_OUT_OF_BOUNDS`) and touch nothing.  `limb_eq`: the raw `limb(ptr, i)` address,
  unchecked.
- `load_exec`, `store_exec`: `mloadInt (.u 64)` reads a limb the memory holds, `mstoreInt (.u 64)`
  writes `store8`; `ArrayAt.store` and `LimbsAt.store_other` say what holds after.
- `try_new_zeroed_exec`: `MemArray::try_new_zeroed(n)` takes `8 n` fresh zero bytes at the end of
  memory, which then holds `n` zero limbs there (`arrayAt_fresh`): memory grows by exactly those
  bytes, so everything allocated before is unchanged.
- `loop_up`: the induction of a counted `partial_fixpoint` loop, from a step that keeps an
  invariant.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

open Lib (MemArray_u64)

/-- The array `a` holds the limbs `ls` in the memory `mem`, which is smaller than `2 ^ 256`
    bytes. -/
structure ArrayAt (a : MemArray_u64) (ls : List Limb) (mem : ByteArray) : Prop where
  len : a.len.toNat = ls.length
  limbs : LimbsAt mem a.ptr.toNat ls
  small : mem.size < UInt256.size

theorem ArrayAt.addr_lt {a : MemArray_u64} {ls : List Limb} {mem : ByteArray} (h : ArrayAt a ls mem)
    {i : ℕ} (hi : i < ls.length) : a.ptr.toNat + 8 * i + 8 ≤ mem.size := by
  have := h.limbs.1; omega

/-- The address `p + 8 i`. -/
theorem addr_eq (p : UInt256) {i : ℕ} (h : p.toNat + 8 * i < UInt256.size) :
    p + UInt256.ofNat i * UInt256.ofNat 8 = UInt256.ofNat (p.toNat + 8 * i) := by
  rw [Fe.EVM.ofNat_mul_ofNat (by omega) (by unfold UInt256.size; omega) (by omega),
    ← ofNat_toNat p, ofNat_toNat, show i * 8 = 8 * i by ring]
  conv_lhs => rw [← ofNat_toNat p]
  exact Fe.EVM.ofNat_add_ofNat h

theorem elem_eq (p : UInt256) {i : ℕ} (h : p.toNat + 8 * i < UInt256.size) :
    Lib.elem_u64 p (UInt256.ofNat i) = pure (UInt256.ofNat (p.toNat + 8 * i)) := by
  simp only [Lib.elem_u64, Lib.usize_wrapping_mul, pure_bind, addr_eq p h]

/-- `limb(ptr, i)`, the unchecked address of limb `i`. -/
theorem limb_eq (p : UInt256) {i : ℕ} (h : p.toNat + 8 * i < UInt256.size) :
    p + UInt256.ofNat i * UInt256.ofNat 8 = UInt256.ofNat (p.toNat + 8 * i) := addr_eq p h

/-- **Element `i` of an array**, below its length. -/
theorem index_ref_eq {a : MemArray_u64} {i : ℕ} (hi : i < a.len.toNat)
    (h : a.ptr.toNat + 8 * i < UInt256.size) :
    Lib.MemArray_index_ref_u64 a (UInt256.ofNat i) = pure (UInt256.ofNat (a.ptr.toNat + 8 * i)) := by
  have hi' : (UInt256.ofNat i).toNat = i := toNat_lit (by unfold UInt256.size at h; omega)
  simp [Lib.MemArray_index_ref_u64, Lib.mem_array_elem_u64, hi', Nat.not_le.mpr hi, elem_eq _ h]

theorem index_mut_eq {a : MemArray_u64} {i : ℕ} (hi : i < a.len.toNat)
    (h : a.ptr.toNat + 8 * i < UInt256.size) :
    Lib.MemArray_index_mut_u64 a (UInt256.ofNat i) =
      pure (UInt256.ofNat (a.ptr.toNat + 8 * i), fun _ => pure a) := by
  have hi' : (UInt256.ofNat i).toNat = i := toNat_lit (by unfold UInt256.size at h; omega)
  simp [Lib.MemArray_index_mut_u64, Lib.mem_array_elem_u64, hi', Nat.not_le.mpr hi, elem_eq _ h]

/-- **Out of bounds**, an index panics with code 50 and changes nothing. -/
theorem index_ref_oob {a : MemArray_u64} {i : ℕ} (hi : a.len.toNat ≤ i) (h : i < UInt256.size)
    (I : Env) (w : World) :
    (Lib.MemArray_index_ref_u64 a (UInt256.ofNat i)).exec I w = some (.error (.panic 50)) := by
  have hi' : (UInt256.ofNat i).toNat = i := toNat_lit h
  simp [Lib.MemArray_index_ref_u64, Lib.mem_array_elem_u64, hi', hi, Lib.index_out_of_bounds,
    Lib.PANIC_INDEX_OUT_OF_BOUNDS, panicCode, toNat_lit (show 50 < 2 ^ 256 by norm_num)]

theorem index_mut_oob {a : MemArray_u64} {i : ℕ} (hi : a.len.toNat ≤ i) (h : i < UInt256.size)
    (I : Env) (w : World) :
    (Lib.MemArray_index_mut_u64 a (UInt256.ofNat i)).exec I w = some (.error (.panic 50)) := by
  have hi' : (UInt256.ofNat i).toNat = i := toNat_lit h
  simp [Lib.MemArray_index_mut_u64, Lib.mem_array_elem_u64, hi', hi, Lib.index_out_of_bounds,
    Lib.PANIC_INDEX_OUT_OF_BOUNDS, panicCode, toNat_lit (show 50 < 2 ^ 256 by norm_num)]

/-- The `u64` of a limb's number. -/
theorem cast64 (x : Limb) : IntTy.cast (.u 256) (.u 64) (UInt256.ofNat x.val) = x.w := by
  have hx := x.isLt
  simp only [IntTy.cast, IntTy.val, IntTy.wrap, Limb.w]
  rw [ulit_toNat' _ (by unfold UInt256.size; omega)]
  norm_cast
  rw [Int.toNat_natCast, Nat.mod_eq_of_lt hx]

/-- **A limb that memory holds**, read. -/
theorem load_exec {w : World} {p : ℕ} {ls : List Limb} (h : LimbsAt w.memory p ls) {i : ℕ}
    (hi : i < ls.length) (hs : w.memory.size < UInt256.size) (I : Env) :
    (mloadInt (.u 64) (UInt256.ofNat (p + 8 * i))).exec I w = some (.ok (ls[i].w, w)) := by
  have hb : p + 8 * i + 8 ≤ w.memory.size := by have := h.1; omega
  have hr := read_beAt w.memory (p + 8 * i) 8 (by decide) (by decide) hb
  rw [h.2 i hi] at hr
  simp only [mloadInt, show (IntTy.u 64).bits / 8 = 8 from rfl, toNat_lit (show p + 8 * i < 2 ^ 256
    by unfold UInt256.size at hs; omega), hr, cast64, Fe.M.exec_bind, Fe.M.exec_get]
  rfl

/-- **A limb written**: `store8`. -/
theorem store_exec {q : ℕ} (hq : q < UInt256.size) (x : Limb) (I : Env) (w : World) :
    (mstoreInt (.u 64) (UInt256.ofNat q) x.w).exec I w =
      some (.ok ((), { w with memory := store8 w.memory q x })) := by
  simp only [mstoreInt, Fe.M.exec_modify, toNat_lit (show q < 2 ^ 256 from hq), store8, enc8,
    show (IntTy.u 64).bits / 8 = 8 from rfl]

/-- A store over element `i` of an array. -/
theorem ArrayAt.store {a : MemArray_u64} {ls : List Limb} {mem : ByteArray} (h : ArrayAt a ls mem)
    {i : ℕ} (hi : i < ls.length) (x : Limb) :
    ArrayAt a (ls.set i x) (store8 mem (a.ptr.toNat + 8 * i) x) :=
  ⟨by rw [List.length_set]; exact h.len, h.limbs.store hi x,
    by rw [store8_size x (h.addr_lt hi)]; exact h.small⟩

/-- A store apart from an array. -/
theorem ArrayAt.store_other {a : MemArray_u64} {ls : List Limb} {mem : ByteArray}
    (h : ArrayAt a ls mem) {q : ℕ} (hq : q + 8 ≤ mem.size)
    (hd : q + 8 ≤ a.ptr.toNat ∨ a.ptr.toNat + 8 * ls.length ≤ q) (x : Limb) :
    ArrayAt a ls (store8 mem q x) :=
  ⟨h.len, h.limbs.store_other hq hd x, by rw [store8_size x hq]; exact h.small⟩

theorem ArrayAt.append {a : MemArray_u64} {ls : List Limb} {mem : ByteArray} (h : ArrayAt a ls mem)
    (X : ByteArray) (hs : mem.size + X.size < UInt256.size) : ArrayAt a ls (mem ++ X) :=
  ⟨h.len, h.limbs.append X, by rw [ByteArray.size_append]; exact hs⟩

/-! ## Allocation -/

theorem max_allocation : Lib.MAX_ALLOCATION = pure (UInt256.ofNat (2 ^ 64 - 1)) := rfl

/-- Zeroing fresh zeros changes nothing. -/
theorem zeros_write_zeros (mem : ByteArray) (n : ℕ) :
    (zeros n).write 0 (mem ++ zeros n) mem.size n = mem ++ zeros n := by
  have hs : mem.size + n ≤ (mem ++ zeros n).size := by simp [ByteArray.size_append]
  apply ext_byteAt (byteArray_write_size_of_inBounds _ _ _ _ (by simp) hs)
  intro j _
  rw [byteAt_write _ _ _ _ _ (by simp) hs, byteAt_zeros, byteAt_append]
  split_ifs with h1 h2 <;> first | rfl | (rw [byteAt_zeros]) | omega

/-- `try_alloc_bytes(k)` in nonempty memory with room: `k` fresh zero bytes at the end. -/
theorem try_alloc_bytes_exec {k : ℕ} (I : Env) (w : World) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + k < UInt256.size) (hk : k ≤ 2 ^ 64 - 1) :
    (Lib.try_alloc_bytes (UInt256.ofNat k)).exec I w =
      some (.ok (.Some (UInt256.ofNat w.memory.size), { w with memory := w.memory ++ zeros k })) := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  have hk' : (UInt256.ofNat k).toNat = k := toNat_lit (by omega)
  have hm : (UInt256.ofNat w.memory.size).toNat = w.memory.size := toNat_lit (by omega)
  have hne : UInt256.ofNat w.memory.size ≠ UInt256.ofNat 0 := fun e => by
    have := congrArg UInt256.toNat e; rw [hm, toNat_lit (by norm_num)] at this; omega
  have hmax : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := toNat_lit (by norm_num)
  simp only [Lib.try_alloc_bytes, max_allocation, pure_bind, hk', hmax,
    show ¬ (2 ^ 64 - 1 < k) by omega, decide_false, Bool.false_eq_true, if_false]
  simp only [Fe.M.exec_bind, alloc, Fe.M.exec_get, hk', if_pos hroom, Fe.M.exec_set,
    Fe.M.exec_pure, hne, decide_false, Bool.false_eq_true, if_false]
  rfl

/-- **`MemArray::try_new_zeroed(n)`** in nonempty memory with room for `8 n` more bytes: an
    array of `n` limbs at the end of memory, memory grown by `8 n` zero bytes. -/
theorem try_new_zeroed_exec {n : ℕ} (I : Env) (w : World) (h0 : 0 < w.memory.size)
    (hroom : w.memory.size + 8 * n < UInt256.size) (hn : 8 * n < 2 ^ 64) :
    (Lib.MemArray_try_new_zeroed_u64 (UInt256.ofNat n)).exec I w =
      some (.ok (.Some ⟨UInt256.ofNat w.memory.size, UInt256.ofNat n⟩,
        { w with memory := w.memory ++ zeros (8 * n) })) := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  have hn' : (UInt256.ofNat n).toNat = n := toNat_lit (by omega)
  have hmax : (UInt256.ofNat ((2 ^ 64 - 1) / 8)).toNat = (2 ^ 64 - 1) / 8 := toNat_lit (by norm_num)
  have hm8 : checkedMul (UInt256.ofNat n) (UInt256.ofNat 8) = pure (UInt256.ofNat (8 * n)) := by
    rw [checkedMul_small (by omega) (by norm_num) (by omega), Nat.mul_comm]
  have hm : (UInt256.ofNat w.memory.size).toNat = w.memory.size := toNat_lit (by omega)
  have h8 : (UInt256.ofNat (8 * n)).toNat = 8 * n := toNat_lit (by omega)
  have hne : (UInt256.ofNat 8 ≠ UInt256.ofNat 0) = True := by
    apply propext; constructor
    · intro _; trivial
    · intro _ e; have := congrArg UInt256.toNat e
      rw [toNat_lit (by norm_num), toNat_lit (by norm_num)] at this; omega
  have hal := try_alloc_bytes_exec (k := 8 * n) I w h0 hroom (by omega)
  simp only [Lib.MemArray_try_new_zeroed_u64, Lib.MemArray_try_new_uninit_u64,
    Lib.try_alloc_elems_u64, max_allocation, Lib.MemArray_byte_len_u64, Lib.cast_u8_u64,
    Lib.zero_bytes, Lib.cast_u64_u8, pure_bind, bind_assoc, hne, decide_true, if_true,
    checkedDiv_lit (show 2 ^ 64 - 1 < 2 ^ 256 by norm_num) (show 8 < 2 ^ 256 by norm_num)
      (by norm_num), hmax, hn', show ¬ ((2 ^ 64 - 1) / 8 < n) by omega, decide_false,
    Bool.false_eq_true, if_false, hm8]
  simp only [Fe.M.exec_bind, hal, Fe.M.exec_pure, Lib.Option_u8.Some_0, Lib.Option_u64.Some_0,
    Lib.Option_MemArray_u64.Some_0, if_true, zeroMem, Fe.M.exec_modify, hm]
  simp only [hm8, Fe.M.exec_pure, h8,
    show (⟨Array.replicate (8 * n) 0⟩ : ByteArray) = zeros (8 * n) from rfl, zeros_write_zeros]

/-- The array `try_new_zeroed(n)` makes holds `n` zero limbs. -/
theorem arrayAt_fresh (mem : ByteArray) (n : ℕ) (hroom : mem.size + 8 * n < UInt256.size) :
    ArrayAt ⟨UInt256.ofNat mem.size, UInt256.ofNat n⟩ (List.replicate n 0) (mem ++ zeros (8 * n)) :=
  ⟨by rw [List.length_replicate]; exact toNat_lit (by unfold UInt256.size at hroom; omega),
    by rw [toNat_lit (by unfold UInt256.size at hroom; omega)]; exact limbsAt_zeros mem n,
    by rw [ByteArray.size_append, zeros_size]; exact hroom⟩

/-! ## Counted loops -/

/-- **A counted loop**: if from each index `i < N` the run of the loop at `i`, in a state and world
    with the invariant `P i`, is its run at `i + 1` in another such, then from any `i ≤ N` it is
    its run at `N` in a state and world with `P N`. -/
theorem loop_up {α S : Type} {I : Env} (N : ℕ) (P : ℕ → S → World → Prop) (L : ℕ → S → FeM α)
    (step : ∀ i s w, i < N → P i s w →
      ∃ s' w', P (i + 1) s' w' ∧ (L i s).exec I w = (L (i + 1) s').exec I w') :
    ∀ i s w, i ≤ N → P i s w → ∃ s' w', P N s' w' ∧ (L i s).exec I w = (L N s').exec I w' := by
  intro i
  induction h : N - i generalizing i with
  | zero => intro s w hi hp; exact ⟨s, w, by rwa [show i = N by omega] at hp, by rw [show i = N by omega]⟩
  | succ k ih =>
    intro s w hi hp
    obtain ⟨s', w', hp', he⟩ := step i s w (by omega) hp
    obtain ⟨s'', w'', hp'', he'⟩ := ih (i + 1) (by omega) s' w' (by omega) hp'
    exact ⟨s'', w'', hp'', he.trans he'⟩

end FeProofs.Precompiles
