import FeProofs.Precompiles.Buffer

/-!
# Precompiles: limbs in memory

Fe's `MemArray<u64>` is a pointer and a length; element `i` lies at `ptr + 8 i`, and the exported
code reads it with `mloadInt (.u 64)` and writes it with `mstoreInt (.u 64)`: eight bytes,
big-endian.  This file says what memory holds in those terms.

- Bytes: `byteAt_append`, `byteAt_write`, `zeros`, `ext_byteAt` (two memories with the same
  bytes are equal), `beAt_congr` (a number read depends only on its bytes), `read_beAt` (what
  `readWithPadding` gives, as `beAt`).
- Limbs: `val` (the little-endian number of limbs), `enc8` and `store8` (the bytes `mstoreInt`
  writes), `LimbsAt mem p ls` (memory at `p` holds the limbs `ls`), with the lemmas for a store
  over one of them (`LimbsAt.store`), a store elsewhere (`LimbsAt.store_other`), memory that
  grows (`LimbsAt.append`) and fresh zeros (`limbsAt_zeros`).
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Precompiles

/-! ## Bytes -/

theorem byteAt_eq (d : ByteArray) (j : ℕ) :
    byteAt d j = if h : j < d.size then d[j].toNat else 0 := by
  have hl : d.toList.length = d.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  split_ifs with h
  · simp only [byteAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < d.toList.length),
      Option.getD_some]
    congr 1
    rw [List.getElem_of_eq (byteArray_toList_eq d)]
    simp [Array.getElem_toList]
    rfl
  · exact byteAt_of_ge (by omega)

theorem byteAt_append (a b : ByteArray) (j : ℕ) :
    byteAt (a ++ b) j = if j < a.size then byteAt a j else byteAt b (j - a.size) := by
  have hs := ByteArray.size_append (a := a) (b := b)
  by_cases h : j < a.size
  · rw [if_pos h, byteAt_eq, byteAt_eq, dif_pos (by omega), dif_pos h,
      ByteArray.getElem_append_left h]
  · rw [if_neg h, byteAt_eq, byteAt_eq]
    by_cases h' : j - a.size < b.size
    · rw [dif_pos (by omega), dif_pos h', ByteArray.getElem_append_right (by omega)]
    · rw [dif_neg (by omega), dif_neg h']

theorem byteAt_extract (d : ByteArray) (s e j : ℕ) (h : e ≤ d.size) :
    byteAt (d.extract s e) j = if j < e - s then byteAt d (s + j) else 0 := by
  have hs : (d.extract s e).size = e - s := by rw [ByteArray.size_extract, Nat.min_eq_left h]
  by_cases hj : j < e - s
  · rw [if_pos hj, byteAt_eq, byteAt_eq, dif_pos (by omega), dif_pos (by omega),
      ByteArray.getElem_extract]
  · rw [if_neg hj, byteAt_of_ge (by omega)]

/-- Writing `n` bytes of `src` at `a` inside `mem` changes those bytes only. -/
theorem byteAt_write (src mem : ByteArray) (a n j : ℕ) (hn : n ≤ src.size) (h : a + n ≤ mem.size) :
    byteAt (src.write 0 mem a n) j = if a ≤ j ∧ j < a + n then byteAt src (j - a) else byteAt mem j := by
  by_cases h0 : n = 0
  · subst h0; rw [byteArray_write_len_zero]; simp
  rw [write_eq_gen _ _ _ _ h0 hn h, byteAt_append, byteAt_append]
  simp only [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left (show a ≤ mem.size by omega),
    Nat.min_eq_left hn, Nat.sub_zero]
  rw [byteAt_extract _ _ _ _ (by omega), byteAt_extract _ _ _ _ (by omega),
    byteAt_extract _ _ _ _ le_rfl]
  simp only [Nat.sub_zero, Nat.zero_add]
  by_cases h1 : j < a
  · rw [if_pos (by omega), if_pos h1, if_pos h1, if_neg (by omega)]
  · by_cases h2 : j < a + n
    · rw [if_pos h2, if_neg h1, if_pos (by omega), if_pos ⟨by omega, h2⟩]
    · rw [if_neg h2, if_neg (show ¬ (a ≤ j ∧ j < a + n) by omega)]
      by_cases h3 : j - (a + n) < mem.size - (a + n)
      · rw [if_pos h3, show a + n + (j - (a + n)) = j by omega]
      · rw [if_neg h3, byteAt_of_ge (by omega)]

/-- Writing `n` bytes of `src` from `so` at `a` inside `mem` changes those bytes only. -/
theorem byteAt_write_from (src mem : ByteArray) (so a n j : ℕ) (hn : so + n ≤ src.size)
    (h : a + n ≤ mem.size) :
    byteAt (src.write so mem a n) j =
      if a ≤ j ∧ j < a + n then byteAt src (so + (j - a)) else byteAt mem j := by
  by_cases h0 : n = 0
  · subst h0; rw [byteArray_write_len_zero]; simp
  rw [write_eq_gen_from _ _ _ _ _ h0 hn h, byteAt_append, byteAt_append]
  simp only [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left (show a ≤ mem.size by omega),
    Nat.min_eq_left hn, Nat.sub_zero, Nat.add_sub_cancel_left]
  rw [byteAt_extract _ _ _ _ (by omega), byteAt_extract _ _ _ _ hn,
    byteAt_extract _ _ _ _ le_rfl]
  simp only [Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel_left]
  by_cases h1 : j < a
  · rw [if_pos (by omega), if_pos h1, if_pos h1, if_neg (by omega)]
  · by_cases h2 : j < a + n
    · rw [if_pos (by omega), if_neg h1, if_pos (by omega), if_pos ⟨(by omega), h2⟩]
    · rw [if_neg (by omega), if_neg (show ¬ (a ≤ j ∧ j < a + n) by omega)]
      by_cases h3 : j < mem.size
      · rw [if_pos (by omega)]; congr 1; omega
      · rw [if_neg (by omega), byteAt_of_ge (by omega)]

theorem write_size_from (src mem : ByteArray) (so a n : ℕ) (hn : so + n ≤ src.size)
    (h : a + n ≤ mem.size) : (src.write so mem a n).size = mem.size := by
  by_cases h0 : n = 0
  · subst h0; rw [byteArray_write_len_zero]
  rw [write_eq_gen_from _ _ _ _ _ h0 hn h]
  simp only [ByteArray.size_append, ByteArray.size_extract]
  omega

/-- `n` zero bytes. -/
def zeros (n : ℕ) : ByteArray := ⟨Array.replicate n 0⟩

@[simp] theorem zeros_size (n : ℕ) : (zeros n).size = n := Array.size_replicate

theorem byteAt_zeros (n j : ℕ) : byteAt (zeros n) j = 0 := by
  rw [byteAt_eq]
  split_ifs with h
  · show ((zeros n).data[j]'(by simpa using h)).toNat = 0
    simp [zeros]
  · rfl

/-- **Memories with the same bytes are equal.** -/
theorem ext_byteAt {d d' : ByteArray} (hs : d.size = d'.size)
    (h : ∀ j < d.size, byteAt d j = byteAt d' j) : d = d' := by
  apply ByteArray.ext
  apply Array.ext hs
  intro j h1 h2
  have := h j h1
  rw [byteAt_eq, byteAt_eq, dif_pos (show j < d.size from h1),
    dif_pos (show j < d'.size from h2)] at this
  exact UInt8.toNat_inj.mp this

/-- A number read depends only on its bytes. -/
theorem beAt_congr {d d' : ByteArray} {o o' : ℕ} :
    ∀ {n}, (∀ k < n, byteAt d (o + k) = byteAt d' (o' + k)) → beAt d o n = beAt d' o' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [beAt, beAt, beAt_congr (fun k hk => h k (by omega)), h n (by omega)]

/-- **A read inside memory** is `beAt`. -/
theorem read_beAt (mem : ByteArray) (a n : ℕ) (hn : 0 < n) (hn64 : n < 2 ^ 64)
    (h : a + n ≤ mem.size) : fromByteArrayBigEndian (mem.readWithPadding a n) = beAt mem a n := by
  rw [readWithPadding_eq_extract' _ _ _ hn hn64 h, fromByteArrayBigEndian_extract _ _ _ h]

/-! ## Limbs -/

/-- The number of limbs, least significant first. -/
def val : List Limb → ℕ
  | [] => 0
  | x :: xs => x.val + 2 ^ 64 * val xs

theorem val_lt : ∀ ls : List Limb, val ls < 2 ^ (64 * ls.length)
  | [] => by simp [val]
  | x :: xs => by
    have := val_lt xs
    have := x.isLt
    rw [val, List.length_cons, show 64 * (xs.length + 1) = 64 + 64 * xs.length by ring, pow_add]
    nlinarith

theorem val_append : ∀ a b : List Limb, val (a ++ b) = val a + 2 ^ (64 * a.length) * val b
  | [], b => by simp [val]
  | x :: xs, b => by
    rw [List.cons_append, val, val, val_append xs b, List.length_cons,
      show 64 * (xs.length + 1) = 64 + 64 * xs.length by ring, pow_add]
    ring

theorem val_replicate_zero (n : ℕ) : val (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, val, ih]; rfl

/-- Limb `k` of the number. -/
theorem val_limb : ∀ (ls : List Limb) (k : ℕ) (hk : k < ls.length),
    val ls / 2 ^ (64 * k) % 2 ^ 64 = ls[k].val
  | x :: xs, 0, _ => by
    simp only [val, Nat.mul_zero, pow_zero, Nat.div_one, List.getElem_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]
  | x :: xs, k + 1, hk => by
    have hx := x.isLt
    rw [val, show 64 * (k + 1) = 64 + 64 * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
      show (x.val + 2 ^ 64 * val xs) / 2 ^ 64 = val xs by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add],
      List.getElem_cons_succ]
    exact val_limb xs k (by simp at hk; omega)

/-- Limbs past the first `c` that are zero do not count. -/
theorem val_take_of_zero (ls : List Limb) (c : ℕ)
    (hz : ∀ j (hj : j < ls.length), c ≤ j → ls[j] = 0) : val ls = val (ls.take c) := by
  have hd : ls.drop c = List.replicate (ls.drop c).length 0 :=
    List.eq_replicate_iff.mpr ⟨rfl, fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_drop]
      exact hz _ (by simp at hj; omega) (by omega)⟩
  conv_lhs => rw [← List.take_append_drop c ls, val_append, hd, val_replicate_zero]
  simp

/-- **The top bit of limbs** whose last nonzero one is limb `c`. -/
theorem log2_val (ls : List Limb) (c : ℕ) (hc : c < ls.length)
    (hz : ∀ j (hj : j < ls.length), c < j → ls[j] = 0) (hne : ls[c] ≠ 0) :
    val ls ≠ 0 ∧ (val ls).log2 = 64 * c + ls[c].val.log2 := by
  have h1 : val ls = val (ls.take c) + 2 ^ (64 * c) * ls[c].val := by
    rw [val_take_of_zero ls (c + 1) (fun j hj hcj => hz j hj (by omega)), List.take_add_one,
      List.getElem?_eq_getElem hc, Option.toList_some, val_append, List.length_take,
      Nat.min_eq_left hc.le]
    simp [val]
  have hlo : val (ls.take c) < 2 ^ (64 * c) := by
    have := val_lt (ls.take c); rwa [List.length_take, Nat.min_eq_left hc.le] at this
  have ha : ls[c].val ≠ 0 := fun h => hne (Fin.ext h)
  have hL1 := Nat.log2_self_le ha
  have hL2 := Nat.lt_log2_self (n := ls[c].val)
  have hV : val ls ≠ 0 := by
    rw [h1]; have : 0 < 2 ^ (64 * c) * ls[c].val := Nat.mul_pos (by positivity) (by omega)
    omega
  refine ⟨hV, le_antisymm ?_ ?_⟩
  · rw [← Nat.lt_succ_iff, Nat.log2_lt hV, h1]
    calc val (ls.take c) + 2 ^ (64 * c) * ls[c].val < 2 ^ (64 * c) * (ls[c].val + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ 2 ^ (64 * c) * 2 ^ (ls[c].val.log2 + 1) := Nat.mul_le_mul_left _ hL2
      _ = 2 ^ (64 * c + ls[c].val.log2).succ := by rw [← pow_add]; rfl
  · rw [Nat.le_log2 hV, h1, pow_add]
    exact le_trans (Nat.mul_le_mul_left _ hL1) (Nat.le_add_left _ _)

/-- A bit of a number below `2 ^ 64` past its first `q` limbs. -/
theorem bit_low (n r : ℕ) (hr : r < 64) : n / 2 ^ r % 2 = n % 2 ^ 64 / 2 ^ r % 2 := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ 64)]
  rw [show 2 ^ 64 * (n / 2 ^ 64) = 2 ^ r * (2 ^ (64 - r) * (n / 2 ^ 64)) by
      rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_cancel' hr.le], Nat.add_comm,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod,
    show 2 ^ (64 - r) * (n / 2 ^ 64) % 2 = 0 by
      rw [show 64 - r = (64 - r - 1) + 1 by omega, pow_succ]
      rw [Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _,
    Nat.add_zero, Nat.mod_mod]

/-- **Bit `p` of the number** is bit `p mod 64` of limb `p / 64`. -/
theorem val_bit (ls : List Limb) (p : ℕ) (hp : p < 64 * ls.length) :
    val ls / 2 ^ p % 2 = ls[p / 64].val / 2 ^ (p % 64) % 2 := by
  rw [← val_limb ls (p / 64) (by omega), ← bit_low _ _ (Nat.mod_lt _ (by norm_num)),
    Nat.div_div_eq_div_mul, ← pow_add, Nat.div_add_mod]

/-- The eight bytes `mstoreInt (.u 64)` writes of a limb. -/
def enc8 (x : Limb) : ByteArray := x.w.toByteArray.extract 24 32

@[simp] theorem enc8_size (x : Limb) : (enc8 x).size = 8 := by
  rw [enc8, ByteArray.size_extract, toByteArray_size]; rfl

theorem beAt_enc8 (x : Limb) : beAt (enc8 x) 0 8 = x.val := by
  rw [← fromByteArrayBigEndian_extract _ 0 8 (by simp), Nat.zero_add,
    show (enc8 x).extract 0 8 = enc8 x by
      conv_rhs => rw [← ByteArray.extract_zero_size (b := enc8 x)]
      rw [enc8_size],
    enc8, fromByteArrayBigEndian_low8, Limb.toNat_w, Nat.mod_eq_of_lt x.isLt]

/-- Memory with the limb `x` stored at `q`. -/
def store8 (mem : ByteArray) (q : ℕ) (x : Limb) : ByteArray := (enc8 x).write 0 mem q 8

theorem store8_size {mem : ByteArray} {q : ℕ} (x : Limb) (h : q + 8 ≤ mem.size) :
    (store8 mem q x).size = mem.size :=
  byteArray_write_size_of_inBounds _ _ _ _ (by simp) h

theorem byteAt_store8 {mem : ByteArray} {q : ℕ} (x : Limb) (h : q + 8 ≤ mem.size) (j : ℕ) :
    byteAt (store8 mem q x) j =
      if q ≤ j ∧ j < q + 8 then byteAt (enc8 x) (j - q) else byteAt mem j :=
  byteAt_write _ _ _ _ _ (by simp) h

theorem beAt_store8_same {mem : ByteArray} {q : ℕ} (x : Limb) (h : q + 8 ≤ mem.size) :
    beAt (store8 mem q x) q 8 = x.val := by
  rw [← beAt_enc8 x]
  apply beAt_congr
  intro k hk
  rw [byteAt_store8 x h, if_pos (by omega), Nat.zero_add, Nat.add_sub_cancel_left]

/-- A store leaves the bytes of a window apart from it. -/
theorem beAt_store8_other {mem : ByteArray} {q r n : ℕ} (x : Limb) (h : q + 8 ≤ mem.size)
    (hd : r + n ≤ q ∨ q + 8 ≤ r) : beAt (store8 mem q x) r n = beAt mem r n := by
  apply beAt_congr
  intro k hk
  rw [byteAt_store8 x h, if_neg (by omega)]

/-- **Memory at `p` holds the limbs `ls`**: element `i` is the big-endian number of the eight
    bytes at `p + 8 i`, all inside memory. -/
def LimbsAt (mem : ByteArray) (p : ℕ) (ls : List Limb) : Prop :=
  p + 8 * ls.length ≤ mem.size ∧ ∀ i (h : i < ls.length), beAt mem (p + 8 * i) 8 = ls[i].val

/-- A store over limb `i`. -/
theorem LimbsAt.store {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls) {i : ℕ}
    (hi : i < ls.length) (x : Limb) : LimbsAt (store8 mem (p + 8 * i) x) p (ls.set i x) := by
  have hq : p + 8 * i + 8 ≤ mem.size := by have := h.1; omega
  refine ⟨by rw [store8_size x hq, List.length_set]; exact h.1, fun k hk => ?_⟩
  rw [List.length_set] at hk
  by_cases hik : i = k
  · subst hik; rw [List.getElem_set_self, beAt_store8_same x hq]
  · rw [List.getElem_set_ne hik, beAt_store8_other x hq (by omega), h.2 k hk]

/-- A store apart from the limbs. -/
theorem LimbsAt.store_other {mem : ByteArray} {p q : ℕ} {ls : List Limb} (h : LimbsAt mem p ls)
    (hq : q + 8 ≤ mem.size) (hd : q + 8 ≤ p ∨ p + 8 * ls.length ≤ q) (x : Limb) :
    LimbsAt (store8 mem q x) p ls :=
  ⟨by rw [store8_size x hq]; exact h.1, fun k hk => by
    rw [beAt_store8_other x hq (by omega), h.2 k hk]⟩

/-- Memory that grows keeps the limbs. -/
theorem LimbsAt.append {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls)
    (X : ByteArray) : LimbsAt (mem ++ X) p ls :=
  ⟨by rw [ByteArray.size_append]; have := h.1; omega, fun k hk => by
    rw [← h.2 k hk]
    apply beAt_congr
    intro j hj
    rw [byteAt_append, if_pos (by have := h.1; omega)]⟩

/-- Memory whose bytes over the limbs are the same holds them too. -/
theorem LimbsAt.congr {mem mem' : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls)
    (hs : p + 8 * ls.length ≤ mem'.size)
    (hb : ∀ j, p ≤ j → j < p + 8 * ls.length → byteAt mem' j = byteAt mem j) :
    LimbsAt mem' p ls :=
  ⟨hs, fun k hk => by
    rw [← h.2 k hk]
    apply beAt_congr
    intro j hj
    exact hb _ (by omega) (by omega)⟩

/-- **Fresh zeros** hold zero limbs. -/
theorem limbsAt_zeros (mem : ByteArray) (n : ℕ) :
    LimbsAt (mem ++ zeros (8 * n)) mem.size (List.replicate n 0) := by
  refine ⟨by simp [ByteArray.size_append], fun k hk => ?_⟩
  rw [List.length_replicate] at hk
  rw [List.getElem_replicate]
  have : beAt (mem ++ zeros (8 * n)) (mem.size + 8 * k) 8 = beAt (zeros 8) 0 8 := by
    apply beAt_congr
    intro j hj
    rw [byteAt_append, if_neg (by omega), byteAt_zeros, byteAt_zeros]
  rw [this]
  simp [beAt, byteAt_zeros]

/-! ## Limbs written into fresh memory -/

/-- The bytes of limbs in memory: eight big-endian bytes each, in order. -/
def limbBytes : List Limb → ByteArray
  | [] => .empty
  | x :: xs => enc8 x ++ limbBytes xs

@[simp] theorem limbBytes_size : ∀ ls : List Limb, (limbBytes ls).size = 8 * ls.length
  | [] => rfl
  | x :: xs => by
    rw [limbBytes, ByteArray.size_append, enc8_size, limbBytes_size xs, List.length_cons]; ring

/-- **Memory followed by the bytes of limbs** holds them. -/
theorem limbsAt_limbBytes : ∀ (A : ByteArray) (ls : List Limb), LimbsAt (A ++ limbBytes ls) A.size ls
  | A, [] => ⟨by simp [ByteArray.size_append], fun i h => absurd h (by simp)⟩
  | A, x :: xs => by
    have ih := limbsAt_limbBytes (A ++ enc8 x) xs
    rw [ByteArray.size_append, enc8_size, ByteArray.append_assoc, ← limbBytes] at ih
    refine ⟨by simp only [ByteArray.size_append, limbBytes_size, List.length_cons]; omega,
      fun i hi => ?_⟩
    rcases i with _ | i
    · rw [List.getElem_cons_zero, ← beAt_enc8 x]
      apply beAt_congr
      intro k hk
      rw [limbBytes, byteAt_append, if_neg (by omega), byteAt_append, if_pos (by simp; omega),
        show A.size + 8 * 0 + k - A.size = 0 + k by omega]
    · rw [List.getElem_cons_succ, ← ih.2 i (by simpa using hi), show A.size + 8 * (i + 1) =
        A.size + 8 + 8 * i by ring]

/-- A limb stored at the start of fresh zeros: its bytes, then the rest of the zeros. -/
theorem store8_zeros (A : ByteArray) (x : Limb) (k q : ℕ) (hq : q = A.size) :
    store8 (A ++ zeros (k + 8)) q x = A ++ enc8 x ++ zeros k := by
  subst hq
  have hs : A.size + 8 ≤ (A ++ zeros (k + 8)).size := by
    rw [ByteArray.size_append, zeros_size]; omega
  have hsz : (store8 (A ++ zeros (k + 8)) A.size x).size = (A ++ enc8 x ++ zeros k).size := by
    rw [store8_size x hs]; simp only [ByteArray.size_append, zeros_size, enc8_size]; omega
  apply ext_byteAt hsz
  intro j _
  rw [byteAt_store8 x hs, byteAt_append, byteAt_append, byteAt_append, ByteArray.size_append,
    enc8_size, byteAt_zeros, byteAt_zeros]
  by_cases hj : j < A.size
  · rw [if_neg (by omega), if_pos hj, if_pos (by omega), if_pos hj]
  · by_cases hk : j < A.size + 8
    · rw [if_pos ⟨(by omega), hk⟩, if_pos hk, if_neg hj]
    · rw [if_neg (by omega), if_neg hj, if_neg hk]

theorem zeros_zero : zeros 0 = ByteArray.empty := rfl

theorem limbBytes_append : ∀ a b : List Limb, limbBytes (a ++ b) = limbBytes a ++ limbBytes b
  | [], b => by rw [List.nil_append, limbBytes, ByteArray.empty_append]
  | x :: a, b => by rw [List.cons_append, limbBytes, limbBytes, limbBytes_append a b,
      ByteArray.append_assoc]

theorem byteAt_zero_of_beAt {d : ByteArray} {off : ℕ} :
    ∀ {n}, beAt d off n = 0 → ∀ k < n, byteAt d (off + k) = 0
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    rw [beAt] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact byteAt_zero_of_beAt (by omega) k hk
    · subst hk; omega

theorem enc8_zero : enc8 0 = zeros 8 := by
  have h := beAt_enc8 0
  apply ext_byteAt (by simp)
  intro j hj
  rw [enc8_size] at hj
  rw [byteAt_zeros, show j = 0 + j by omega]
  exact byteAt_zero_of_beAt h j hj

/-- **Zero limbs** are zero bytes. -/
theorem limbBytes_replicate_zero : ∀ k : ℕ, limbBytes (List.replicate k 0) = zeros (8 * k)
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, limbBytes, limbBytes_replicate_zero k, enc8_zero]
    apply ByteArray.ext
    simp [zeros, ByteArray.data_append, show 8 * (k + 1) = 8 + 8 * k by ring, Array.replicate_append_replicate]

/-- The first `n` limbs of `N`, least significant first. -/
def limbsOf (N : ℕ) : ℕ → List Limb
  | 0 => []
  | n + 1 => ⟨N % 2 ^ 64, Nat.mod_lt _ (by norm_num)⟩ :: limbsOf (N / 2 ^ 64) n

@[simp] theorem limbsOf_length (N : ℕ) : ∀ n, (limbsOf N n).length = n
  | 0 => rfl
  | n + 1 => by rw [limbsOf, List.length_cons, limbsOf_length _ n]

theorem val_limbsOf : ∀ (N n : ℕ), val (limbsOf N n) = N % 2 ^ (64 * n)
  | N, 0 => by simp [limbsOf, val, Nat.mod_one]
  | N, n + 1 => by
    rw [limbsOf, val, val_limbsOf, show 64 * (n + 1) = 64 + 64 * n by ring, pow_add, Nat.mod_mul]

theorem limbsOf_getElem : ∀ (N n i : ℕ) (hi : i < (limbsOf N n).length),
    ((limbsOf N n)[i]).val = N / 2 ^ (64 * i) % 2 ^ 64
  | N, n + 1, 0, _ => by simp [limbsOf]
  | N, n + 1, i + 1, hi => by
    rw [show (limbsOf N (n + 1))[i + 1] = (limbsOf (N / 2 ^ 64) n)[i]'(by simp at hi ⊢; omega) from rfl,
      limbsOf_getElem _ n i, Nat.div_div_eq_div_mul, ← pow_add, show 64 + 64 * i = 64 * (i + 1) by ring]


end FeProofs.Precompiles
