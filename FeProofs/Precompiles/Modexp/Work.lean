import FeProofs.Precompiles.Modexp.TryRead
import FeProofs.Precompiles.Modexp.Quot32
import FeProofs.Precompiles.LimbSlice

/-!
# Modexp: a work array as a function of limbs

`Modulus::try_new` and `Modulus::reduce` write limbs one at a time through raw pointers, in
loops that run up and down.  Their proofs hold the limbs as a function `f : ℕ → Limb` and the
memory as `putLimbs mem p (lf f K)`: `mem` with the first `K` limbs of `f` written at `p`.

- `wv f a k`: the number of the limbs `[a, a + k)` of `f`, least significant first, with
  `wv_add` (a window splits into two), `wv_lt`, `wv_congr`, `wv_limbAt` (the limbs of a number)
  and `wv_digit` (a limb of a window).
- `putLimbs`: its bytes (`byteAt_putLimbs_out`, `limbsAt_putLimbs`), `eq_putLimbs` (a memory
  of the right size that holds the limbs and agrees elsewhere is it), `putLimbs_self` and
  `store8_putLimbs` (a store over a limb is a `List.set`).
- `load_lf`, `store_lf`, `limb_lit`: what the exported code's `limb(p, i)`, `mloadInt` and
  `mstoreInt` do on such memory.
- `limbAt_shl`, `limbAt_shr`: the limbs of `V * 2 ^ s` and `V / 2 ^ s` from those of `V`, as
  the normalising and denormalising loops compute them.
-/

open Ethereum Fe Fe.EVM Reasoning.Theory

namespace FeProofs.Modexp

open FeProofs.Precompiles
open Precompiles.Exported.Shared Precompiles.Exported.Modexp

/-! ## Windows of limbs -/

/-- The number of the limbs `[a, a + k)` of `f`, least significant first. -/
def wv (f : ℕ → Limb) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => wv f a k + 2 ^ (64 * k) * (f (a + k)).val

theorem wv_zero (f : ℕ → Limb) (a : ℕ) : wv f a 0 = 0 := rfl

theorem wv_succ (f : ℕ → Limb) (a k : ℕ) :
    wv f a (k + 1) = wv f a k + 2 ^ (64 * k) * (f (a + k)).val := rfl

theorem wv_one (f : ℕ → Limb) (a : ℕ) : wv f a 1 = (f a).val := by
  rw [wv_succ, wv_zero]; simp

theorem wv_lt (f : ℕ → Limb) (a : ℕ) : ∀ k, wv f a k < 2 ^ (64 * k)
  | 0 => by simp [wv]
  | k + 1 => by
    have := wv_lt f a k; have := (f (a + k)).isLt
    rw [wv_succ, show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
    nlinarith

theorem wv_add (f : ℕ → Limb) (a k : ℕ) :
    ∀ m, wv f a (k + m) = wv f a k + 2 ^ (64 * k) * wv f (a + k) m
  | 0 => by simp [wv]
  | m + 1 => by
    rw [← Nat.add_assoc, wv_succ, wv_add f a k m, wv_succ, show a + (k + m) = a + k + m by ring,
      show 64 * (k + m) = 64 * k + 64 * m by ring, pow_add]
    ring

/-- The low limb, then the rest. -/
theorem wv_low (f : ℕ → Limb) (a k : ℕ) : wv f a (k + 1) = (f a).val + 2 ^ 64 * wv f (a + 1) k := by
  rw [Nat.add_comm k 1, wv_add, wv_one]

theorem wv_congr {f g : ℕ → Limb} {a : ℕ} :
    ∀ {k}, (∀ i < k, f (a + i) = g (a + i)) → wv f a k = wv g a k
  | 0, _ => rfl
  | k + 1, h => by rw [wv_succ, wv_succ, wv_congr (fun i hi => h i (by omega)), h k (by omega)]

/-- A change apart from a window leaves it. -/
theorem wv_update_out (f : ℕ → Limb) {a k j : ℕ} (hj : j < a ∨ a + k ≤ j) (x : Limb) :
    wv (Function.update f j x) a k = wv f a k :=
  wv_congr fun i hi => by rw [Function.update_of_ne (by omega)]

/-- **The limbs of a number** `N`, from limb `a`. -/
theorem wv_limbAt (N a : ℕ) : ∀ k, wv (limbAt N) a k = N / 2 ^ (64 * a) % 2 ^ (64 * k)
  | 0 => by simp [wv, Nat.mod_one]
  | k + 1 => by
    rw [wv_succ, wv_limbAt N a k, show 64 * (k + 1) = 64 * k + 64 by ring, pow_add, Nat.mod_mul,
      Nat.div_div_eq_div_mul, ← pow_add, limbAt, show 64 * a + 64 * k = 64 * (a + k) by ring]

/-- **Limb `i` of a window.** -/
theorem wv_digit (f : ℕ → Limb) (a k i : ℕ) (hi : i < k) :
    wv f a k / 2 ^ (64 * i) % 2 ^ 64 = (f (a + i)).val := by
  obtain ⟨m, rfl⟩ : ∃ m, k = i + (m + 1) := ⟨k - i - 1, by omega⟩
  rw [wv_add, wv_low, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (wv_lt f a i),
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (f (a + i)).isLt]

/-- A window whose number is `N` holds the limbs of `N`. -/
theorem eq_limbAt_of_wv {f : ℕ → Limb} {a k N : ℕ} (h : wv f a k = N) {i : ℕ} (hi : i < k) :
    f (a + i) = limbAt N i :=
  Fin.ext (by rw [← wv_digit f a k i hi, h]; rfl)

/-! ## The first limbs of a function, in memory -/

/-- The first `K` limbs of `f`. -/
def lf (f : ℕ → Limb) (K : ℕ) : List Limb := List.ofFn fun i : Fin K => f i

@[simp] theorem lf_length (f : ℕ → Limb) (K : ℕ) : (lf f K).length = K := List.length_ofFn

theorem lf_get (f : ℕ → Limb) {K i : ℕ} (hi : i < K) : (lf f K)[i]'(by simpa using hi) = f i :=
  List.getElem_ofFn _

theorem lf_set (f : ℕ → Limb) {K i : ℕ} (x : Limb) :
    (lf f K).set i x = lf (Function.update f i x) K := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  rw [List.getElem_set, lf_get _ (by simpa using h2), lf_get _ (by simpa using h2)]
  by_cases hk : i = k
  · subst hk; simp
  · rw [ite_eq_right hk, Function.update_of_ne (Ne.symm hk)]

theorem lf_succ (f : ℕ → Limb) (K : ℕ) : lf f (K + 1) = lf f K ++ [f K] := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [lf_length] at h1
  rw [lf_get _ h1]
  by_cases hk : k < K
  · rw [List.getElem_append_left (by simpa using hk), lf_get _ hk]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [lf_length, List.getElem_singleton]
    congr 1; omega

theorem val_lf (f : ℕ → Limb) : ∀ K, val (lf f K) = wv f 0 K
  | 0 => rfl
  | K + 1 => by
    rw [lf_succ, val_append, val_lf f K, lf_length, wv_succ, Nat.zero_add]
    simp [val]

theorem lf_congr {f g : ℕ → Limb} {K : ℕ} (h : ∀ i < K, f i = g i) : lf f K = lf g K := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [lf_length] at h1
  rw [lf_get _ h1, lf_get _ h1, h k h1]

/-- `lf` of the limbs of `N` is `limbsOf`. -/
theorem lf_limbAt (N K : ℕ) : lf (limbAt N) K = limbsOf N K := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [lf_length] at h1
  rw [lf_get _ h1, limbsOf_get N K k h1]

/-- Memory `mem` with the limbs `ls` written at `p`. -/
def putLimbs (mem : ByteArray) (p : ℕ) (ls : List Limb) : ByteArray :=
  (limbBytes ls).write 0 mem p (8 * ls.length)

theorem putLimbs_size {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : p + 8 * ls.length ≤ mem.size) :
    (putLimbs mem p ls).size = mem.size :=
  write_size_from _ _ _ _ _ (by simp) h

theorem byteAt_putLimbs_out {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : p + 8 * ls.length ≤ mem.size)
    {j : ℕ} (hj : j < p ∨ p + 8 * ls.length ≤ j) : byteAt (putLimbs mem p ls) j = byteAt mem j := by
  rw [putLimbs, byteAt_write_from _ _ _ _ _ _ (by simp) h, ite_eq_right (by omega)]

theorem limbsAt_putLimbs {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : p + 8 * ls.length ≤ mem.size) :
    LimbsAt (putLimbs mem p ls) p ls := by
  have hz : LimbsAt (limbBytes ls) 0 ls := by
    have := limbsAt_limbBytes ByteArray.empty ls
    rwa [ByteArray.empty_append, ByteArray.size_empty] at this
  exact hz.write_same h

/-- A byte of a limb that memory holds. -/
theorem byte_of_limbsAt {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls) {i r : ℕ}
    (hi : i < ls.length) (hr : r < 8) :
    byteAt mem (p + 8 * i + r) = ls[i].val / 2 ^ (8 * (7 - r)) % 256 := by
  have e := beAt_digit mem (p + 8 * i) 8 (7 - r)
  rw [ite_eq_left (by omega), h.2 i hi] at e
  rw [e]; congr 1; omega

/-- **Memory with the limbs written**: a memory of the same size that holds `ls` at `p` and
    agrees with `mem` elsewhere. -/
theorem eq_putLimbs {mem mem' : ByteArray} {p : ℕ} {ls : List Limb} (hs : mem'.size = mem.size)
    (h : LimbsAt mem' p ls) (ho : ∀ j, j < p ∨ p + 8 * ls.length ≤ j → byteAt mem' j = byteAt mem j) :
    mem' = putLimbs mem p ls := by
  have hb := h.1
  apply ext_byteAt (by rw [putLimbs_size (by omega)]; exact hs)
  intro j _
  by_cases hj : j < p ∨ p + 8 * ls.length ≤ j
  · rw [ho j hj, byteAt_putLimbs_out (by omega) hj]
  · obtain ⟨i, r, hi, hr, rfl⟩ : ∃ i r, i < ls.length ∧ r < 8 ∧ j = p + 8 * i + r :=
      ⟨(j - p) / 8, (j - p) % 8, by omega, by omega, by omega⟩
    rw [byte_of_limbsAt h hi hr, byte_of_limbsAt (limbsAt_putLimbs (by omega)) hi hr]

/-- Writing the limbs memory holds changes nothing. -/
theorem putLimbs_self {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : LimbsAt mem p ls) :
    putLimbs mem p ls = mem :=
  (eq_putLimbs rfl h (fun _ _ => rfl)).symm

/-- **A store over limb `i`.** -/
theorem store8_putLimbs {mem : ByteArray} {p : ℕ} {ls : List Limb} (h : p + 8 * ls.length ≤ mem.size)
    {i : ℕ} (hi : i < ls.length) (x : Limb) :
    store8 (putLimbs mem p ls) (p + 8 * i) x = putLimbs mem p (ls.set i x) := by
  have hL := limbsAt_putLimbs h
  have hs := putLimbs_size h
  apply eq_putLimbs (by rw [store8_size x (by omega), hs]) (hL.store hi x)
  intro j hj
  rw [List.length_set] at hj
  rw [byteAt_store8 x (by omega), ite_eq_right (by omega), byteAt_putLimbs_out h hj]

/-- Writes at `p` of the same number of limbs: the last one counts. -/
theorem putLimbs_putLimbs {mem : ByteArray} {p : ℕ} {ls ks : List Limb}
    (h : p + 8 * ls.length ≤ mem.size) (hl : ks.length = ls.length) :
    putLimbs (putLimbs mem p ls) p ks = putLimbs mem p ks := by
  have hs := putLimbs_size h
  apply eq_putLimbs (by rw [putLimbs_size (by omega), hs]) (limbsAt_putLimbs (by omega))
  intro j hj
  rw [byteAt_putLimbs_out (by omega) hj, byteAt_putLimbs_out h (by omega)]

/-- Limbs apart from the written ones stay. -/
theorem LimbsAt.putLimbs_other {mem : ByteArray} {q : ℕ} {ms : List Limb} (hm : LimbsAt mem q ms)
    {p : ℕ} {ls : List Limb} (h : p + 8 * ls.length ≤ mem.size)
    (hd : p + 8 * ls.length ≤ q ∨ q + 8 * ms.length ≤ p) : LimbsAt (putLimbs mem p ls) q ms :=
  hm.write_other (by simp) h hd

/-! ## The exported code's reads and writes of limbs -/

/-- `limb(p, i)`, the address of limb `i`. -/
theorem limb_lit (p : UInt256) {i : ℕ} (h : p.toNat + 8 * i < UInt256.size) :
    Exported.Modexp.limb p (UInt256.ofNat i) = pure (UInt256.ofNat (p.toNat + 8 * i)) := by
  simp only [Exported.Modexp.limb, limb_eq p h]

/-- **A read of limb `i`** of memory holding the first `K` limbs of `f`. -/
theorem load_lf {w : World} {M : ByteArray} {p K : ℕ} (f : ℕ → Limb) (hK : p + 8 * K ≤ M.size)
    (hs : M.size < UInt256.size) {i : ℕ} (hi : i < K) (I : Env) :
    (mloadInt (.u 64) (UInt256.ofNat (p + 8 * i))).exec I { w with memory := putLimbs M p (lf f K) } =
      some (.ok ((f i).w, { w with memory := putLimbs M p (lf f K) })) := by
  have hK' : p + 8 * (lf f K).length ≤ M.size := by simpa using hK
  have hL := limbsAt_putLimbs hK'
  have := load_exec (w := { w with memory := putLimbs M p (lf f K) }) hL
    (i := i) (by simpa using hi) (by rw [putLimbs_size hK']; exact hs) I
  rwa [lf_get f hi] at this

/-- **A write of limb `i`.** -/
theorem store_lf {w : World} {M : ByteArray} {p K : ℕ} (f : ℕ → Limb) (hK : p + 8 * K ≤ M.size)
    (hs : M.size < UInt256.size) {i : ℕ} (hi : i < K) (x : Limb) (I : Env) :
    (mstoreInt (.u 64) (UInt256.ofNat (p + 8 * i)) x.w).exec I { w with memory := putLimbs M p (lf f K) } =
      some (.ok ((), { w with memory := putLimbs M p (lf (Function.update f i x) K) })) := by
  have hK' : p + 8 * (lf f K).length ≤ M.size := by simpa using hK
  rw [store_exec (by omega), store8_putLimbs hK' (by simpa using hi), lf_set f]

/-! ## Shifts of limbs -/

/-- **A limb of `V * 2 ^ s`**, `0 < s < 64`, from limbs `i` and `i - 1` of `V`. -/
theorem limbAt_shl (V : ℕ) {s i : ℕ} (hs : 0 < s) (hs' : s < 64) (hi : 1 ≤ i) :
    (limbAt V i).val * 2 ^ s % 2 ^ 64 ||| (limbAt V (i - 1)).val / 2 ^ (64 - s) =
      (limbAt (V * 2 ^ s) i).val := by
  simp only [limbAt]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_lor, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hk : k < 64
  · by_cases hsk : s ≤ k
    · rw [show k - s + 64 * i = k + 64 * i - s by omega]
      simp [hk, hsk, show k - s < 64 by omega, show ¬ (k + (64 - s) < 64) by omega,
        show s ≤ k + 64 * i by omega]
    · rw [show k + (64 - s) + 64 * (i - 1) = k + 64 * i - s by omega]
      simp [hk, hsk, show k + (64 - s) < 64 by omega, show s ≤ k + 64 * i by omega]
  · simp [hk, show ¬ (k + (64 - s) < 64) by omega]

/-- Limb `0` of `V * 2 ^ s`. -/
theorem limbAt_shl_zero (V s : ℕ) : (limbAt V 0).val * 2 ^ s % 2 ^ 64 = (limbAt (V * 2 ^ s) 0).val := by
  simp only [limbAt, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [Nat.mod_mul_mod]

/-- **A limb of `V / 2 ^ s`**, `0 < s < 64`, from limbs `i` and `i + 1` of `V`. -/
theorem limbAt_shr (V : ℕ) {s : ℕ} (hs : 0 < s) (hs' : s < 64) (i : ℕ) :
    (limbAt V i).val / 2 ^ s ||| (limbAt V (i + 1)).val * 2 ^ (64 - s) % 2 ^ 64 =
      (limbAt (V / 2 ^ s) i).val := by
  simp only [limbAt]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_lor, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hk : k < 64
  · by_cases hsk : k + s < 64
    · rw [show k + s + 64 * i = k + 64 * i + s by omega]
      simp [hk, hsk]
    · rw [show k - (64 - s) + 64 * (i + 1) = k + 64 * i + s by omega]
      simp [hk, hsk, show 64 - s ≤ k by omega, show k - (64 - s) < 64 by omega]
  · simp [hk, show ¬ (k + s < 64) by omega]

/-! ## Word operations -/

theorem shl64_lit (x : Limb) {s : ℕ} (hs : s < 256) :
    IntTy.shl (.u 64) x.w (UInt256.ofNat s) = UInt256.ofNat (x.val * 2 ^ s % 2 ^ 64) := by
  simp only [IntTy.shl, val_u, Limb.toNat_w, toNat_lit (show s < 2 ^ 256 by omega),
    show ¬ (256 ≤ s) by omega, ite_false]
  rw [show ((x.val : ℤ) * 2 ^ s) = ((x.val * 2 ^ s : ℕ) : ℤ) by push_cast; ring, wrap_u_nat]

theorem lor_lit {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.ofNat a ||| UInt256.ofNat b = UInt256.ofNat (a ||| b) := by
  apply word_eq_of_toNat
  change (UInt256.lor _ _).toNat = _
  rw [u256_lor_toNat_exact, toNat_lit ha, toNat_lit hb, toNat_lit (Nat.or_lt_two_pow ha hb)]

theorem sub64_checked {a b : ℕ} (ha : a < 2 ^ 64) (h : b ≤ a) :
    IntTy.sub (.u 64) (UInt256.ofNat a) (UInt256.ofNat b) = pure (UInt256.ofNat (a - b)) := by
  simp only [IntTy.sub, IntTy.checked, IntTy.Fits, val_u, toNat_lit (show a < 2 ^ 256 by omega),
    toNat_lit (show b < 2 ^ 256 by omega)]
  rw [ite_eq_left (by omega), show ((a : ℤ) - b) = ((a - b : ℕ) : ℤ) by omega, wrap_u_nat,
    Nat.mod_eq_of_lt (by omega)]

end FeProofs.Modexp
