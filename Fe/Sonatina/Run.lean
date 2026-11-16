import Fe.Sonatina.CheckCert
import Fe.EVM.Entry
import Reasoning.Memory

/-!
# Running the machine IR of a contract

Lemmas for running a function of the machine IR on a call by `simp`, block by block: `ir_step`
unfolds `runBlocks` once and simplifies the block it is at, found by the block lemmas
`sonatina_func` makes, with the interpreter's definitions, the model library's primitives and
the memory lemmas below.  A contract's run lemmas give it the facts of the call
(`calldata_facts` for an arm's head check) and apply it once per block on the path.
-/

namespace Fe.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory

/-- `2 ^ 256`, as `simp` leaves it. -/
local notation "size256" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The word 0 in the form `ir_step` leaves it. -/
theorem ofNat_zero_eq : UInt256.ofNat 0 = ⟨0⟩ := rfl

/-- A word's value modulo `2 ^ 256`, as `simp` meets it once `UInt256.size` is a literal. -/
theorem toNat_mod (u : UInt256) : u.toNat % size256 = u.toNat :=
  Nat.mod_eq_of_lt u.val.isLt

/-- The selector word of calldata, as the IR computes it with `shr`. -/
theorem selWord_toNat (cd : ByteArray) :
    (selWord cd).toNat = (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 := by
  have h := Check.shr_word (x := 224) (y := (uInt256OfByteArray (cd.readBytes 0 32)).toNat)
    (by decide) (UInt256.val _).isLt
  rw [Reasoning.Theory.u256_ofNat_toNat] at h
  rw [selWord, show (⟨224⟩ : UInt256) = UInt256.ofNat 224 from rfl, h, ite_eq_right (by decide)]
  exact Check.toNat_ofNat_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt256.val _).isLt)

/-- The exported dispatcher's selector test, as the machine IR's `br_table` makes it. -/
theorem selWord_eq_iff {cd : ByteArray} {k : Nat} (hk : k < UInt256.size) :
    selWord cd = UInt256.ofNat k ↔ (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 = k := by
  rw [← selWord_toNat]
  constructor
  · intro h; rw [h, Check.toNat_ofNat_lt hk]
  · intro h; exact Check.eq_of_toNat (by rw [h, Check.toNat_ofNat_lt hk])

/-- A word of a value is the word of the value modulo `2 ^ 256`. -/
theorem ofNat_mod (n : Nat) : UInt256.ofNat (n % size256) = UInt256.ofNat n :=
  Check.eq_of_toNat (by simp [Check.toNat_ofNat, UInt256.size])

/-- The machine IR's `sub` of two words, as a word. -/
theorem wrap_sub_word (a b : UInt256) :
    UInt256.ofNat (wrap 256 ((a.toNat : Int) - (b.toNat : Int))) = UInt256.sub a b := by
  have := Check.sub_word (x := a.toNat) (y := b.toNat) a.val.isLt b.val.isLt
  rw [Reasoning.Theory.u256_ofNat_toNat, Reasoning.Theory.u256_ofNat_toNat] at this
  exact this.symm

/-- The machine IR's `add` of two words, as a word. -/
theorem wrap_add_word (a b : UInt256) :
    UInt256.ofNat (wrap 256 ((a.toNat : Int) + (b.toNat : Int))) = a + b := by
  have := Check.add_word a.toNat b.toNat
  rw [Reasoning.Theory.u256_ofNat_toNat, Reasoning.Theory.u256_ofNat_toNat] at this
  rw [this]

/-- A wrapped value is below `2 ^ 256`. -/
theorem wrap_mod (n : Int) : wrap 256 n % size256 = wrap 256 n := by
  simp only [wrap]; omega

/-- The machine IR's overflow test of an `add`, `lt (a + b) a`, is the checked one's. -/
theorem wrap_add_lt (a b : UInt256) :
    wrap 256 ((a.toNat : Int) + (b.toNat : Int)) < a.toNat ↔ UInt256.size ≤ a.toNat + b.toNat := by
  have ha := a.val.isLt; have hb := b.val.isLt
  change a.toNat < UInt256.size at ha; change b.toNat < UInt256.size at hb
  simp only [wrap]; rw [Check.size_eq] at ha hb ⊢
  omega

/-- The machine IR's `add` of two words, as the value a later instruction reads.  Not in
    `ir_step`'s set: pass it, with `add_toNat_lt`, where a sum is an operand of a later block. -/
theorem wrap_add_toNat (a b : UInt256) :
    wrap 256 ((a.toNat : Int) + (b.toNat : Int)) = (a + b).toNat := by
  rw [← wrap_add_word, Check.toNat_ofNat_lt]
  have := wrap_mod ((a.toNat : Int) + (b.toNat : Int))
  simp only [wrap, UInt256.size] at this ⊢
  omega

/-- The overflow test of an `add` whose sum `wrap_add_toNat` made a word. -/
theorem add_toNat_lt (a b : UInt256) :
    (a + b).toNat < a.toNat ↔ UInt256.size ≤ a.toNat + b.toNat := by
  rw [← wrap_add_toNat]
  exact wrap_add_lt a b

/-- A word shifted right, below `2 ^ 256`. -/
theorem shr_mod (u : UInt256) (k : Nat) : u.toNat >>> k % size256 = u.toNat >>> k :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) u.val.isLt)

/-- Std's address check, as the machine IR's `shr 160` makes it. -/
theorem notAddress_iff (v : UInt256) : NotAddress v ↔ v.toNat >>> 160 ≠ 0 := by
  unfold NotAddress
  rw [Nat.shiftRight_eq_div_pow]
  constructor
  · intro h; exact Nat.pos_iff_ne_zero.mp (Nat.div_pos h (by positivity))
  · intro h; by_contra hn; exact h (Nat.div_eq_of_lt (by omega))

/-- The selector word of calldata as the IR computes it, below `2 ^ 256`. -/
theorem sel_mod (cd : ByteArray) : (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 %
    size256 = (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt256.val _).isLt)

/-- The facts of a calldata size `n` that holds a selector, as `simp` meets them in an arm's
    head check `n - 4 <s k`. -/
theorem calldata_facts {n : Nat} (hsz : 4 ≤ n) (hfits : n < 2 ^ 64) :
    n % size256 = n ∧ (n : Int) % size256 = n ∧ wrap 256 ((n : Int) - 4) = n - 4 ∧
      (n - 4) % size256 = n - 4 ∧ signed 256 (n - 4) = (n : Int) - 4 ∧ ¬ n < 4 := by
  refine ⟨by omega, by omega, by simp only [wrap]; omega, by omega, ?_, by omega⟩
  simp only [signed]
  split <;> omega

/-- A value below `2 ^ (bits - 1)` is itself as a signed integer. -/
@[simp] theorem signed_of_lt {bits v : Nat} (h : v < 2 ^ (bits - 1)) : signed bits v = v := by
  simp [signed, h]

/-- A copy of `len` bytes from offset `so` of `src` is a copy of that window from its start: the
    shape `codecopy` and `calldatacopy` leave in memory, for the read-back lemmas of writes from
    offset 0. -/
theorem write_window (src base : ByteArray) (so d len : ℕ) (hlen : len ≠ 0)
    (hsrc : so + len ≤ src.size) :
    src.write so base d len = (src.extract so (so + len)).write 0 base d len := by
  have hs : (src.extract so (so + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [ite_eq_right hlen, ite_eq_right hlen, ite_eq_right (by omega), ite_eq_right (by omega), hs]
  have hz : (ByteArray.zeroes (min base.size (d + len) - (d + len))).data = #[] := by
    rw [show min base.size (d + len) - (d + len) = 0 by omega,
      Reasoning.Theory.zeroes_zero (n := 0) (by rfl)]; rfl
  have hd : src.data.size = src.size := rfl
  simp only [ByteArray.data_copySlice, ByteArray.data_append,
    show min len (src.size - so) = len by omega, show min len (len - 0) = len by omega, hz,
    Array.append_empty, hd, Nat.zero_add]
  rw [show min base.size (d + len) - (d + len) = 0 by omega, Nat.add_zero,
    show (src.extract so (so + len)).data.size - 0 = len from hs, Nat.min_self,
    show min len (src.size - so) = len by omega, ByteArray.data_extract, Array.extract_extract]
  simp

/-! ## Memory the machine IR writes and reads back

The machine IR stores at constant addresses: a map's key and root at 0 and 32 for `keccak256`
(`pair_slot`), a word at 0 to return or log it (`toByteArray_write32_read_back`), the words of
an `Error(string)` payload one after another (`storeWords_read`), and the selector and code of a
panic at 0 and 4 (`panic_read`). -/

/-- A word written at `off` of memory that reaches `off`: the memory as the bytes before, the
    word's, and the bytes after. -/
theorem write_word (mem : ByteArray) (v : UInt256) {off : Nat} (h : off ≤ mem.size) :
    v.toByteArray.write 0 mem off 32 =
      mem.extract 0 off ++ v.toByteArray ++ mem.extract (off + 32) mem.size := by
  rw [write32_eq _ _ off (by rw [toByteArray_size]) h, toByteArray_extract_all]

/-- Two words stored at 0 and 32, as the machine IR stores a map's key and root, read back as
    64 bytes. -/
theorem pair_read (mem : ByteArray) (a b : UInt256) :
    (b.toByteArray.write 0 (a.toByteArray.write 0 mem 0 32) 32 32).readWithPadding 0 64 =
      a.toByteArray ++ b.toByteArray := by
  have ha := toByteArray_size a
  have hb := toByteArray_size b
  have h1 : (a.toByteArray.write 0 mem 0 32).size ≥ 32 :=
    toByteArray_write_size_ge_off_add32 _ _ 0 (by simp)
  rw [write_word _ b (by omega), write_word _ a (Nat.zero_le _)]
  rw [readWithPadding_eq_extract' _ 0 64 (by decide) (by decide)
    (by simp [ByteArray.size_append, ha, hb])]
  have he : mem.extract 0 0 = ByteArray.empty := ByteArray.ext (by simp)
  have hx : (a.toByteArray ++ mem.extract 32 mem.size).extract 0 32 = a.toByteArray := by
    rw [extract_append_left _ _ 0 32 (by rw [ha]), ← ha, byteArray_extract_self]
  rw [he, ByteArray.empty_append, Nat.zero_add, hx, Nat.zero_add]
  exact byteArray_extract_two_chunks_0 _ _ _ ha hb

/-- The slot the machine IR hashes a map's key and root into, as `mapSlot` gives it. -/
theorem pair_slot (mem : ByteArray) (key root : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian (KEC ((root.toByteArray.write 0
      (key.toByteArray.write 0 mem 0 32) 32 32).readWithPadding 0 64))) = mapSlot key root := by
  rw [pair_read, mappingSlot_single]; rfl

/-- A map's key and root stored at `off` and `off + 32` of memory that reaches `off` hash to
    `mapSlot`, as a constructor stores them above its argument. -/
theorem pair_slot_at (mem : ByteArray) (key root : UInt256) {off off2 : Nat}
    (h : off ≤ mem.size) (h2 : off2 = off + 32) :
    UInt256.ofNat (fromByteArrayBigEndian (KEC ((root.toByteArray.write 0
      (key.toByteArray.write 0 mem off 32) off2 32).readWithPadding off 64))) =
      mapSlot key root := by
  subst h2
  have hk := toByteArray_size key
  have hr := toByteArray_size root
  have hP : (mem.extract 0 off).size = off := by rw [ByteArray.size_extract]; omega
  have h1 := write_word mem key h
  have hs : off + 32 ≤ (key.toByteArray.write 0 mem off 32).size := by
    rw [h1, ByteArray.size_append, ByteArray.size_append, hP, hk]; omega
  have hx : (key.toByteArray.write 0 mem off 32).extract 0 (off + 32) =
      mem.extract 0 off ++ key.toByteArray := by
    rw [h1, extract_append_left _ _ 0 (off + 32) (by rw [ByteArray.size_append, hP, hk]),
      show off + 32 = (mem.extract 0 off ++ key.toByteArray).size by
        rw [ByteArray.size_append, hP, hk], byteArray_extract_self]
  rw [write_word _ root hs, hx, readWithPadding_eq_extract' _ off 64 (by decide) (by decide)
      (by simp only [ByteArray.size_append, hP, hk, hr]; omega),
    ByteArray.append_assoc, ByteArray.append_assoc,
    extract_append_right_window _ _ _ _ (by omega), hP, Nat.sub_self, Nat.add_sub_cancel_left,
    ← ByteArray.append_assoc, byteArray_extract_two_chunks_0 _ _ _ hk hr, mappingSlot_single]
  rfl

/-- Words stored one after another from `base`. -/
def storeWords (mem : ByteArray) (base : Nat) : List UInt256 → ByteArray
  | [] => mem
  | v :: vs => storeWords (v.toByteArray.write 0 mem base 32) (base + 32) vs

/-- The bytes of words, one after another. -/
def wordBytes : List UInt256 → ByteArray
  | [] => .empty
  | v :: vs => v.toByteArray ++ wordBytes vs

theorem wordBytes_size : ∀ vs : List UInt256, (wordBytes vs).size = 32 * vs.length
  | [] => rfl
  | v :: vs => by
    simp only [wordBytes, ByteArray.size_append, toByteArray_size, wordBytes_size vs,
      List.length_cons]
    omega

theorem storeWords_eq : ∀ (vs : List UInt256) (mem : ByteArray) (base : Nat), base ≤ mem.size →
    ∃ rest, storeWords mem base vs = mem.extract 0 base ++ wordBytes vs ++ rest
  | [], mem, base, h => ⟨mem.extract base mem.size, by
      simp only [storeWords, wordBytes, ByteArray.append_empty]
      apply ByteArray.ext
      simp only [ByteArray.data_append, ByteArray.data_extract]
      rw [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
        Nat.max_eq_right h]
      exact Array.extract_size.symm⟩
  | v :: vs, mem, base, h => by
    have hP : (mem.extract 0 base).size = base := by rw [ByteArray.size_extract]; omega
    have hv := toByteArray_size v
    have hw := write_word mem v h
    have h' : base + 32 ≤ (v.toByteArray.write 0 mem base 32).size := by
      rw [hw, ByteArray.size_append, ByteArray.size_append, hP, hv]; omega
    obtain ⟨rest, hr⟩ := storeWords_eq vs _ (base + 32) h'
    refine ⟨rest, ?_⟩
    have hx : (v.toByteArray.write 0 mem base 32).extract 0 (base + 32) =
        mem.extract 0 base ++ v.toByteArray := by
      rw [hw, extract_append_left _ _ 0 (base + 32)
        (by rw [ByteArray.size_append, hP, hv]),
        show base + 32 = (mem.extract 0 base ++ v.toByteArray).size by
          rw [ByteArray.size_append, hP, hv], byteArray_extract_self]
    simp only [storeWords, wordBytes]
    rw [hr, hx]
    simp only [ByteArray.append_assoc]

/-- Words stored one after another from `base` read back from it, as the machine IR returns or
    reverts with them. -/
theorem storeWords_read (vs : List UInt256) {mem : ByteArray} {base len : Nat}
    (h : base ≤ mem.size) (hpos : 0 < len) (hlen : len ≤ 32 * vs.length) (h64 : len < 2 ^ 64) :
    (storeWords mem base vs).readWithPadding base len = (wordBytes vs).extract 0 len := by
  obtain ⟨rest, hr⟩ := storeWords_eq vs mem base h
  have hP : (mem.extract 0 base).size = base := by rw [ByteArray.size_extract]; omega
  have hW := wordBytes_size vs
  rw [hr, readWithPadding_eq_extract' _ _ _ hpos h64
      (by simp only [ByteArray.size_append, hP, hW]; omega),
    ByteArray.append_assoc, extract_append_right_window _ _ _ _ (by omega), hP, Nat.sub_self,
    Nat.add_sub_cancel_left, extract_append_left _ _ _ _ (by omega)]

/-- An `Error(string)` payload as the machine IR reverts with it: four words stored from 64,
    after a map's key and root at 0 and 32, read back as 100 bytes. -/
theorem error_read (mem : ByteArray) (a b w0 w1 w2 w3 : UInt256) :
    (w3.toByteArray.write 0 (w2.toByteArray.write 0 (w1.toByteArray.write 0
      (w0.toByteArray.write 0 (b.toByteArray.write 0 (a.toByteArray.write 0 mem 0 32) 32 32)
        64 32) 96 32) 128 32) 160 32).readWithPadding 64 100 =
      (wordBytes [w0, w1, w2, w3]).extract 0 100 := by
  have h1 : (a.toByteArray.write 0 mem 0 32).size ≥ 32 :=
    toByteArray_write_size_ge_off_add32 _ _ 0 (by simp)
  have h2 : 64 ≤ (b.toByteArray.write 0 (a.toByteArray.write 0 mem 0 32) 32 32).size :=
    toByteArray_write_size_ge_off_add32 _ _ 32 (lt_of_le_of_lt (Nat.sub_le_sub_left h1 32)
      (by simp))
  exact storeWords_read [w0, w1, w2, w3] h2 (by decide) (by simp) (by decide)

/-- The selector of `Panic(uint256)` stored at 0 and the code at 4, read back as 36 bytes: the
    payload `revert_error` of a panic reverts with. -/
theorem panic_read (mem : ByteArray) (c : UInt256) :
    (c.toByteArray.write 0 ((UInt256.ofNat
      35408467139433450592217433187231851964531694900788300625387963629091585785856
      ).toByteArray.write 0 mem 0 32) 4 32).readWithPadding 0 36 = panicData c.toNat := by
  set S := (UInt256.ofNat
    35408467139433450592217433187231851964531694900788300625387963629091585785856).toByteArray
  have hS : S.size = 32 := toByteArray_size _
  have hc := toByteArray_size c
  have he : mem.extract 0 0 = ByteArray.empty := ByteArray.ext (by simp)
  have h1 := write_word mem (UInt256.ofNat
    35408467139433450592217433187231851964531694900788300625387963629091585785856) (Nat.zero_le _)
  rw [he, ByteArray.empty_append] at h1
  have hsz : 4 ≤ (S.write 0 mem 0 32).size := by
    rw [h1, ByteArray.size_append, hS]; omega
  rw [write_word _ c hsz, h1]
  have hx : (S ++ mem.extract (0 + 32) mem.size).extract 0 4 = ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ := by
    rw [extract_append_left _ _ 0 4 (by omega)]
    decide +kernel
  have h4 : (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ : ByteArray).size = 4 := rfl
  rw [hx, readWithPadding_eq_extract' _ 0 36 (by decide) (by decide)
      (by simp only [ByteArray.size_append, hc, h4]; omega), extract_append_left _ _ 0 36
      (by rw [ByteArray.size_append, hc, h4]),
    show (36 : Nat) = (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ c.toByteArray : ByteArray).size by
      rw [ByteArray.size_append, hc, h4], byteArray_extract_self, panicData,
    u256_ofNat_toNat]

/-- A word written at `off` below `2 ^ 32` reads back, whatever the memory's size: a write past
    the end extends memory with zeros first. -/
theorem word_read_gap (mem : ByteArray) (v : UInt256) {off : Nat} (h : off < 2 ^ 32) :
    (v.toByteArray.write 0 mem off 32).readWithPadding off 32 = v.toByteArray :=
  toByteArray_write_read_back_of_gap v mem off
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ h))

/-- Two words stored at `off` and `off + 32`, read back as 64 bytes, whatever the memory's
    size: the machine IR stores a map's key and root in its arena, above the free pointer. -/
theorem pair_read_gap (mem : ByteArray) (key root : UInt256) {off off2 : Nat}
    (h : off2 < 2 ^ 32) (h2 : off2 = off + 32) :
    (root.toByteArray.write 0 (key.toByteArray.write 0 mem off 32) off2 32).readWithPadding
      off 64 = key.toByteArray ++ root.toByteArray := by
  subst h2
  have hgap : ∀ (M : ByteArray) (o : Nat), o < 2 ^ 32 → o - M.size < USize.size :=
    fun M o ho => lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ ho)
  have h1 := toByteArray_write_size_ge_off_add32 key mem off (hgap _ _ (by omega))
  have h2 := toByteArray_write_size_ge_off_add32 root (key.toByteArray.write 0 mem off 32)
    (off + 32) (hgap _ _ (by omega))
  rw [show (64 : Nat) = 32 + 32 from rfl, byteArray_readWithPadding_split _ off 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega),
    toByteArray_write_read_below_of_gap _ _ _ _ h1 (le_refl _) (hgap _ _ (by omega)),
    toByteArray_write_read_back_of_gap _ _ _ (hgap _ _ (by omega)),
    toByteArray_write_read_back_of_gap _ _ _ (hgap _ _ h)]

/-- The slot the machine IR hashes a map's key and root into from its arena at `off`, as
    `mapSlot` gives it. -/
theorem pair_slot_gap (mem : ByteArray) (key root : UInt256) {off off2 : Nat}
    (h : off2 < 2 ^ 32) (h2 : off2 = off + 32) :
    UInt256.ofNat (fromByteArrayBigEndian (KEC ((root.toByteArray.write 0
      (key.toByteArray.write 0 mem off 32) off2 32).readWithPadding off 64))) =
      mapSlot key root := by
  rw [pair_read_gap mem key root h h2, mappingSlot_single]; rfl

/-- The selector of `Panic(uint256)` stored at `off` and the code at `off + 4`, read back as 36
    bytes, whatever the memory's size: the payload of a `revert_error` that stores in its arena. -/
theorem panic_read_gap (mem : ByteArray) (c : UInt256) {off off4 : Nat} (h : off + 36 < 2 ^ 32)
    (h4 : off4 = off + 4) :
    (c.toByteArray.write 0 ((UInt256.ofNat
      35408467139433450592217433187231851964531694900788300625387963629091585785856
      ).toByteArray.write 0 mem off 32) off4 32).readWithPadding off 36 = panicData c.toNat := by
  subst h4
  have hgap : ∀ (M : ByteArray) (o : Nat), o < 2 ^ 32 → o - M.size < USize.size :=
    fun M o ho => lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ ho)
  have h1 := toByteArray_write_size_ge_off_add32 (UInt256.ofNat
      35408467139433450592217433187231851964531694900788300625387963629091585785856) mem off
    (hgap _ _ (by omega))
  have h2 := toByteArray_write_size_ge_off_add32 c ((UInt256.ofNat
      35408467139433450592217433187231851964531694900788300625387963629091585785856
      ).toByteArray.write 0 mem off 32) (off + 4) (hgap _ _ (by omega))
  rw [show (36 : Nat) = 4 + 32 from rfl, byteArray_readWithPadding_split _ off 4 32
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega),
    toByteArray_write_read_below_len_of_gap _ _ _ _ _ (by omega) (le_refl _) (by decide)
      (by decide) (hgap _ _ (by omega)),
    toByteArray_write_read_back_of_gap _ _ _ (hgap _ _ (by omega)),
    show off = off + 0 from rfl, toByteArray_write_read_window_of_gap _ _ _ 0 4 (by decide)
      (by decide) (by decide) (hgap _ _ (by omega)), panicData, u256_ofNat_toNat]
  congr 1
  decide +kernel

/-! ## Internal calls

`ir_step` does not run a callee: at a `call` statement it leaves the callee's run,
`(runFunc m ic "f" args).exec I w`, in the goal, its arguments evaluated
(`[Val.int 256 a.toNat, …]`).  A contract proves one lemma per callee, from any world and any
argument words, stating what that run returns or how it halts, and passes it to `ir_step` (in
its list or as a hypothesis, which `ir_step` uses too): each call site then rewrites with it
and goes on with the caller's next statement.  A callee lemma whose right side is an `if` (an
overflow check, a static call) needs its condition decided by a hypothesis in the form
`ir_step` leaves it, so that `simp` takes the branch before the caller's continuation.

The callee lemma holds of any module `m` whose function `f` is the callee's IR
(`m.func? "f" = some fFunc`); the section's own module satisfies it by `rfl`.  Its proof
starts at the callee's entry block by `runFunc_entry` and runs the callee's blocks by
`ir_step`. -/

/-- A call of function `name` of `m`: the function's blocks from its entry block, its parameters
    bound to the arguments. -/
theorem runFunc_entry {m : Module} {c : Ctx} {name : String} {f : Func} {eb : Block}
    {args : List Val} (hf : m.func? name = some f) (he : f.blocks.head? = some eb) :
    runFunc m c name args =
      (Fe.Sonatina.bind {} f.params args >>= fun env => runBlocks m c f env none eb.id) := by
  rw [runFunc_eq]
  simp only [hf, he]

/-- Unfold `runBlocks` once and simplify the block the run is at, with the interpreter's
    definitions, the model library's primitives, the local hypotheses and the extra lemmas.
    A call is left to a lemma about the callee (see above).
    `CharP.cast_eq_zero` is left out: on every cast of a word's value to `ℤ` it searches for a
    `CharP ℤ` instance, unfolding the word to compare it with `0`. -/
syntax "ir_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_step) => `(tactic| ir_step [])
  | `(tactic| ir_step [$ls,*]) => `(tactic| (rw [runBlocks_eq]; simp [enter,
      Fe.Sonatina.bind, runBody_cons_eq, runBody_nil_eq, runInst, EvmOp.run, evalPair, evalInt,
      evalOperand, evalWord, Fe.Sonatina.word, Val.as, Ty.bits, CmpOp.eval, BinOp.eval,
      Sonatina.bool, Check.toNat_ofNat, UInt256.size, Fe.EVM.calldatasize, Fe.EVM.calldataload,
      Fe.EVM.callvalue, Fe.EVM.caller, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.codesize,
      Fe.EVM.codecopy, Fe.EVM.calldatacopy, Fe.EVM.sload, Fe.EVM.sstore, Fe.EVM.mstore,
      Fe.EVM.mload,
      Fe.EVM.keccak256, revertData, returnData, Reasoning.Theory.byteArray_readWithPadding_zero,
      toNat_mod, sel_mod, shr_mod, ofNat_mod, pair_slot, error_read, panic_read,
      wrap_sub_word, wrap_add_word, wrap_add_lt, wrap_mod,
      Reasoning.Theory.toByteArray_write32_read_back,
      Reasoning.Theory.u256_ofNat_toNat, ofNat_zero_eq,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      Std.TreeMap.getElem_insert, -CharP.cast_eq_zero, *, $ls,*]))


/-- `ir_step`'s simplification without the unfolding: for the rest of a block after a call whose
    callee's result the goal holds symbolically (a match on it), once case facts decide it, and
    for an exported arm and the machine IR simplified together. -/
syntax "ir_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_simp) => `(tactic| ir_simp [])
  | `(tactic| ir_simp [$ls,*]) => `(tactic| (simp [enter,
      Fe.Sonatina.bind, runBody_cons_eq, runBody_nil_eq, runInst, EvmOp.run, evalPair, evalInt,
      evalOperand, evalWord, Fe.Sonatina.word, Val.as, Ty.bits, CmpOp.eval, BinOp.eval,
      Sonatina.bool, Check.toNat_ofNat, UInt256.size, Fe.EVM.calldatasize, Fe.EVM.calldataload,
      Fe.EVM.callvalue, Fe.EVM.caller, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.codesize,
      Fe.EVM.codecopy, Fe.EVM.calldatacopy, Fe.EVM.sload, Fe.EVM.sstore, Fe.EVM.mstore,
      Fe.EVM.mload,
      Fe.EVM.keccak256, revertData, returnData, Reasoning.Theory.byteArray_readWithPadding_zero,
      toNat_mod, sel_mod, shr_mod, ofNat_mod, pair_slot, error_read, panic_read,
      wrap_sub_word, wrap_add_word, wrap_add_lt, wrap_mod,
      Reasoning.Theory.toByteArray_write32_read_back,
      Reasoning.Theory.u256_ofNat_toNat, ofNat_zero_eq,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      Std.TreeMap.getElem_insert, -CharP.cast_eq_zero, *, $ls,*]))

/-- A message call with no input and no output, as `ir_step` leaves its zero lengths: the call
    on empty memory, the memory then put back (`Fe.EVM.call_noData`).  A rewrite to use once with
    `rw`: as a `simp` lemma it applies to its own right side. -/
theorem call_noData0 (gasArg addr value argsPtr retPtr : UInt256) (I : ExecutionEnv)
    (w : World) :
    (Fe.EVM.call gasArg addr value argsPtr ⟨0⟩ retPtr ⟨0⟩).exec I w =
      withMemory w.memory ((Fe.EVM.call gasArg addr value ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩).exec I
        { w with memory := ByteArray.empty }) :=
  call_noData gasArg addr value argsPtr retPtr I w

/-! ## Arithmetic as naturals

`ir_step` leaves the machine IR's arithmetic as `wrap`s of casts to `ℤ`, in a shape that changes
with the facts at hand, which a symbolic length or loop counter makes hard to state facts for.
`ir_step_nat` runs a block with the operations' values as naturals modulo `2 ^ 256` instead
(`eval_add` …; a `sub` stays `BinOp.eval` until `ir_clean` knows it does not wrap), then
`ir_clean` removes each modulus and decides each condition that `omega` proves from the
hypotheses: the bounds of the symbolic values are the only facts a block needs.  The
environment's lookups go through `Std.TreeMap.getElem?_insert`, so the environment may start
from any `E` whose keys a proof states. -/

theorem eval_add (x y : Nat) : BinOp.eval .add 256 x y = (x + y) % size256 := by
  simp only [BinOp.eval, wrap]; omega

theorem eval_sub_le (x y : Nat) (h : y ≤ x) (hx : x < size256) :
    BinOp.eval .sub 256 x y = x - y := by
  simp only [BinOp.eval, wrap]; omega

theorem eval_shl (x y : Nat) :
    BinOp.eval .shl 256 x y = if x ≥ 256 then 0 else y * 2 ^ x % size256 := by
  simp only [BinOp.eval, wrap, Nat.shiftLeft_eq]; split <;> omega

theorem eval_shr (x y : Nat) : BinOp.eval .shr 256 x y = if x ≥ 256 then 0 else y / 2 ^ x := by
  simp only [BinOp.eval, Nat.shiftRight_eq_div_pow]

theorem eval_and (x y : Nat) : BinOp.eval .and 256 x y = x &&& y := rfl


theorem eval_mul (x y : Nat) : BinOp.eval .mul 256 x y = x * y % size256 := by
  simp only [BinOp.eval, wrap]; omega

theorem eval_or (x y : Nat) : BinOp.eval .or 256 x y = x ||| y := rfl

theorem eval_xor (x y : Nat) : BinOp.eval .xor 256 x y = x ^^^ y := rfl

theorem eval_udiv (x y : Nat) : BinOp.eval .udiv 256 x y = if y = 0 then 0 else x / y := rfl

theorem eval_umod (x y : Nat) : BinOp.eval .umod 256 x y = if y = 0 then 0 else x % y := rfl

/-- A word rounded down to a multiple of 32, as the machine IR's `and _ -32` makes it. -/
theorem and_mask32 (x : Nat) (hx : x < size256) :
    x &&& 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      x / 32 * 32 := by
  have hm : (115792089237316195423570985008687907853269984665640564039457584007913129639904 : Nat)
      = (2 ^ 251 - 1) <<< 5 := by norm_num [Nat.shiftLeft_eq]
  have hr : x / 32 * 32 = (x >>> 5) <<< 5 := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  by_cases h5 : 5 ≤ j
  · rw [show 5 + (j - 5) = j by omega]
    by_cases hj : j < 256
    · simp [h5, show j - 5 < 251 by omega]
    · have : x.testBit j = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (le_trans (by norm_num)
          (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 256 ≤ j by omega))))
      simp [h5, this]
  · simp [h5]

/-- `ir_step_nat`'s second half: remove the moduli of values below `2 ^ 256` and decide the
    conditions of `if`s, each by `omega` from the hypotheses. -/
macro "ir_clean" : tactic => `(tactic| try simp (disch := omega) only [Nat.mod_eq_of_lt,
  eval_sub_le, and_mask32, ite_eq_left, ite_eq_right])

/-- `ir_step` with the arithmetic as naturals (see above). -/
syntax "ir_step_nat" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_step_nat) => `(tactic| ir_step_nat [])
  | `(tactic| ir_step_nat [$ls,*]) => `(tactic| ((rw [runBlocks_eq]; simp [enter,
      Fe.Sonatina.bind, runBody_cons_eq, runBody_nil_eq, runInst, EvmOp.run, evalPair, evalInt,
      evalOperand, evalWord, Fe.Sonatina.word, Val.as, Ty.bits, CmpOp.eval, eval_add, eval_mul,
      eval_shl, eval_shr, eval_and, eval_or, eval_xor, eval_udiv, eval_umod, Sonatina.bool,
      Check.toNat_ofNat, UInt256.size, Fe.EVM.calldatasize, Fe.EVM.calldataload,
      Fe.EVM.callvalue, Fe.EVM.caller, Fe.EVM.logData, Fe.EVM.emit, Fe.EVM.codesize,
      Fe.EVM.codecopy, Fe.EVM.calldatacopy, Fe.EVM.sload, Fe.EVM.sstore, Fe.EVM.mstore,
      Fe.EVM.mload, Fe.EVM.mcopy, Fe.EVM.keccak256, revertData, returnData,
      Reasoning.Theory.byteArray_readWithPadding_zero, toNat_mod, ofNat_mod, pair_slot,
      error_read, panic_read, Reasoning.Theory.u256_ofNat_toNat, ofNat_zero_eq,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, Std.TreeMap.getElem_insert,
      Std.TreeMap.getElem?_insert, -CharP.cast_eq_zero, *, $ls,*]) <;> ir_clean))

/-- A word plus a number below `2 ^ 256`, as the machine IR's `add` gives it to `evm_sload`. -/
theorem ofNat_toNat_add (a : UInt256) {i : Nat} (hi : i < size256) :
    UInt256.ofNat (a.toNat + i) = a + UInt256.ofNat i :=
  Check.eq_of_toNat (by
    rw [uadd_toNat, Check.toNat_ofNat, Check.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < UInt256.size from hi)])

/-! ## Memory a block writes past what it reads

A run that copies a value into fresh memory writes at the free pointer, past the memory's end
or at it, and reads the copy back; these lemmas keep memory as a known prefix followed by the
words written. -/

/-- A word written at or past the end of memory: zeros up to it, then the word. -/
theorem write_gap (v : UInt256) (M : ByteArray) {d : Nat} (h : M.size ≤ d)
    (hg : d - M.size < USize.size) :
    v.toByteArray.write 0 M d 32 = M ++ ByteArray.zeroes (d - M.size) ++ v.toByteArray := by
  rw [write_from_gap_eq _ _ 0 d 32 (by decide) (by rw [toByteArray_size]) h hg,
    toByteArray_extract_all]

/-- A word written at the end of memory is appended. -/
theorem write_end (v : UInt256) (M : ByteArray) {d : Nat} (h : d = M.size) :
    v.toByteArray.write 0 M d 32 = M ++ v.toByteArray := by
  subst h
  rw [write_gap v M le_rfl (by simp), Nat.sub_self, zeroes_zero rfl, ByteArray.append_empty]

/-- A word written inside the first part of memory leaves the rest. -/
theorem write_append_left (v : UInt256) (X T : ByteArray) {d : Nat} (h : d + 32 ≤ X.size) :
    v.toByteArray.write 0 (X ++ T) d 32 = v.toByteArray.write 0 X d 32 ++ T := by
  have hv := toByteArray_size v
  rw [write32_eq _ _ d (by omega) (by rw [ByteArray.size_append]; omega),
    write32_eq _ _ d (by omega) (by omega), extract_append_left _ _ 0 d (by omega),
    extract_append_span _ _ _ _ (by omega) (by rw [ByteArray.size_append]; omega),
    ByteArray.size_append, show X.size + T.size - X.size = T.size by omega,
    byteArray_extract_self]
  simp only [ByteArray.append_assoc]

/-- The size of memory after a word is written below `2 ^ 32`. -/
theorem write_size (v : UInt256) (M : ByteArray) {d : Nat} (hd : d < 2 ^ 32) :
    (v.toByteArray.write 0 M d 32).size = max M.size (d + 32) := by
  by_cases h : d ≤ M.size
  · exact toByteArray_write32_size_of_le _ _ _ _ _ rfl h rfl
  · exact toByteArray_write32_size_of_ge _ _ _ _ _ rfl (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ hd)) (by omega)

/-- A read inside the first part of memory. -/
theorem read_prefix (X T : ByteArray) {a n : Nat} (hn : 0 < n) (h : a + n ≤ X.size) :
    (X ++ T).readWithPadding a n = X.readWithPadding a n := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ hn (by rw [ByteArray.size_append]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ hn h, extract_append_left _ _ _ _ h]

/-- The word at the start of memory past a prefix of `p` bytes. -/
theorem read_after (B D : ByteArray) (v : UInt256) {p : Nat} (h : p = B.size) :
    (B ++ (v.toByteArray ++ D)).readWithPadding p 32 = v.toByteArray := by
  rw [readWithPadding_tail B _ 0 32 (by omega) (by decide)
      (by rw [ByteArray.size_append, toByteArray_size]; omega),
    extract_append_left _ _ 0 32 (by rw [toByteArray_size]), toByteArray_extract_all]

/-- A copy from past the end of its source to the end of memory, as a `calldatacopy` at
    `calldatasize` into fresh memory: the model's `write` copies nothing then, the bytes past
    the end of memory reading as zeros anyway. -/
theorem copy_past_end (src M : ByteArray) {s d n : Nat} (hs : src.size ≤ s) (hd : M.size ≤ d) :
    src.write s M d n = M := by
  by_cases hn : n = 0
  · simp [ByteArray.write, hn]
  · simp only [ByteArray.write, ite_eq_right hn, ite_eq_left (show s ≥ src.size from hs)]
    apply ByteArray.ext
    simp [ByteArray.copySlice, show M.size - d = 0 by omega, show min d M.size = M.size by omega]

/-- A copy of memory's own bytes to its end, as `mcopy` to fresh memory. -/
theorem copy_to_end (X : ByteArray) {ptr d n : Nat} (hn : n ≠ 0) (h : ptr + n ≤ X.size)
    (hd : d = X.size) : X.write ptr X d n = X ++ X.extract ptr (ptr + n) := by
  subst hd
  rw [write_from_gap_eq _ _ _ _ _ hn h le_rfl (by simp), Nat.sub_self, zeroes_zero rfl,
    ByteArray.append_empty]

/-! ## Loops

A loop of the machine IR is a header block entered again from its latch.  `runBlocks_loop` runs
one by induction on the iterations left, from an invariant `J i` of the environment and world at
the header after `i` iterations: `hstep` says that the run from the header with `J i` ends as
every run from the header with `J (i + 1)` ends, for whatever result `K` that is (by
`ir_step_nat` through the body to the latch, then the hypothesis on `K`); `hdone` gives the run
from `J n` through the exit.  The first entry, from the block before the loop, binds the
header's phis to their initial values; a proof runs it once by hand and then this lemma. -/

theorem runBlocks_loop {m : Module} {c : Ctx} {f : Func} {I : ExecutionEnv} {prev : Option Nat}
    {hd n : Nat} (J : Nat → Env → World → Prop)
    {R : Option (Except (Exit World) (List Val × World))}
    (hstep : ∀ i E w, i < n → J i E w → ∀ K : Option (Except (Exit World) (List Val × World)),
      (∀ E' w', J (i + 1) E' w' → (runBlocks m c f E' prev hd).exec I w' = K) →
      (runBlocks m c f E prev hd).exec I w = K)
    (hdone : ∀ E w, J n E w → (runBlocks m c f E prev hd).exec I w = R) :
    ∀ i E w, i ≤ n → J i E w → (runBlocks m c f E prev hd).exec I w = R := by
  intro i
  induction h : n - i generalizing i with
  | zero =>
    intro E w hi hJ
    obtain rfl : i = n := by omega
    exact hdone E w hJ
  | succ k ih =>
    intro E w hi hJ
    exact hstep i E w (by omega) hJ R fun E' w' hJ' => ih (i + 1) (by omega) E' w' (by omega) hJ'

end Fe.Sonatina
