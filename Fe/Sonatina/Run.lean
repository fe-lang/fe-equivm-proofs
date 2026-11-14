import Fe.Sonatina.CheckCert
import Fe.EVM.Entry
import Reasoning.Memory

/-!
# Running the machine IR of a contract

Lemmas for running a function of the machine IR on a call by `simp`, block by block: `ir_step`
unfolds `runBlocks` once and simplifies the block it is at, with the interpreter's definitions
and the model library's primitives.  A contract's run lemmas give it the function and the facts
of the call (`calldata_facts` for an arm's head check) and apply it once per block on the path.
-/

namespace Fe.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Reasoning.Theory

/-- `2 ^ 256`, as `simp` leaves it. -/
local notation "size256" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- A word's value modulo `2 ^ 256`, as `simp` meets it once `UInt256.size` is a literal. -/
theorem toNat_mod (u : UInt256) : u.toNat % size256 = u.toNat :=
  Nat.mod_eq_of_lt u.val.isLt

/-- The selector word of calldata, as the IR computes it with `shr`. -/
theorem selWord_toNat (cd : ByteArray) :
    (selWord cd).toNat = (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 := by
  have h := Check.shr_word (x := 224) (y := (uInt256OfByteArray (cd.readBytes 0 32)).toNat)
    (by decide) (UInt256.val _).isLt
  rw [Reasoning.Theory.u256_ofNat_toNat] at h
  rw [selWord, show (⟨224⟩ : UInt256) = UInt256.ofNat 224 from rfl, h, if_neg (by decide)]
  exact Check.toNat_ofNat_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt256.val _).isLt)

/-- The exported dispatcher's selector test, as the machine IR's `br_table` makes it. -/
theorem selWord_eq_iff {cd : ByteArray} {k : Nat} (hk : k < UInt256.size) :
    selWord cd = UInt256.ofNat k ↔ (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 = k := by
  rw [← selWord_toNat]
  constructor
  · intro h; rw [h, Check.toNat_ofNat_lt hk]
  · intro h; exact Check.eq_of_toNat (by rw [h, Check.toNat_ofNat_lt hk])

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
  rw [if_neg hlen, if_neg hlen, if_neg (by omega), if_neg (by omega), hs]
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

/-- Unfold `runBlocks` once and simplify the block the run is at, with the interpreter's
    definitions, the model library's primitives, the local hypotheses and the extra lemmas. -/
syntax "ir_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_step) => `(tactic| ir_step [])
  | `(tactic| ir_step [$ls,*]) => `(tactic| (rw [runBlocks.eq_1]; simp [Func.block?, enter,
      Fe.Sonatina.bind, runBody.eq_2, runBody.eq_1, runInst, EvmOp.run, evalPair, evalInt,
      evalOperand, evalWord, Fe.Sonatina.word, Val.as, Ty.bits, CmpOp.eval, BinOp.eval,
      Sonatina.bool, Check.toNat_ofNat, UInt256.size, Fe.EVM.calldatasize, Fe.EVM.calldataload,
      Fe.EVM.callvalue, Fe.EVM.codesize, Fe.EVM.codecopy, Fe.EVM.sload, Fe.EVM.sstore,
      Fe.EVM.mstore, Fe.EVM.mload, revertData, returnData,
      Reasoning.Theory.byteArray_readWithPadding_zero, toNat_mod, sel_mod,
      Reasoning.Theory.u256_ofNat_toNat, show UInt256.ofNat 0 = ⟨0⟩ from rfl,
      Std.TreeMap.getElem_insert, *, $ls,*]))

end Fe.Sonatina
