import FeProofs.WETH9.SonatinaRun

/-!
# FeWETH9's `%load`, run

`%load slot` reads a Solidity-style string from storage into fresh memory at the free pointer:
the length word, then a short string's head or each data word of a long one, cut to the bytes
left.  `name()` and `symbol()` call it.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Reasoning.Theory
open Stele (solidityDecodeBytesLengthHeader solidityBytesDataBaseSlot)
open Exported (loadWords loaded)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

/-- `2 ^ 256`, as `simp` leaves it. -/
local notation "size256" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The machine IR's mask of a word's first `r` bytes, `and x (not (shr (shl 3 r) -1))`, is
    `leadWord`. -/
theorem mask_leadWord (x : UInt256) (r : Nat) (hr : r < 32) :
    x.toNat &&& (115792089237316195423570985008687907853269984665640564039457584007913129639935 -
      115792089237316195423570985008687907853269984665640564039457584007913129639935 /
        2 ^ (r * 8) % size256) = (leadWord x r).toNat := by
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num))]
  have h1 : 1 ≤ 2 ^ (8 * (32 - r)) := Nat.one_le_two_pow
  have h2 : 2 ^ (8 * (32 - r)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [leadWord, ite_eq_left hr, uland_toNat, leadMask_eq r hr, lit_toNat (by omega)]
  have h := two_pow_sub_one_div 256 (r * 8) (by omega)
  rw [show 256 - r * 8 = 8 * (32 - r) by omega] at h
  norm_num at h ⊢
  rw [h]
  congr 1
  omega

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

set_option maxHeartbeats 4000000 in
/-- `%load`'s blocks from 6 on: the length word at the free pointer `p` is checked against the
    length, and the pointer and the size of the copy are returned. -/
theorem loadTail_run (L p : Nat) (B D : ByteArray) (hB : B.size = p) (hL : L < 2 ^ 255)
    (hp : p < 2 ^ 64) (E : Sonatina.Env) (prev : Option Nat)
    (h6 : E[6]? = some (Val.int 256 L))
    (h13 : E[13]? = some (Val.int 256 (32 + (L + 31) / 32 * 32)))
    (h22 : E[22]? = some (Val.int 256 p)) :
    (runBlocks m ic loadFunc E prev 6).exec I
        { w with memory := B ++ ((UInt256.ofNat L).toByteArray ++ D) } =
      some (.ok ([Val.int 256 p, Val.int 256 (32 + (L + 31) / 32 * 32)],
        { w with memory := B ++ ((UInt256.ofNat L).toByteArray ++ D) })) := by
  have hread := read_after B D (UInt256.ofNat L) hB.symm
  have hLn : (UInt256.ofNat L).toNat = L := lit_toNat (by omega)
  by_cases hL0 : L = 0
  · subst hL0
    rw [ofNat_zero_eq] at hread
    repeat ir_step_nat [uInt256OfByteArray_toByteArray]
  · have hW : (L - 1) / 32 + 1 = (L + 31) / 32 := by omega
    repeat ir_step_nat [uInt256OfByteArray_toByteArray, hW]

set_option maxHeartbeats 4000000 in
/-- One iteration of `%load`'s copy loop over a long string's data words, blocks 25 to 28: the
    data word `i`, cut to the bytes left, is appended, and the loop header is entered again with
    `i + 1`.  Stated for any run `R` the header's state goes on to. -/
theorem loadIter_run (slot : UInt256) (L p i : Nat) (B : ByteArray) (hB : B.size = p)
    (hL : L < 2 ^ 255) (hp : p < 2 ^ 64) (hi : i < (L + 31) / 32)
    (R : Option (Except (Exit World) (List Val × World))) (E : Sonatina.Env)
    (h3 : E[3]? = some (Val.int 256 i)) (h6 : E[6]? = some (Val.int 256 L))
    (h10 : E[10]? = some (Val.int 256 ((L + 31) / 32)))
    (h13 : E[13]? = some (Val.int 256 (32 + (L + 31) / 32 * 32)))
    (h22 : E[22]? = some (Val.int 256 p))
    (h40 : E[40]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat))
    (hk : ∀ E' : Sonatina.Env, E'[53]? = some (Val.int 256 (i + 1)) →
      E'[6]? = some (Val.int 256 L) → E'[10]? = some (Val.int 256 ((L + 31) / 32)) →
      E'[13]? = some (Val.int 256 (32 + (L + 31) / 32 * 32)) → E'[22]? = some (Val.int 256 p) →
      E'[40]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat) →
      (runBlocks m ic loadFunc E' (some 28) 24).exec I { w with memory :=
        B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L (i + 1)) } = R) :
    (runBlocks m ic loadFunc E (some 24) 25).exec I
        { w with memory := B ++ ((UInt256.ofNat L).toByteArray ++
          loadWords I w.accounts slot L i) } = R := by
  have hadd := ofNat_toNat_add (solidityBytesDataBaseSlot slot) (i := i) (by omega)
  have hsize : (B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L i)).size =
      p + (32 + i * 32) := by
    simp only [ByteArray.size_append, toByteArray_size, loadWords, wordsBytes_size, hB]; omega
  have hnext : ∀ v : UInt256, v = leadWord (slotWord I w.accounts
        (solidityBytesDataBaseSlot slot + UInt256.ofNat i)) (L - 32 * i) →
      B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L i) ++ v.toByteArray =
        B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L (i + 1)) := by
    rintro v rfl
    simp only [loadWords, wordsBytes, ByteArray.append_assoc]
  by_cases hr : L - i * 32 < 32
  · ir_step_nat
    ir_step_nat [hadd]
    ir_step_nat [mask_leadWord _ _ hr]
    rw [write_end _ _ hsize.symm, hnext _ (by congr 1; omega)]
    exact hk _ (by simp) (by simp [Std.TreeMap.getElem?_insert, h6])
      (by simp [Std.TreeMap.getElem?_insert, h10]) (by simp [Std.TreeMap.getElem?_insert, h13])
      (by simp [Std.TreeMap.getElem?_insert, h22]) (by simp [Std.TreeMap.getElem?_insert, h40])
  · ir_step_nat
    ir_step_nat [hadd]
    ir_step_nat
    rw [write_end _ _ hsize.symm, hnext _ (by rw [leadWord, ite_eq_right (by omega)])]
    exact hk _ (by simp) (by simp [Std.TreeMap.getElem?_insert, h6])
      (by simp [Std.TreeMap.getElem?_insert, h10]) (by simp [Std.TreeMap.getElem?_insert, h13])
      (by simp [Std.TreeMap.getElem?_insert, h22]) (by simp [Std.TreeMap.getElem?_insert, h40])

set_option maxHeartbeats 4000000 in
/-- `%load`'s copy loop, from its header entered again from block 28 after `i` iterations: each
    appends a data word (`loadIter_run`), and at the end the run goes on through
    `loadTail_run` to the return. -/
theorem loadLoop_run (slot : UInt256) (L p : Nat) (B : ByteArray) (hB : B.size = p)
    (hL : L < 2 ^ 255) (hp : p < 2 ^ 64) :
    ∀ i (E : Sonatina.Env), i ≤ (L + 31) / 32 → E[53]? = some (Val.int 256 i) →
      E[6]? = some (Val.int 256 L) → E[10]? = some (Val.int 256 ((L + 31) / 32)) →
      E[13]? = some (Val.int 256 (32 + (L + 31) / 32 * 32)) → E[22]? = some (Val.int 256 p) →
      E[40]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat) →
      (runBlocks m ic loadFunc E (some 28) 24).exec I { w with memory :=
          B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L i) } =
        some (.ok ([Val.int 256 p, Val.int 256 (32 + (L + 31) / 32 * 32)], { w with memory :=
          B ++ ((UInt256.ofNat L).toByteArray ++
            loadWords I w.accounts slot L ((L + 31) / 32)) })) := by
  intro i E hi h53 h6 h10 h13 h22 h40
  refine runBlocks_loop (fun i E w' => w' = { w with memory :=
      B ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L i) } ∧
      E[53]? = some (Val.int 256 i) ∧ E[6]? = some (Val.int 256 L) ∧
      E[10]? = some (Val.int 256 ((L + 31) / 32)) ∧
      E[13]? = some (Val.int 256 (32 + (L + 31) / 32 * 32)) ∧ E[22]? = some (Val.int 256 p) ∧
      E[40]? = some (Val.int 256 (solidityBytesDataBaseSlot slot).toNat)) ?_ ?_ i E _ hi
    ⟨rfl, h53, h6, h10, h13, h22, h40⟩
  · rintro i E w' hi ⟨rfl, h53, h6, h10, h13, h22, h40⟩ K hK
    ir_step_nat
    exact loadIter_run ic I w slot L p i B hB hL hp hi _ _
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp [Std.TreeMap.getElem?_insert, h6]) (by simp [Std.TreeMap.getElem?_insert, h10])
      (by simp [Std.TreeMap.getElem?_insert, h13]) (by simp [Std.TreeMap.getElem?_insert, h22])
      (by simp [Std.TreeMap.getElem?_insert, h40])
      (fun E' h53' h6' h10' h13' h22' h40' => hK E' _ ⟨rfl, h53', h6', h10', h13', h22', h40'⟩)
  · rintro E w' ⟨rfl, h53, h6, h10, h13, h22, h40⟩
    ir_step_nat
    ir_step_nat
    exact loadTail_run ic I w L p B _ hB hL hp _ _ (by simp [Std.TreeMap.getElem?_insert, h6])
      (by simp [Std.TreeMap.getElem?_insert, h13]) (by simp [Std.TreeMap.getElem?_insert, h22])

/-- What `%load slot` ends with, from memory whose free pointer is `p`: `Panic(0x22)` on a head
    whose length contradicts its flag, `Panic(0x41)` when the copy would reach `2 ^ 64` bytes,
    or the copy's pointer `p` and size, the copy (the length word, then the bytes as Stele reads
    them, zero-padded to words, as `SolString::load` copies them) following a first part `A'` of
    memory. -/
def loadOut (slot : UInt256) (p : Nat) (A' : ByteArray) :
    Option (Except (Exit World) (List Val × World)) :=
  match solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) with
  | .ok L =>
    if 32 + (L + 31) / 32 * 32 < 2 ^ 64 then
      some (.ok ([Val.int 256 p, Val.int 256 (32 + (L + 31) / 32 * 32)],
        { w with memory := A' ++ ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I slot L) }))
    else some (.error (.revert (panicData 65)))
  | _ => some (.error (.revert (panicData 0x22)))

set_option maxHeartbeats 8000000 in
/-- `%load slot` from memory `A` whose free pointer `p` lies at or past its end, above the
    arena: it ends as `loadOut`, the first part `A'` of memory `p` bytes long and holding the
    free pointer past the copy. -/
theorem load_run (hf : m.func? "load" = some loadFunc)
    (hs : m.func? "stored_len" = some storedLenFunc)
    (hr : m.func? "revert_error" = some revertErrorFunc) (slot : UInt256) (A : ByteArray)
    (p : Nat) (hfp : uInt256OfByteArray (A.readWithPadding 64 32) = UInt256.ofNat p)
    (hA : A.size ≤ p) (h192 : 192 ≤ p) (hp : p < 2 ^ 32) :
    ∃ A' : ByteArray, A'.size = p ∧
      (∀ L, solidityDecodeBytesLengthHeader (slotWord I w.accounts slot) = .ok L →
        uInt256OfByteArray (A'.readWithPadding 64 32) =
          UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))) ∧
      (runFunc m ic "load" [Val.int 256 slot.toNat]).exec I { w with memory := A } =
        loadOut I w slot p A' := by
  have hh := (slotWord I w.accounts slot).val.isLt
  change (slotWord I w.accounts slot).toNat < 2 ^ 256 at hh
  rw [runFunc_entry hf rfl]
  rcases decodeHeader_cases (slotWord I w.accounts slot) with
    ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨_, hrev⟩
  · generalize hL : (slotWord I w.accounts slot).toNat / 2 = L at hge hok
    have hL255 : L < 2 ^ 255 := by omega
    have hround : (32 + (L + 31) / 32 * 32 + 31) / 32 * 32 = 32 + (L + 31) / 32 * 32 := by omega
    have hA1 : ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write 0 A 64 32).size
        ≤ p := by rw [write_size _ _ (by decide)]; omega
    have hA2 : ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write 0 A 64 32 ++
        ByteArray.zeroes (p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
          0 A 64 32).size)).size = p := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
    have hfp2 : uInt256OfByteArray (((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
        0 A 64 32 ++ ByteArray.zeroes (p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
          0 A 64 32).size)).readWithPadding 64 32) = UInt256.ofNat (p + (32 + (L + 31) / 32 * 32)) := by
      rw [read_prefix _ _ (by decide) (by rw [write_size _ _ (by decide)]; omega),
        word_read_gap _ _ (by decide), uInt256OfByteArray_toByteArray]
    have hgap : p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
        0 A 64 32).size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ hp)
    by_cases h64 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    swap
    · refine ⟨_, hA2, fun L' h => by rw [hok] at h; cases h; exact hfp2, ?_⟩
      simp only [loadOut, hok, ite_eq_right h64]
      simp [Fe.Sonatina.bind]
      repeat ir_step_nat [storedLen_run ic I _ hs hr, hok]
    have hbs : UInt256.ofNat (fromByteArrayBigEndian (KEC slot.toByteArray)) =
        solidityBytesDataBaseSlot slot := keccakSlot_eq _
    have hbs' : fromByteArrayBigEndian (KEC slot.toByteArray) % size256 =
        (solidityBytesDataBaseSlot slot).toNat := by rw [← hbs]; rfl
    have hlong : loadWords I w.accounts slot L ((L + 31) / 32) = loaded w.accounts I slot L := by
      rw [loadWords, leadWords_eq _ L (by omega), loaded, strBytes, ite_eq_right (by omega)]
      rfl
    have hA's : (slot.toByteArray.write 0 ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
        0 A 64 32 ++ ByteArray.zeroes (p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
          0 A 64 32).size)) 160 32).size = p := by rw [write_size _ _ (by decide), hA2]; omega
    refine ⟨_, hA's,
      fun L' h => by
        rw [hok] at h; cases h
        rw [toByteArray_write_read_below_of_gap _ _ _ _ (by omega) (by decide)
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by decide))), hfp2], ?_⟩
    simp only [loadOut, hok, ite_eq_left h64]
    simp [Fe.Sonatina.bind]
    ir_step_nat [storedLen_run ic I _ hs hr, hok]
    ir_step_nat [Nat.and_one_is_mod, ho]
    ir_step_nat [word_read_gap]
    ir_step_nat
    rw [write_gap _ _ hA1 hgap, write_append_left _ _ _ (by rw [hA2]; omega),
      show ∀ X : ByteArray, X ++ (UInt256.ofNat L).toByteArray =
        X ++ ((UInt256.ofNat L).toByteArray ++ loadWords I w.accounts slot L 0) by
          intro X; simp [loadWords, wordsBytes], ← hlong]
    exact loadIter_run ic I w slot L p 0 _ hA's
      hL255 (by omega) (by omega) _ _ (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (by simp only [Std.TreeMap.getElem?_insert]; simp)
      (fun E' h53 h6 h10 h13 h22 h40 => loadLoop_run ic I w slot L p _ hA's hL255 (by omega)
        1 E' (by omega) h53 h6 h10 h13 h22 h40)
  · generalize hL : (slotWord I w.accounts slot).toNat % 256 / 2 = L at hlt hok
    have h64 : 32 + (L + 31) / 32 * 32 < 2 ^ 64 := by omega
    have hround : (32 + (L + 31) / 32 * 32 + 31) / 32 * 32 = 32 + (L + 31) / 32 * 32 := by omega
    have hA1 : ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write 0 A 64 32).size
        ≤ p := by rw [write_size _ _ (by decide)]; omega
    have hA2 : ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write 0 A 64 32 ++
        ByteArray.zeroes (p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
          0 A 64 32).size)).size = p := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
    have hfp2 : uInt256OfByteArray (((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
        0 A 64 32 ++ ByteArray.zeroes (p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
          0 A 64 32).size)).readWithPadding 64 32) = UInt256.ofNat (p + (32 + (L + 31) / 32 * 32)) := by
      rw [read_prefix _ _ (by decide) (by rw [write_size _ _ (by decide)]; omega),
        word_read_gap _ _ (by decide), uInt256OfByteArray_toByteArray]
    have hgap : p - ((UInt256.ofNat (p + (32 + (L + 31) / 32 * 32))).toByteArray.write
        0 A 64 32).size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ hp)
    refine ⟨_, hA2, fun L' h => by rw [hok] at h; cases h; exact hfp2, ?_⟩
    simp only [loadOut, hok, ite_eq_left h64]
    simp [Fe.Sonatina.bind]
    ir_step_nat [storedLen_run ic I _ hs hr, hok]
    ir_step_nat [Nat.and_one_is_mod, he]
    by_cases hL0 : L = 0
    · subst hL0
      ir_step_nat
      ir_step_nat
      have h0 : loaded w.accounts I slot 0 = ByteArray.empty := by simp [loaded, strBytes]
      rw [write_gap _ _ hA1 hgap, h0]
      have ht := loadTail_run (m := m) ic I w 0 p _ ByteArray.empty hA2 (by omega) (by omega)
      simp only [ofNat_zero_eq, ByteArray.append_empty, Nat.zero_add, Nat.add_zero, Nat.reduceDiv,
        Nat.reduceMul] at ht ⊢
      exact ht _ _ (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
    · ir_step_nat
      ir_step_nat
      ir_step_nat
      ir_step_nat [mask_leadWord _ _ hlt]
      have hW : (L + 31) / 32 = 1 := by omega
      have hls : (leadWord (slotWord I w.accounts slot) L).toByteArray = loaded w.accounts I slot L := by
        rw [leadWord_toByteArray, loaded, strBytes, ite_eq_left (by omega), Nat.min_eq_left (by omega), hW]
        rfl
      rw [write_gap _ _ hA1 hgap, write_end _ _ (by
          simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]; omega),
        show ∀ X : ByteArray, X ++ (UInt256.ofNat L).toByteArray ++
            (leadWord (slotWord I w.accounts slot) L).toByteArray =
          X ++ ((UInt256.ofNat L).toByteArray ++
            (leadWord (slotWord I w.accounts slot) L).toByteArray) from
          fun X => ByteArray.append_assoc, hls]
      exact loadTail_run ic I w L p _ _ hA2 (by omega) (by omega) _ _
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
        (by simp only [Std.TreeMap.getElem?_insert]; simp)
  · refine ⟨A ++ ByteArray.zeroes (p - A.size), by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega, fun L h => by simp [hrev] at h, ?_⟩
    simp [Fe.Sonatina.bind]
    ir_step_nat [storedLen_run ic I _ hs hr, hrev]
    simp [loadOut, hrev]

end FeProofs.WETH9.Sonatina
