import Fe.Sonatina.Stage3.Place.Word
import Fe.Sonatina.Steps.Mem

/-!
# Memory: the machine's bytes and H's cells

The machine IR's memory is one byte array (`World.memory`), read with zero padding past its end;
`mem m a` is its byte at address `a`.  H's memory is its blocks' cells (`H/Memory.lean`).  The
simulation (`Place/Inv.lean`) relates the two byte by byte: the byte at `j b + i` is the value
of cell `i` of block `b`.  This file gives each side's operations byte by byte:

- the machine's: `mem_write` (every write is a `ByteArray.write`, `Steps.write_getD`), and
  `readWithPadding_of_mem` (a padded read is the list of its bytes);
- H's: `State.cell`, `State.bsize`, the cells after `State.write` (`cell_write`) and after an
  allocation (`cell_alloc`), the cells a range reads (`cellsAt_eq`), and that neither changes a
  block's address word or size or the number of blocks;
- between them: a read of a block whose bytes agree with the machine's reads the same bytes
  (`bytes_of_agree`), and the typed load of 32 cells is the machine's word of them
  (`load_word`).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Machine memory -/

/-- The byte at address `a` of the machine's memory: zero past its end. -/
def mem (m : ByteArray) (a : Nat) : UInt8 := m.data.getD a 0

theorem mem_write (src : ByteArray) (sa : Nat) (m : ByteArray) (da len i : Nat) :
    mem (src.write sa m da len) i =
      if da ≤ i ∧ i < da + len then src.data.getD (sa + (i - da)) 0 else mem m i :=
  write_getD src sa m da len i

/-- A padded read is the list of the bytes it covers. -/
theorem readWithPadding_of_mem {m : ByteArray} {a n : Nat} {l : List UInt8} (hl : l.length = n)
    (h : ∀ i (hi : i < n), mem m (a + i) = l[i]'(hl ▸ hi)) :
    m.readWithPadding a n = ⟨l.toArray⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, Check.readWithPadding_size', List.size_toArray, hl]
  · intro i h1 h2
    have hi : i < n := by simpa [Check.readWithPadding_size'] using h1
    have e := Check.readWithPadding_getD m a n i hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some] at e
    rw [e]
    simp only [List.getElem_toArray]
    exact h i hi

/-! ## H's cells -/

/-- Cell `i` of block `b` (a zero byte past its bytes, or for a block that does not exist). -/
def _root_.Fe.Sonatina.H.State.cell (st : H.State) (b i : Nat) : MByte :=
  (st.blocks[b]?.map fun blk => blk.bytes.getD i (.byte 0)).getD (.byte 0)

/-- The size of block `b` (0 for a block that does not exist). -/
def _root_.Fe.Sonatina.H.State.bsize (st : H.State) (b : Nat) : Nat :=
  (st.blocks[b]?.map (·.size)).getD 0

theorem cellsAt_eq {st : H.State} {b : Nat} (hb : b < st.blocks.size) (o len : Nat) :
    st.cellsAt b o len = (List.range len).map fun i => st.cell b (o + i) := by
  simp [State.cellsAt, State.cell, Array.getElem?_eq_getElem hb]

/-- The bytes the set-loop of `State.write` leaves: the cells written in the window within the
    array, the old ones elsewhere. -/
theorem foldl_set_getD (o : Nat) (d : MByte) :
    ∀ (cs : List MByte) (k : Nat) (arr : Array MByte) (i : Nat),
    ((cs.zipIdx k).foldl (fun a (c, j) => a.set! (o + j) c) arr).getD i d =
      if o + k ≤ i ∧ i < arr.size then (cs[i - (o + k)]?).getD (arr.getD i d) else arr.getD i d
  | [], k, arr, i => by simp
  | c :: cs, k, arr, i => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_set_getD o d cs (k + 1) (arr.set! (o + k) c) i]
    have hset : ∀ j, (arr.set! (o + k) c).getD j d =
        if o + k = j ∧ j < arr.size then c else arr.getD j d := by
      intro j
      simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds]
      by_cases h1 : o + k = j
      · subst h1
        by_cases h2 : o + k < arr.size
        · simp [h2]
        · simp [h2, Array.getElem?_eq_none (by omega : arr.size ≤ o + k)]
      · simp [h1]
    simp only [Array.size_setIfInBounds, Array.set!_eq_setIfInBounds] at hset ⊢
    rcases Nat.lt_trichotomy i (o + k) with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), hset, if_neg (by omega)]
    · subst h
      rw [if_neg (by omega), hset]
      by_cases h2 : o + k < arr.size
      · rw [if_pos ⟨rfl, h2⟩, if_pos ⟨le_refl _, h2⟩]; simp
      · rw [if_neg (by omega), if_neg (by omega)]
    · rw [hset, if_neg (show ¬ (o + k = i ∧ i < arr.size) by omega)]
      by_cases h2 : i < arr.size
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨by omega, h2⟩]
        have : i - (o + k) = (i - (o + (k + 1))) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      · rw [if_neg (by omega), if_neg (by omega)]

theorem foldl_set_size (o : Nat) :
    ∀ (cs : List MByte) (k : Nat) (arr : Array MByte),
    ((cs.zipIdx k).foldl (fun a (c, j) => a.set! (o + j) c) arr).size = arr.size
  | [], _, _ => rfl
  | c :: cs, k, arr => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_set_size o cs (k + 1)]
    simp

theorem write_blocks_size (st : H.State) (b o : Nat) (cs : List MByte) :
    (st.write (.at b o) cs).blocks.size = st.blocks.size := by
  simp [State.write]

theorem write_blocks_get? (st : H.State) (b o : Nat) (cs : List MByte) (b' : Nat) :
    (st.write (.at b o) cs).blocks[b']? = st.blocks[b']?.map fun blk =>
      if b' = b then { blk with bytes := cs.zipIdx.foldl (fun a (c, i) => a.set! (o + i) c) blk.bytes }
      else blk := by
  simp only [State.write, Array.getElem?_modify]
  by_cases h : b = b' <;> simp [h, eq_comm]

/-- A write changes no block's address word. -/
theorem addrOf_write (st : H.State) (r : H.Range) (cs : List MByte) :
    (st.write r cs).addrOf = st.addrOf := by
  funext b'
  cases r with
  | empty => rfl
  | «at» b o =>
    simp only [State.addrOf, write_blocks_get?, Option.map_map]
    congr 1
    cases st.blocks[b']? with
    | none => rfl
    | some blk => simp only [Option.map_some, Function.comp_apply]; split <;> rfl

theorem bsize_write (st : H.State) (r : H.Range) (cs : List MByte) (b' : Nat) :
    (st.write r cs).bsize b' = st.bsize b' := by
  cases r with
  | empty => rfl
  | «at» b o =>
    simp only [State.bsize, write_blocks_get?, Option.map_map]
    cases st.blocks[b']? with
    | none => rfl
    | some blk => simp only [Option.map_some, Function.comp_apply]; split <;> rfl

theorem write_bytes_size (st : H.State) (b o : Nat) (cs : List MByte) (b' : Nat) :
    ((st.write (.at b o) cs).blocks[b']?.map (·.bytes.size)) = st.blocks[b']?.map (·.bytes.size) := by
  rw [write_blocks_get?]
  cases st.blocks[b']? with
  | none => rfl
  | some blk =>
    simp only [Option.map_some]
    split
    · exact congrArg some (foldl_set_size o cs 0 blk.bytes)
    · rfl

/-- The cells after a write to an existing block: those written, in the window, the old ones
    elsewhere (a write within the block's bytes). -/
theorem cell_write (st : H.State) (b o : Nat) (cs : List MByte) (b' i : Nat)
    (hb : b < st.blocks.size) (hsz : o + cs.length ≤ st.blocks[b].bytes.size) :
    (st.write (.at b o) cs).cell b' i =
      if b' = b ∧ o ≤ i then (cs[i - o]?).getD (st.cell b' i) else st.cell b' i := by
  simp only [State.cell, write_blocks_get?, Option.map_map]
  by_cases hbb : b' = b
  · subst hbb
    rw [Array.getElem?_eq_getElem hb]
    simp only [Option.map_some, Function.comp_apply, if_true, Option.getD_some, true_and]
    rw [foldl_set_getD o (.byte 0) cs 0 _ i]
    simp only [Nat.add_zero]
    by_cases h1 : o ≤ i
    · rw [if_pos h1]
      by_cases h2 : i < st.blocks[b'].bytes.size
      · rw [if_pos ⟨h1, h2⟩]
      · rw [if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl
    · rw [if_neg (by omega), if_neg h1]
  · rw [if_neg (by omega)]
    cases st.blocks[b']? with
    | none => rfl
    | some blk => simp [hbb]

/-! ## Allocation -/

theorem alloc_get? (st : H.State) (k : BlockKind) (n a : Nat) (fresh : List UInt8) (b : Nat) :
    (st.alloc k n a fresh).blocks[b]? =
      if b = st.blocks.size then some ⟨n, (fresh.map MByte.byte).toArray, a, k⟩
      else st.blocks[b]? := by
  simp only [State.alloc, Array.getElem?_push]

theorem addrOf_alloc (st : H.State) (k : BlockKind) (n a : Nat) (fresh : List UInt8) (b : Nat) :
    (st.alloc k n a fresh).addrOf b = if b = st.blocks.size then a else st.addrOf b := by
  simp only [State.addrOf, alloc_get?]
  split <;> simp

theorem cell_alloc (st : H.State) (k : BlockKind) (n a : Nat) (fresh : List UInt8) (b i : Nat) :
    (st.alloc k n a fresh).cell b i =
      if b = st.blocks.size then (if h : i < fresh.length then .byte (fresh[i]'h) else .byte 0)
      else st.cell b i := by
  simp only [State.cell, alloc_get?]
  split
  · simp only [Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getElem?_map]
    split
    · next h => simp [List.getElem?_eq_getElem h]
    · next h => simp [List.getElem?_eq_none (by omega : fresh.length ≤ i)]
  · rfl

theorem bsize_alloc (st : H.State) (k : BlockKind) (n a : Nat) (fresh : List UInt8) (b : Nat) :
    (st.alloc k n a fresh).bsize b = if b = st.blocks.size then n else st.bsize b := by
  simp only [State.bsize, alloc_get?]
  split <;> simp

/-! ## Reads that agree -/

/-- A block whose bytes agree with the machine's from `A`: a range of it reads the machine's
    bytes there. -/
theorem bytes_of_agree {st : H.State} {m : ByteArray} {b o len A : Nat} (hb : b < st.blocks.size)
    (hag : ∀ i, i < len → mem m (A + i) = (st.cell b (o + i)).val st.addrOf) :
    m.readWithPadding A len = st.bytes (.at b o) len := by
  simp only [State.bytes, State.cells, cellsAt_eq hb]
  exact readWithPadding_of_mem (by simp) fun i hi => by simp [hag i hi]

/-! ## Words in cells -/

theorem wordBytes_size (x : Nat) : (wordBytes x).size = 32 :=
  Reasoning.Theory.toByteArray_size _

theorem toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  rw [Reasoning.Theory.byteArray_toList_eq, Array.length_toList]; rfl

/-- The 32 bytes of a word, by index, are its byte list. -/
theorem finRange_get! (bs : ByteArray) (h : bs.size = 32) :
    (List.finRange 32).map (fun (i : Fin 32) => bs.get! (i : Nat)) = bs.toList := by
  rw [Reasoning.Theory.byteArray_toList_eq]
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, Array.length_toList]
    exact h.symm
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rcases bs with ⟨arr⟩
    have hk : k < arr.size := by simpa using h2
    show arr[k]! = arr[k]
    exact getElem!_pos arr k hk

/-- The byte values of the cells a typed store writes are the 32 big-endian bytes of the
    stored value's word. -/
theorem cells_val (st : H.State) (v : H.Val) :
    v.cells.map (·.val st.addrOf) = (wordBytes (st.word v)).toList := by
  cases v with
  | int bits x =>
    simp only [H.Val.cells, List.map_map, Function.comp_def, MByte.val, List.map_id']
    rfl
  | ptr b o =>
    simp only [H.Val.cells, List.map_map]
    exact finRange_get! _ (wordBytes_size _)

theorem cells_length (v : H.Val) : v.cells.length = 32 := by
  cases v with
  | int bits x => simp only [H.Val.cells, List.length_map, toList_length, wordBytes_size]
  | ptr b o => simp [H.Val.cells]

theorem fragsOf_some {cs : List MByte} {b o : Nat} (h : fragsOf cs = some (b, o)) :
    cs = (List.finRange 32).map (.frag b o) := by
  unfold fragsOf at h
  split at h
  · split at h
    · next he =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact he
    · cases h
  · cases h

/-- A typed load gives the pointer whose fragments the cells are, or an integer whose value is
    the machine word of the cells' bytes. -/
theorem load_cases {st : H.State} {b o : Nat} {ty : Ty} {v : H.Val}
    (h : st.load b o ty = some v) :
    (∃ b' o', fragsOf (st.cellsAt b o 32) = some (b', o') ∧ v = .ptr b' o') ∨
      ∃ n, v = .int n (Ethereum.uInt256OfByteArray (st.bytes (.at b o) 32)).toNat := by
  unfold State.load at h
  simp only at h
  split at h <;> (try split at h) <;>
    first
    | (cases h; exact Or.inl ⟨_, _, by assumption, rfl⟩)
    | (cases h; exact Or.inr ⟨_, rfl⟩)
    | cases h

/-- The word of a typed load of 32 cells is the machine word of their byte values. -/
theorem load_word {st : H.State} {b o : Nat} {ty : Ty} {v : H.Val}
    (h : st.load b o ty = some v) :
    (Ethereum.uInt256OfByteArray (st.bytes (.at b o) 32)).toNat = st.word v := by
  rcases load_cases h with ⟨b', o', hf, rfl⟩ | ⟨n, rfl⟩
  · have hc := fragsOf_some hf
    have hb : st.bytes (.at b o) 32 = wordBytes ((st.addrOf b' + o') % 2 ^ 256) := by
      simp only [State.bytes, State.cells]
      rw [hc]
      have e := finRange_get! (wordBytes ((st.addrOf b' + o') % 2 ^ 256)) (wordBytes_size _)
      rw [Reasoning.Theory.byteArray_toList_eq] at e
      apply ByteArray.ext
      rw [← @Array.toArray_toList _ (wordBytes _).data, ← e, List.map_map]
      rfl
    rw [hb, wordBytes, Reasoning.Theory.uInt256OfByteArray_toByteArray]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))
  · rfl

end Fe.Sonatina.Stage3.Place
