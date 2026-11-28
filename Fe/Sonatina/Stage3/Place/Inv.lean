import Fe.Sonatina.Stage3.Place.Evm

/-!
# The simulation invariant of S14 (PLAN §4)

A machine state (world `w`, its memory the machine's bytes) is related to an H state `hst` by a
ghost `g` (`Ghost`): the machine base `j b` of each H block, fixed when the block is allocated,
the blocks whose bytes the machine still holds (`live`), and the heap blocks (`heap`).  `Inv`
is the relation, one structure whose fields the simulation lemmas use directly:

- the worlds agree but for memory; live blocks exist, hold as many cells as bytes, and do not
  wrap; H's address word of a block is its machine base unless that is 0, which happens only in
  address-0 mode (`zero`), where the proof chose H's word 1;
- live blocks have disjoint ranges, and the machine's bytes over each are the values of its cells;
- a cell of a live block is a byte or a fragment of a heap pointer (rule S3), never one in
  address-0 mode (rule S8: no derived value is stored);
- with a heap: the free-pointer word at `0x40` bounds every heap block's end and is bounded by
  `F0 + heapReq` (S5), heap blocks start at the heap floor `e`, frame blocks end below it and
  miss `[0x40, 0x60)` (S1, S4).

Values (`VRel`): an integer is its machine word; a pointer `ptr b o` is `(j b + o) mod 2 ^ 256`,
and in address-0 mode only a derived value (S8) is one.  `OrigOk` is rule S3's consequence: a
pointer is into a heap block, or into a live block whose range is that of one of the value's
`alloca` sites or misses the function's footprint when the value may come from a parameter.

The preservation lemmas: `inv_write` (a write of cells into a live block, the machine writing
their byte values), `inv_alloca`, `inv_heap` (an allocation: H's block where the machine puts
it, its fresh bytes the machine's), `inv_load` (a typed load's value is related), `inv_world`
(an operation on the world other than memory).
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-! ## Definitions -/

/-- The facts of a section the invariant depends on: the heap floor (the entry free pointer),
    whether the section has a heap site, whether it is in address-0 mode, and the bound `F0` of
    the heap bases (the largest of `e` and the `min_base`s). -/
structure SecFacts where
  e : Nat
  hasHeap : Bool
  z : Bool
  F0 : Nat

/-- The ghost state of the simulation. -/
structure Ghost where
  j : Nat → Nat
  live : Nat → Prop
  heap : Nat → Prop

/-- The machine range of block `b`. -/
def Ghost.rg (g : Ghost) (st : H.State) (b : Nat) : Nat × Nat := (g.j b, g.j b + st.bsize b)

/-- Two ranges `[lo, hi)` are disjoint, an empty one with every range (`disjoint` as a
    proposition). -/
def Disj (r s : Nat × Nat) : Prop := r.1 = r.2 ∨ s.1 = s.2 ∨ r.2 ≤ s.1 ∨ s.2 ≤ r.1

theorem disjoint_iff (r s : Nat × Nat) : disjoint r s = true ↔ Disj r s := by
  simp only [disjoint, Disj, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc]

/-- An address of a nonempty range is not in a range disjoint from it. -/
theorem Disj.out {lo n lo' n' i : Nat} (h : Disj (lo, lo + n) (lo', lo' + n')) (hi : i < n) :
    ¬ (lo' ≤ lo + i ∧ lo + i < lo' + n') := by
  unfold Disj at h; simp only at h; omega

/-- The machine's free-pointer word, at `0x40`. -/
def fpWord (m : ByteArray) : Nat :=
  (Ethereum.uInt256OfByteArray (m.readWithPadding 64 32)).toNat

/-- The simulation invariant. -/
structure Inv (S : SecFacts) (hst : H.State) (w : World) (g : Ghost) : Prop where
  world : { w with memory := hst.world.memory } = hst.world
  live_lt : ∀ b, g.live b → b < hst.blocks.size
  heap_live : ∀ b, g.heap b → g.live b
  heap_has : ∀ b, g.heap b → S.hasHeap = true
  bytes_size : ∀ (b : Nat) (blk : MemBlock), hst.blocks[b]? = some blk → blk.bytes.size = blk.size
  exact : ∀ b, b < hst.blocks.size → g.j b ≠ 0 → hst.addrOf b = g.j b
  zero : ∀ b, b < hst.blocks.size → g.j b = 0 → S.z = true
  bound : ∀ b, g.live b → g.j b + hst.bsize b < W
  disj : ∀ b b', g.live b → g.live b' → b ≠ b' → Disj (g.rg hst b) (g.rg hst b')
  bytes : ∀ b, g.live b → ∀ i, i < hst.bsize b →
    mem w.memory (g.j b + i) = (hst.cell b i).val hst.addrOf
  frags : ∀ b, g.live b → ∀ i, i < hst.bsize b → ∀ b' o k, hst.cell b i = .frag b' o k →
    g.heap b' ∧ o < W ∧ S.z = false
  e96 : S.hasHeap = true → 0x60 ≤ S.e
  heap_floor : ∀ b, g.heap b → S.e ≤ g.j b
  fp : S.hasHeap = true → S.e ≤ fpWord w.memory ∧ fpWord w.memory ≤ S.F0 + hst.heapReq ∧
    ∀ b, g.heap b → g.j b + hst.bsize b ≤ fpWord w.memory
  frame : S.hasHeap = true → ∀ b, g.live b → ¬ g.heap b →
    g.j b + hst.bsize b ≤ S.e ∧ Disj (g.rg hst b) (0x40, 0x60)

/-- A value is related to the machine word `m`: an integer is it; a pointer is its block's base
    plus its offset, and in address-0 mode only a derived value (`dx`) is a pointer. -/
def VRel (g : Ghost) (z dx : Bool) : H.Val → Nat → Prop
  | .int _ n, m => n = m
  | .ptr b o, m => (g.j b + o) % W = m ∧ (z = true → dx = true)

/-- A pointer is into a block that exists, at an offset below `2 ^ 256`. -/
def ValOk (st : H.State) : H.Val → Prop
  | .int .. => True
  | .ptr b o => b < st.blocks.size ∧ o < W

/-- Rule S3's consequence for a value with origins `os` (`0` a parameter, `s + 1` site `vs`) in
    a function whose `alloca` ranges are `R` and footprint `fpf`: a pointer is into a heap
    block, or into a live block whose range is one of its sites', or that misses the footprint
    when it may come from a parameter. -/
def OrigOk (g : Ghost) (st : H.State) (R : NatMap Range) (fpf : List Range) (os : List Nat) :
    H.Val → Prop
  | .int .. => True
  | .ptr b _ => g.heap b ∨ (g.live b ∧
      ((∃ s, s + 1 ∈ os ∧ R.find? s = some (g.rg st b)) ∨
        (0 ∈ os ∧ ∀ r ∈ fpf, Disj r (g.rg st b))))

/-! ## Values and words -/

/-- In the invariant, a related value's word in H is its machine word, unless it is a pointer in
    address-0 mode. -/
theorem vrel_word {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {dx : Bool} {v : H.Val} {m : Nat} (hv : VRel g S.z dx v m) (hok : ValOk hst v)
    (hnz : S.z = false ∨ ∀ b o, v ≠ .ptr b o) : hst.word v = m := by
  cases v with
  | int bits n => exact hv
  | ptr b o =>
    rcases hnz with hz | hp
    · have hj : g.j b ≠ 0 := fun h0 => by rw [hI.zero b hok.1 h0] at hz; cases hz
      rw [word_ptr, hI.exact b hok.1 hj]; exact hv.1
    · exact absurd rfl (hp b o)

/-! ## Writes -/

theorem fpWord_congr {m' m : ByteArray} (h : ∀ k, k < 32 → mem m' (64 + k) = mem m (64 + k)) :
    fpWord m' = fpWord m := by
  unfold fpWord
  rw [Check.readWithPadding_congr (fun i hi => h i hi)]

/-- A write of the cells `cs` at offset `o` of live block `b`, the machine writing their byte
    values over the same window and nothing else, keeps the invariant if every fragment it writes
    is one of a heap pointer at a word offset, outside address-0 mode. -/
theorem inv_write {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {b o : Nat} {cs : List MByte} {m' : ByteArray}
    (hb : g.live b) (hlen : o + cs.length ≤ hst.bsize b)
    (hm : ∀ i, mem m' i = if g.j b + o ≤ i ∧ i < g.j b + o + cs.length then
        ((cs[i - (g.j b + o)]?).getD (.byte 0)).val hst.addrOf else mem w.memory i)
    (hcs : ∀ c ∈ cs, ∀ b' o' k, c = .frag b' o' k → g.heap b' ∧ o' < W ∧ S.z = false) :
    Inv S (hst.write (.at b o) cs) { w with memory := m' } g := by
  have hbl := hI.live_lt b hb
  have hbs : hst.bsize b = hst.blocks[b].size := by
    simp [State.bsize, Array.getElem?_eq_getElem hbl]
  have hsz : o + cs.length ≤ hst.blocks[b].bytes.size := by
    rw [hI.bytes_size b _ (Array.getElem?_eq_getElem hbl)]; omega
  have hcell := fun b' i => cell_write hst b o cs b' i hbl hsz
  -- No address of another live block is in the window.
  have hout : ∀ b', g.live b' → b' ≠ b → ∀ i, i < hst.bsize b' →
      ¬ (g.j b + o ≤ g.j b' + i ∧ g.j b' + i < g.j b + o + cs.length) := by
    intro b' hb' hne i hi hw
    exact Disj.out (hI.disj b' b hb' hb hne) hi ⟨by omega, by omega⟩
  -- The window misses the free-pointer word.
  have hfp : S.hasHeap = true → ∀ k, k < 32 →
      ¬ (g.j b + o ≤ 64 + k ∧ 64 + k < g.j b + o + cs.length) := by
    intro hh k hk hw
    by_cases hhb : g.heap b
    · have := hI.heap_floor b hhb; have := hI.e96 hh; omega
    · have hd := (hI.frame hh b hb hhb).2
      unfold Disj Ghost.rg at hd; simp only at hd; omega
  refine ⟨?world, ?_, hI.heap_live, hI.heap_has, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.e96,
    hI.heap_floor, ?_, ?_⟩
  · exact hI.world
  · intro b' hb'; rw [write_blocks_size]; exact hI.live_lt b' hb'
  · intro b' blk' h'
    rw [write_blocks_get?] at h'
    cases hg : hst.blocks[b']? with
    | none => rw [hg] at h'; cases h'
    | some blk =>
      rw [hg] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      have := hI.bytes_size b' blk hg
      split
      · simp only; rw [foldl_set_size]; exact this
      · exact this
  · intro b' hb' hj; rw [addrOf_write]; exact hI.exact b' (by rwa [write_blocks_size] at hb') hj
  · intro b' hb' hj; exact hI.zero b' (by rwa [write_blocks_size] at hb') hj
  · intro b' hb'; rw [bsize_write]; exact hI.bound b' hb'
  · intro b1 b2 h1 h2 hne
    simp only [Ghost.rg, bsize_write]
    exact hI.disj b1 b2 h1 h2 hne
  · intro b' hb' i hi
    rw [bsize_write] at hi
    rw [addrOf_write, hcell, hm]
    by_cases hbb : b' = b
    · subst hbb
      by_cases hoi : o ≤ i
      · rw [if_pos (show b' = b' ∧ o ≤ i from ⟨rfl, hoi⟩)]
        by_cases hil : i < o + cs.length
        · rw [if_pos (show g.j b' + o ≤ g.j b' + i ∧ g.j b' + i < g.j b' + o + cs.length by omega),
            show g.j b' + i - (g.j b' + o) = i - o by omega, List.getElem?_eq_getElem (by omega)]
          rfl
        · rw [if_neg (show ¬ (g.j b' + o ≤ g.j b' + i ∧ g.j b' + i < g.j b' + o + cs.length) by omega),
            List.getElem?_eq_none (by omega)]
          exact hI.bytes b' hb' i hi
      · rw [if_neg (show ¬ (b' = b' ∧ o ≤ i) by omega),
          if_neg (show ¬ (g.j b' + o ≤ g.j b' + i ∧ g.j b' + i < g.j b' + o + cs.length) by omega)]
        exact hI.bytes b' hb' i hi
    · rw [if_neg (show ¬ (b' = b ∧ o ≤ i) by omega), if_neg (hout b' hb' hbb i hi)]
      exact hI.bytes b' hb' i hi
  · intro b' hb' i hi b2 o2 k hc
    rw [bsize_write] at hi
    rw [hcell] at hc
    split at hc
    · next hw =>
      cases hx : cs[i - o]? with
      | none => rw [hx] at hc; exact hI.frags b' hb' i hi b2 o2 k hc
      | some c =>
        rw [hx] at hc
        exact hcs c (List.mem_of_getElem? hx) b2 o2 k hc
    · exact hI.frags b' hb' i hi b2 o2 k hc
  · intro hh
    have he : fpWord m' = fpWord w.memory :=
      fpWord_congr fun k hk => by rw [hm, if_neg (hfp hh k hk)]
    obtain ⟨h1, h2, h3⟩ := hI.fp hh
    refine ⟨he ▸ h1, he ▸ h2, fun b' hb' => ?_⟩
    rw [bsize_write, he]; exact h3 b' hb'
  · intro hh b' hb' hnh
    simp only [Ghost.rg, bsize_write]
    exact hI.frame hh b' hb' hnh

/-! ## Allocation -/

theorem Disj.symm {r s : Nat × Nat} (h : Disj r s) : Disj s r := by
  unfold Disj at *; omega

theorem val_congr {c : MByte} {a a' : Nat → Nat} (h : ∀ b o k, c = .frag b o k → a b = a' b) :
    c.val a = c.val a' := by
  cases c with
  | byte x => rfl
  | frag b o k => simp only [MByte.val, h b o k rfl]

/-- The ghost with block `k` added at machine base `A`, kept live with the old blocks `keep`
    holds of, a heap block if `isHeap`. -/
def Ghost.add (g : Ghost) (k A : Nat) (keep : Nat → Prop) (isHeap : Prop) : Ghost where
  j b := if b = k then A else g.j b
  live b := b = k ∨ (b ≠ k ∧ keep b)
  heap b := (b = k ∧ isHeap) ∨ (b ≠ k ∧ g.heap b)

theorem Ghost.add_j_old {g : Ghost} {k A : Nat} {keep : Nat → Prop} {p : Prop} {b : Nat}
    (h : b ≠ k) : (g.add k A keep p).j b = g.j b := by simp [Ghost.add, h]

/-- The fresh bytes of a block the machine puts at `A`: the machine's there. -/
def freshAt (m : ByteArray) (A n : Nat) : List UInt8 := (List.range n).map fun i => mem m (A + i)

theorem freshAt_length (m : ByteArray) (A n : Nat) : (freshAt m A n).length = n := by
  simp [freshAt]

theorem alloc_size (st : H.State) (k : BlockKind) (n a : Nat) (fresh : List UInt8) :
    (st.alloc k n a fresh).blocks.size = st.blocks.size + 1 := by
  simp [State.alloc]

/-- An allocation of `n` bytes at machine base `A` keeps the invariant: H's address word `a` is
    `A` unless `A` is 0 (address-0 mode), its fresh bytes are the machine's there, the old blocks
    `keep` holds of stay live (disjoint from the new one, and every heap block among them), the
    machine changes no byte but the free-pointer word's, and the free-pointer facts hold after. -/
theorem inv_add {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {kind : BlockKind} {A n a R : Nat} {m' : ByteArray} {keep : Nat → Prop} {isHeap : Prop}
    (ha : A ≠ 0 → a = A) (hz : A = 0 → S.z = true) (hA : A + n < W)
    (hkeep : ∀ b, keep b → g.live b ∧ Disj (g.rg hst b) (A, A + n))
    (hheap : ∀ b, g.heap b → keep b)
    (hih : isHeap → S.hasHeap = true ∧ S.e ≤ A)
    (hframe : S.hasHeap = true → ¬ isHeap → A + n ≤ S.e ∧ Disj (A, A + n) (0x40, 0x60))
    (hm : ∀ i, mem m' i ≠ mem w.memory i → S.hasHeap = true ∧ 64 ≤ i ∧ i < 96)
    (hfp : S.hasHeap = true → S.e ≤ fpWord m' ∧ fpWord m' ≤ S.F0 + R ∧
      (isHeap → A + n ≤ fpWord m') ∧ ∀ b, g.heap b → g.j b + hst.bsize b ≤ fpWord m') :
    Inv S { hst.alloc kind n a (freshAt w.memory A n) with heapReq := R } { w with memory := m' }
      (g.add hst.blocks.size A keep isHeap) := by
  set k := hst.blocks.size with hk
  set g' := g.add k A keep isHeap
  have hlt : ∀ b, g.live b → b < k := hI.live_lt
  have hne : ∀ b, g.live b → b ≠ k := fun b hb => by have := hlt b hb; omega
  have hj : ∀ b, b ≠ k → g'.j b = g.j b := fun b h => Ghost.add_j_old h
  have hjk : g'.j k = A := by simp [g', Ghost.add]
  have hsz : ∀ b, b ≠ k → (hst.alloc kind n a (freshAt w.memory A n)).bsize b = hst.bsize b :=
    fun b h => by rw [bsize_alloc, if_neg h]
  have hszk : (hst.alloc kind n a (freshAt w.memory A n)).bsize k = n := by
    rw [bsize_alloc, if_pos rfl]
  have hadr : ∀ b, b ≠ k → (hst.alloc kind n a (freshAt w.memory A n)).addrOf b = hst.addrOf b :=
    fun b h => by rw [addrOf_alloc, if_neg h]
  have hrg : ∀ b, b ≠ k → g'.rg { hst.alloc kind n a (freshAt w.memory A n) with heapReq := R } b =
      g.rg hst b := fun b h => by
    simp only [Ghost.rg, hj b h]; rw [show ({ hst.alloc kind n a (freshAt w.memory A n) with
      heapReq := R } : H.State).bsize b = (hst.alloc kind n a (freshAt w.memory A n)).bsize b
      from rfl, hsz b h]
  have hrgk : g'.rg { hst.alloc kind n a (freshAt w.memory A n) with heapReq := R } k = (A, A + n) := by
    simp only [Ghost.rg, hjk]
    rw [show ({ hst.alloc kind n a (freshAt w.memory A n) with heapReq := R } : H.State).bsize k =
      (hst.alloc kind n a (freshAt w.memory A n)).bsize k from rfl, hszk]
  have hlive : ∀ b, g'.live b ↔ b = k ∨ (b ≠ k ∧ keep b) := fun b => Iff.rfl
  have hheap' : ∀ b, g'.heap b ↔ (b = k ∧ isHeap) ∨ (b ≠ k ∧ g.heap b) := fun b => Iff.rfl
  -- A byte the machine changed is in the free-pointer word, which no live block and not the new
  -- block holds.
  have hmem_old : ∀ b, g.live b → ∀ i, i < hst.bsize b → mem m' (g.j b + i) = mem w.memory (g.j b + i) := by
    intro b hb i hi
    by_contra hc
    obtain ⟨hh, h1, h2⟩ := hm _ hc
    by_cases hhb : g.heap b
    · have := hI.heap_floor b hhb; have := hI.e96 hh; omega
    · have hd := (hI.frame hh b hb hhb).2
      unfold Disj Ghost.rg at hd; simp only at hd; omega
  have hmem_new : ∀ i, i < n → mem m' (A + i) = mem w.memory (A + i) := by
    intro i hi
    by_contra hc
    obtain ⟨hh, h1, h2⟩ := hm _ hc
    by_cases hih' : isHeap
    · have := (hih hih').2; have := hI.e96 hh; omega
    · have hd := (hframe hh hih').2
      unfold Disj at hd; simp only at hd; omega
  have hval : ∀ b i, g.live b → i < hst.bsize b →
      (hst.cell b i).val (hst.alloc kind n a (freshAt w.memory A n)).addrOf =
        (hst.cell b i).val hst.addrOf := by
    intro b i hb hi
    apply val_congr
    intro b2 o2 k2 hc
    have := (hI.frags b hb i hi b2 o2 k2 hc).1
    exact hadr b2 (hne b2 (hI.heap_live b2 this))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.e96, ?_, ?_, ?_⟩
  · exact hI.world
  · intro b hb
    show b < (hst.alloc kind n a (freshAt w.memory A n)).blocks.size
    rw [alloc_size]
    rcases hb with rfl | ⟨_, hb⟩
    · omega
    · have := hlt b (hkeep b hb).1; omega
  · intro b hb
    rcases hb with ⟨rfl, _⟩ | ⟨hb, hh⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hb, hheap b hh⟩
  · intro b hb
    rcases hb with ⟨rfl, hh⟩ | ⟨_, hh⟩
    · exact (hih hh).1
    · exact hI.heap_has b hh
  · intro b blk h
    change (hst.alloc kind n a (freshAt w.memory A n)).blocks[b]? = some blk at h
    rw [alloc_get?] at h
    split at h
    · cases h; simp [freshAt_length]
    · exact hI.bytes_size b blk h
  · intro b hb hjb
    change b < (hst.alloc kind n a (freshAt w.memory A n)).blocks.size at hb
    change (hst.alloc kind n a (freshAt w.memory A n)).addrOf b = _
    rw [alloc_size] at hb
    by_cases hbk : b = k
    · subst hbk; rw [addrOf_alloc, if_pos rfl, hjk]; rw [hjk] at hjb; exact ha hjb
    · rw [hadr b hbk, hj b hbk]; rw [hj b hbk] at hjb; exact hI.exact b (by omega) hjb
  · intro b hb hjb
    change b < (hst.alloc kind n a (freshAt w.memory A n)).blocks.size at hb
    rw [alloc_size] at hb
    by_cases hbk : b = k
    · subst hbk; rw [hjk] at hjb; exact hz hjb
    · rw [hj b hbk] at hjb; exact hI.zero b (by omega) hjb
  · intro b hb
    change g'.j b + (hst.alloc kind n a (freshAt w.memory A n)).bsize b < W
    rcases hb with rfl | ⟨hbk, hb⟩
    · rw [hjk, hszk]; exact hA
    · rw [hj b hbk, hsz b hbk]; exact hI.bound b (hkeep b hb).1
  · intro b1 b2 h1 h2 hne12
    rcases h1 with rfl | ⟨hb1, h1⟩ <;> rcases h2 with rfl | ⟨hb2, h2⟩
    · exact absurd rfl hne12
    · rw [hrgk, hrg b2 hb2]; exact (hkeep b2 h2).2.symm
    · rw [hrgk, hrg b1 hb1]; exact (hkeep b1 h1).2
    · rw [hrg b1 hb1, hrg b2 hb2]; exact hI.disj b1 b2 (hkeep b1 h1).1 (hkeep b2 h2).1 hne12
  · intro b hb i hi
    change i < (hst.alloc kind n a (freshAt w.memory A n)).bsize b at hi
    change mem m' (g'.j b + i) = ((hst.alloc kind n a (freshAt w.memory A n)).cell b i).val
      (hst.alloc kind n a (freshAt w.memory A n)).addrOf
    rcases hb with rfl | ⟨hbk, hb⟩
    · rw [hszk] at hi
      rw [hjk, cell_alloc, if_pos rfl, dif_pos (by rw [freshAt_length]; exact hi), hmem_new i hi]
      simp [MByte.val, freshAt]
    · have hl := (hkeep b hb).1
      rw [hsz b hbk] at hi
      rw [hj b hbk, cell_alloc, if_neg hbk, hval b i hl hi, hmem_old b hl i hi]
      exact hI.bytes b hl i hi
  · intro b hb i hi b2 o2 k2 hc
    change i < (hst.alloc kind n a (freshAt w.memory A n)).bsize b at hi
    change (hst.alloc kind n a (freshAt w.memory A n)).cell b i = _ at hc
    rcases hb with rfl | ⟨hbk, hb⟩
    · rw [cell_alloc, if_pos rfl] at hc
      split at hc <;> cases hc
    · rw [cell_alloc, if_neg hbk] at hc
      rw [hsz b hbk] at hi
      obtain ⟨h1, h2, h3⟩ := hI.frags b (hkeep b hb).1 i hi b2 o2 k2 hc
      exact ⟨Or.inr ⟨hne b2 (hI.heap_live b2 h1), h1⟩, h2, h3⟩
  · intro b hb
    rcases hb with ⟨rfl, hh⟩ | ⟨hbk, hh⟩
    · rw [hjk]; exact (hih hh).2
    · rw [hj b hbk]; exact hI.heap_floor b hh
  · intro hh
    obtain ⟨h1, h2, h3, h4⟩ := hfp hh
    refine ⟨h1, h2, fun b hb => ?_⟩
    change g'.j b + (hst.alloc kind n a (freshAt w.memory A n)).bsize b ≤ fpWord m'
    rcases hb with ⟨rfl, hih'⟩ | ⟨hbk, hb⟩
    · rw [hjk, hszk]; exact h3 hih'
    · rw [hj b hbk, hsz b hbk]; exact h4 b hb
  · intro hh b hb hnh
    rw [hheap'] at hnh
    rcases hb with rfl | ⟨hbk, hb⟩
    · have hni : ¬ isHeap := fun h => hnh (Or.inl ⟨rfl, h⟩)
      rw [hrgk]
      change g'.j _ + (hst.alloc kind n a (freshAt w.memory A n)).bsize _ ≤ S.e ∧ _
      rw [hjk, hszk]; exact hframe hh hni
    · have hng : ¬ g.heap b := fun h => hnh (Or.inr ⟨hbk, h⟩)
      rw [hrg b hbk]
      change g'.j b + (hst.alloc kind n a (freshAt w.memory A n)).bsize b ≤ S.e ∧ _
      rw [hj b hbk, hsz b hbk]
      exact hI.frame hh b (hkeep b hb).1 hng

/-- An `alloca` of `n` bytes at machine base `A` (its record word's address): H's block where
    the machine has it (at address word 1 if that is 0), holding the machine's bytes there; the
    old blocks that miss it stay live. -/
theorem inv_alloca {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    {A n : Nat} (hA : A + n < 2 ^ 32) (hz : A = 0 → S.z = true)
    (hh : S.hasHeap = true → A + n ≤ S.e ∧ Disj (A, A + n) (0x40, 0x60)) :
    AddrOk (if A = 0 then 1 else A) n ∧
    Inv S (hst.alloc .alloca n (if A = 0 then 1 else A) (freshAt w.memory A n)) w
      (g.add hst.blocks.size A (fun b => g.live b ∧ Disj (g.rg hst b) (A, A + n)) False) := by
  have hW : (2 : Nat) ^ 32 < W := by unfold W; norm_num
  refine ⟨⟨by split <;> omega, by split <;> omega⟩, ?_⟩
  refine inv_add (R := hst.heapReq) (m' := w.memory) hI (fun h => if_neg h) hz (by omega)
    (fun b h => h) (fun b hb => ⟨hI.heap_live b hb, ?_⟩) (fun h => h.elim)
    (fun hh' _ => hh hh') (fun i h => absurd rfl h) (fun hh' => ?_)
  · have hhs := hI.heap_has b hb
    have := (hh hhs).1; have := hI.heap_floor b hb
    unfold Disj Ghost.rg; simp only; omega
  · obtain ⟨h1, h2, h3⟩ := hI.fp hh'
    exact ⟨h1, h2, fun h => h.elim, h3⟩

theorem align32_ge (n : Nat) : n ≤ align32 n := by unfold align32; omega

/-- The machine's free-pointer word after it stores `x` there. -/
theorem fpWord_mstore (m : ByteArray) (x : Nat) :
    fpWord ((Ethereum.UInt256.ofNat x).toByteArray.write 0 m 64 32) = x % W := by
  unfold fpWord
  have hT := Reasoning.Theory.toByteArray_size (Ethereum.UInt256.ofNat x)
  have e : ((Ethereum.UInt256.ofNat x).toByteArray.write 0 m 64 32).readWithPadding 64 32 =
      (Ethereum.UInt256.ofNat x).toByteArray := by
    rw [readWithPadding_of_mem (l := (Ethereum.UInt256.ofNat x).toByteArray.toList)
      (by rw [toList_length, hT]) (fun i hi => ?_)]
    · apply ByteArray.ext; rw [Reasoning.Theory.byteArray_toList_eq]
    · rw [mem_write, if_pos ⟨by omega, by omega⟩, show 0 + (64 + i - 64) = i by omega]
      simp only [Reasoning.Theory.byteArray_toList_eq, Array.getElem_toList,
        Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; omega)]
      rfl
  rw [e, Reasoning.Theory.uInt256OfByteArray_toByteArray]
  rfl

/-- A heap `evm_malloc` of `n` bytes within the budget at machine base `base`, at or above the
    free pointer and at most `F0 + heapReq`, the machine then bumping the free pointer to
    `base + align32 n`: H's block where the machine has it, holding the machine's bytes there;
    every live block stays live. -/
theorem inv_heap {S : SecFacts} {hst : H.State} {w : World} {g : Ghost} (hI : Inv S hst w g)
    (hh : S.hasHeap = true) {base n : Nat} (hbase : fpWord w.memory ≤ base)
    (hbF : base ≤ S.F0 + hst.heapReq) (hbud : hst.heapReq + align32 n < heapBudget)
    (hF0 : S.F0 < 2 ^ 32) :
    AddrOk base n ∧
    Inv S { hst.alloc .malloc n base (freshAt w.memory base n) with
        heapReq := hst.heapReq + align32 n }
      { w with memory := (Ethereum.UInt256.ofNat (base + align32 n)).toByteArray.write 0 w.memory 64 32 }
      (g.add hst.blocks.size base g.live True) := by
  have hb' : hst.heapReq + align32 n < 2 ^ 255 := hbud
  have han := align32_ge n
  obtain ⟨hf1, hf2, hf3⟩ := hI.fp hh
  have he := hI.e96 hh
  have hend : base + align32 n < 2 ^ 256 := by omega
  refine ⟨⟨by omega, lt_of_le_of_lt (by omega : base + n ≤ base + align32 n) hend⟩, ?_⟩
  refine inv_add (R := hst.heapReq + align32 n)
    (m' := (Ethereum.UInt256.ofNat (base + align32 n)).toByteArray.write 0 w.memory 64 32) hI (fun _ => rfl) (fun h => by omega)
    (lt_of_le_of_lt (by omega : base + n ≤ base + align32 n) hend)
    (fun b hb => ⟨hb, ?_⟩) (fun b hb => hI.heap_live b hb) (fun _ => ⟨hh, by omega⟩)
    (fun _ h => (h trivial).elim) (fun i hi => ?_) (fun _ => ?_)
  · unfold Disj Ghost.rg; simp only
    by_cases hhb : g.heap b
    · have := hf3 b hhb; omega
    · have := (hI.frame hh b hb hhb).1; omega
  · rw [mem_write] at hi
    split at hi
    · exact ⟨hh, by omega⟩
    · exact absurd rfl hi
  · rw [fpWord_mstore, Nat.mod_eq_of_lt hend]
    exact ⟨by omega, by omega, fun _ => by omega, fun b hb => by have := hf3 b hb; omega⟩

end Fe.Sonatina.Stage3.Place
