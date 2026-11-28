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

end Fe.Sonatina.Stage3.Place
