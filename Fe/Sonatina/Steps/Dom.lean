import Fe.Sonatina.Steps.NatMap
import Fe.Sonatina.Plan

/-!
# Dominators, computed and validated (design §4.1, review H-1)

`domTree f` computes immediate dominators by the iterative algorithm of Cooper, Harvey and
Kennedy over reverse postorder; nothing about it is proved.  `DomTree.valid` checks the result
on a reachable set `R` that it checks closed (the entry is in it, and the successors of its
blocks): the entry has no `idom`; every other block of `R` has one in `R`; for every edge
`p → b` with `p ∈ R` and `b` not the entry, `idom b` is an ancestor-or-self of `p`; and the
entry is an ancestor-or-self of every block of `R` (`valid_root`), so `idom` has no cycle on the
blocks of `R`, reachable or not (review 6, F-8).

D1 (`DomTree.dominates`): in a valid tree, an ancestor-or-self `d` of `b` lies on every path
from the entry to `b`.  By induction on the path.  Ancestry is the inductive `Anc` (`idom`
steps); the checker's `anc` climbs at most as many steps as the function has blocks, and is
sound for `Anc` (`anc_sound`), so a cycle in `idom` can only make the checker reject.
-/

namespace Fe.Sonatina.Steps

/-- The successors of each block. -/
def succMap (f : Func) : NatMap (List Nat) := .ofList (f.blocks.map fun b => (b.id, b.term.succs))

/-- The successors of each block, each once: what the computation walks, so that the number of
    edges, and the fuel, is bounded by the square of the number of blocks (a `br_table` repeats
    targets).  The validation reads `succMap`. -/
def succMapOnce (f : Func) : NatMap (List Nat) :=
  .ofList (f.blocks.map fun b => (b.id, b.term.succs.eraseDups))

def succsOf (S : NatMap (List Nat)) (b : Nat) : List Nat := (S.find? b).getD []

/-- The blocks reachable from `entry`, by a worklist of at most `fuel` steps. -/
def reachAux (S : NatMap (List Nat)) : Nat → List Nat → NatMap Unit → NatMap Unit
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, b :: work, seen =>
    if (seen.find? b).isSome then reachAux S fuel work seen
    else reachAux S fuel (succsOf S b ++ work) (seen.insert b ())

/-- Postorder of a depth-first search, by an explicit stack of at most `fuel` steps: entries
    `(b, true)` emit `b`, `(b, false)` visit it. -/
def postAux (S : NatMap (List Nat)) : Nat → List (Nat × Bool) → NatMap Unit → List Nat →
    List Nat
  | 0, _, _, acc => acc
  | _ + 1, [], _, acc => acc
  | fuel + 1, (b, true) :: st, seen, acc => postAux S fuel st seen (b :: acc)
  | fuel + 1, (b, false) :: st, seen, acc =>
    if (seen.find? b).isSome then postAux S fuel st seen acc
    else postAux S fuel ((succsOf S b).map (·, false) ++ (b, true) :: st) (seen.insert b ()) acc

/-- A dominator tree: each block's immediate dominator. -/
structure DomTree where
  idom : NatMap Nat
  /-- The reachable set the tree claims. -/
  reach : NatMap Unit
  /-- At least the number of blocks: the bound on climbing. -/
  size : Nat

/-- `d` is `b` or an ancestor of `b`, climbing at most `fuel` steps. -/
def DomTree.ancAux (T : DomTree) (d : Nat) : Nat → Nat → Bool
  | 0, b => b == d
  | fuel + 1, b => b == d || match T.idom.find? b with
    | some p => T.ancAux d fuel p
    | none => false

/-- `d` is an ancestor-or-self of `b`. -/
def DomTree.anc (T : DomTree) (d b : Nat) : Bool := T.ancAux d T.size b

/-- Compute the tree: the iterative algorithm, `idom` of the entry removed at the end. -/
def domTree (f : Func) : DomTree :=
  let S := succMapOnce f
  let n := f.blocks.length
  match f.blocks.head? with
  | none => ⟨.empty, .empty, n⟩
  | some e =>
    let post := (postAux S (4 * n * (n + 1) + 4) [(e.id, false)] .empty []).reverse
    -- postorder numbers, and the predecessors of each block
    let num : NatMap Nat := .ofList (post.zipIdx.map fun (b, i) => (b, i))
    let preds : NatMap (List Nat) := f.blocks.foldl (fun m b =>
      b.term.succs.eraseDups.foldl (fun m s => m.insert s (b.id :: (m.find? s).getD [])) m) .empty
    let rpo := post.reverse
    let numOf := fun b => (num.find? b).getD 0
    let rec inter (idom : NatMap Nat) : Nat → Nat → Nat → Nat
      | 0, a, _ => a
      | fuel + 1, a, b =>
        if a = b then a
        else if numOf a < numOf b then inter idom fuel ((idom.find? a).getD a) b
        else inter idom fuel a ((idom.find? b).getD b)
    -- One round over reverse postorder; whether it changed anything.
    let round (idom : NatMap Nat) : NatMap Nat × Bool := rpo.foldl (fun (idom, ch) b =>
      if b = e.id then (idom, ch) else
      match ((preds.find? b).getD []).filter (fun p => (idom.find? p).isSome) with
      | [] => (idom, ch)
      | p :: ps =>
        let d := ps.foldl (fun a q => inter idom (2 * n + 2) a q) p
        if idom.find? b == some d then (idom, ch) else (idom.insert b d, true)) (idom, false)
    let rec iter : Nat → NatMap Nat → NatMap Nat
      | 0, idom => idom
      | k + 1, idom => match round idom with
        | (idom, true) => iter k idom
        | (idom, false) => idom
    let idom := iter (n + 2) (NatMap.empty.insert e.id e.id)
    -- the entry has no immediate dominator
    let idom := rpo.foldl (fun m b => if b = e.id then m else
      match idom.find? b with | some d => m.insert b d | none => m) .empty
    ⟨idom, reachAux S (4 * n * (n + 1) + 4) [e.id] .empty, n⟩

/-- The validation of a tree for `f`. -/
def DomTree.valid (T : DomTree) (f : Func) : Bool :=
  let S := succMap f
  match f.blocks.head? with
  | none => false
  | some e =>
    let inR := fun b => (T.reach.find? b).isSome
    inR e.id && (T.idom.find? e.id).isNone && T.size ≥ f.blocks.length &&
    (f.blocks.all fun blk => !inR blk.id ||
      ((blk.id == e.id || match T.idom.find? blk.id with
        | some d => inR d
        | none => false) &&
       (succsOf S blk.id).all fun b => inR b && (b == e.id || match T.idom.find? b with
         | some d => T.anc d blk.id
         | none => false))) &&
    f.blocks.all fun blk => !inR blk.id || T.anc e.id blk.id

/-! ## D1 -/

/-- Ancestry in the tree: by steps from a block to its immediate dominator. -/
inductive DomTree.Anc (T : DomTree) (d : Nat) : Nat → Prop
  | refl : DomTree.Anc T d d
  | step {b p : Nat} : T.idom.find? b = some p → DomTree.Anc T d p → DomTree.Anc T d b

theorem DomTree.Anc.trans {T : DomTree} {d m b : Nat} (h₁ : T.Anc d m) (h₂ : T.Anc m b) :
    T.Anc d b := by
  induction h₂ with
  | refl => exact h₁
  | step hp _ ih => exact .step hp ih

theorem DomTree.ancAux_sound {T : DomTree} {d : Nat} :
    ∀ fuel b, T.ancAux d fuel b = true → T.Anc d b
  | 0, b, h => by simp only [ancAux, beq_iff_eq] at h; subst h; exact .refl
  | fuel + 1, b, h => by
    simp only [ancAux, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · rcases hp : T.idom.find? b with _ | p
      · rw [hp] at h; cases h
      · rw [hp] at h; exact .step hp (ancAux_sound fuel p h)

theorem DomTree.anc_sound {T : DomTree} {d b : Nat} (h : T.anc d b = true) : T.Anc d b :=
  ancAux_sound _ _ h

/-- An edge of `f`. -/
def Edge (f : Func) (p b : Nat) : Prop := ∃ blk, f.block? p = some blk ∧ b ∈ blk.term.succs

/-- A path from the entry `e` of `f` to `b`, the blocks it passes listed. -/
inductive Path (f : Func) (e : Nat) : Nat → List Nat → Prop
  | start : Path f e e [e]
  | edge {p b : Nat} {bs : List Nat} : Path f e p bs → Edge f p b → Path f e b (b :: bs)

theorem lookup_succs {p : Nat} {blk : Block} :
    ∀ {l : List Block}, l.find? (·.id == p) = some blk →
      (l.map fun b => (b.id, b.term.succs)).lookup p = some blk.term.succs
  | [], h => by cases h
  | a :: l, h => by
    simp only [List.find?_cons] at h
    simp only [List.map_cons, List.lookup_cons]
    by_cases ha : a.id = p
    · simp only [ha, beq_self_eq_true] at h ⊢
      cases h; rfl
    · simp only [show (a.id == p) = false by simpa using ha] at h
      simp only [show (p == a.id) = false by simpa using Ne.symm ha]
      exact lookup_succs h

theorem succMap_find (f : Func) (p : Nat) {blk : Block} (h : f.block? p = some blk) :
    succsOf (succMap f) p = blk.term.succs := by
  unfold succsOf succMap
  rw [NatMap.find?_ofList, lookup_succs h]
  rfl

/-- D1: in a tree the validation accepts, an ancestor-or-self of a block lies on every path
    from the entry to it. -/
theorem DomTree.dominates {T : DomTree} {f : Func} {e : Block} (hv : T.valid f = true)
    (he : f.blocks.head? = some e) {d b : Nat} {bs : List Nat} (hp : Path f e.id b bs)
    (ha : T.Anc d b) : d ∈ bs := by
  simp only [valid, he, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨hre, hroot⟩, _⟩, hblocks⟩, _⟩ := hv
  -- Every block of a path is in the reachable set.
  have hreach : ∀ {b bs}, Path f e.id b bs → (T.reach.find? b).isSome = true := by
    intro b bs hp
    induction hp with
    | start => exact hre
    | @edge p b bs _ hedge ih =>
      obtain ⟨blk, hblk, hb⟩ := hedge
      have hmem := List.mem_of_find?_eq_some hblk
      have hid : blk.id = p := by simpa using List.find?_some hblk
      rcases hblocks blk hmem with h | ⟨_, hs⟩
      · rw [hid] at h; rw [ih] at h; cases h
      · have := hs b (by rw [hid, succMap_find f p hblk]; exact hb)
        exact this.1
  induction hp generalizing d with
  | start =>
    cases ha with
    | refl => exact List.mem_singleton_self _
    | step hp' _ => rw [hroot] at hp'; cases hp'
  | @edge p b bs hpath hedge ih =>
    cases ha with
    | refl => exact List.mem_cons_self ..
    | @step _ i hi hai =>
      obtain ⟨blk, hblk, hb⟩ := hedge
      have hmem := List.mem_of_find?_eq_some hblk
      have hid : blk.id = p := by simpa using List.find?_some hblk
      rcases hblocks blk hmem with h | ⟨_, hs⟩
      · rw [hid, hreach hpath] at h; cases h
      have := hs b (by rw [hid, succMap_find f p hblk]; exact hb)
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
      rcases this.2 with hbe | hd
      · subst hbe; rw [hroot] at hi; cases hi
      · rw [hi] at hd
        rw [hid] at hd
        exact List.mem_cons_of_mem _ (ih (hai.trans (anc_sound hd)))

/-- In a valid tree the entry is an ancestor-or-self of every block of the reachable set. -/
theorem DomTree.valid_root {T : DomTree} {f : Func} {e : Block} (hv : T.valid f = true)
    (he : f.blocks.head? = some e) {blk : Block} (hb : blk ∈ f.blocks)
    (hr : (T.reach.find? blk.id).isSome = true) : T.Anc e.id blk.id := by
  simp only [valid, he, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, decide_eq_true_eq] at hv
  rcases hv.2 blk hb with h | h
  · rw [hr] at h; cases h
  · exact anc_sound h

end Fe.Sonatina.Steps
