import Mathlib.Tactic.SplitIfs

/-!
# A map on naturals the kernel reduces

A binary trie on the bits of the key, least significant bit first.  Lookup recurses on the
trie, insertion on a fuel that is the key itself, so both are structurally recursive: the kernel
evaluates them with no well-founded recursion, as `PcTree` in `Decode.lean`.  The keys are value,
instruction and block ids, below `2 ^ 32`; a lookup takes at most 32 steps.
-/

namespace Fe.Sonatina.Steps

/-- A map from naturals to `α`: the entry of key 0, and the tries of the even and the odd keys,
    halved. -/
inductive NatMap (α : Type) where
  | empty
  | node (here : Option α) (zero one : NatMap α)
  deriving Inhabited

namespace NatMap

variable {α : Type}

def find? : NatMap α → Nat → Option α
  | .empty, _ => none
  | .node h z o, k => if k = 0 then h else if k % 2 = 0 then z.find? (k / 2) else o.find? (k / 2)

/-- Insert at key `k`, with fuel at least `k`. -/
def insertAux (v : α) : Nat → NatMap α → Nat → NatMap α
  | _, .empty, 0 => .node (some v) .empty .empty
  | _, .node _ z o, 0 => .node (some v) z o
  | 0, t, _ + 1 => t
  | fuel + 1, .empty, k@(_ + 1) =>
    if k % 2 = 0 then .node none (insertAux v fuel .empty (k / 2)) .empty
    else .node none .empty (insertAux v fuel .empty (k / 2))
  | fuel + 1, .node h z o, k@(_ + 1) =>
    if k % 2 = 0 then .node h (insertAux v fuel z (k / 2)) o
    else .node h z (insertAux v fuel o (k / 2))

def insert (t : NatMap α) (k : Nat) (v : α) : NatMap α := insertAux v k t k

@[simp] theorem find?_empty (k : Nat) : (empty : NatMap α).find? k = none := rfl

theorem find?_insertAux (v : α) :
    ∀ (fuel : Nat) (t : NatMap α) (k k' : Nat), k ≤ fuel →
      (insertAux v fuel t k).find? k' = if k' = k then some v else t.find? k'
  | fuel, .empty, 0, k', _ => by
    cases fuel <;> simp only [insertAux, find?] <;> split_ifs <;> (first | omega | rfl)
  | fuel, .node h z o, 0, k', _ => by
    cases fuel <;> simp only [insertAux, find?] <;> split_ifs <;> (first | omega | rfl)
  | 0, t, k + 1, k', hk => by omega
  | fuel + 1, .empty, k + 1, k', hk => by
    have hf : (k + 1) / 2 ≤ fuel := by omega
    have IH := fun t k' => find?_insertAux v fuel t ((k + 1) / 2) k' hf
    unfold insertAux
    split_ifs <;> simp only [find?, IH] <;> split_ifs <;> (first | omega | rfl)
  | fuel + 1, .node h z o, k + 1, k', hk => by
    have hf : (k + 1) / 2 ≤ fuel := by omega
    have IH := fun t k' => find?_insertAux v fuel t ((k + 1) / 2) k' hf
    unfold insertAux
    split_ifs <;> simp only [find?, IH] <;> split_ifs <;> (first | omega | rfl)

@[simp] theorem find?_insert (t : NatMap α) (k k' : Nat) (v : α) :
    (t.insert k v).find? k' = if k' = k then some v else t.find? k' :=
  find?_insertAux v k t k k' (Nat.le_refl k)

/-- The map of a list of entries: a key's entry is its first in the list. -/
def ofList (l : List (Nat × α)) : NatMap α := l.foldr (fun e m => m.insert e.1 e.2) .empty

theorem find?_ofList (l : List (Nat × α)) (k : Nat) : (ofList l).find? k = l.lookup k := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [ofList, List.foldr_cons] at ih ⊢
    rw [find?_insert, ih]
    by_cases h : k = e.1
    · simp [List.lookup, h]
    · have h' : (k == e.1) = false := by simpa using h
      simp [List.lookup, h, h']

/-- The map of a list keyed by a function of its elements: an element is the first of its
    key. -/
def ofListBy (key : α → Nat) (l : List α) : NatMap α := l.foldr (fun a m => m.insert (key a) a) .empty

theorem find?_ofListBy (key : α → Nat) (l : List α) (k : Nat) :
    (ofListBy key l).find? k = l.find? (key · == k) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [ofListBy, List.foldr_cons] at ih ⊢
    rw [find?_insert, ih]
    by_cases h : k = key a
    · simp [List.find?, h]
    · have h' : (key a == k) = false := by simpa using Ne.symm h
      simp [List.find?, h, h']

end NatMap

end Fe.Sonatina.Steps
