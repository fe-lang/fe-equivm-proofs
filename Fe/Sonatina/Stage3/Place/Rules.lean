import Fe.Sonatina.Stage3.Place.Word

/-!
# What the rules of S give, statement by statement

The checker's rules are booleans over whole functions; the simulation uses them one statement at
a time.  This file turns each into the fact about a statement it gives.

- Rule S8 (`notObserved`): an operand of a statement that is derived is at a position where
  the statement does not observe its word (`notObserved_stmt`); in particular no derived value
  is stored (`notObserved_mstore`, `notObserved_evm_mstore`), so in address-0 mode memory holds
  no fragment, and every value that is not derived is an integer.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H

theorem mem_zipIdx_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    (a, i) ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]; exact h

/-- Rule S8 for one statement: a derived operand is at a position where the statement does not
    observe its word. -/
theorem notObserved_stmt {D : Derived} {k : Nat} {f : HFunc} (h : notObserved D k f = true)
    {b : HBlock} (hb : b ∈ f.blocks) {s : HStmt} (hs : s ∈ b.body) {i : Nat} {a : Operand}
    (ha : s.inst.args[i]? = some a) (hd : D.op k a = true) : i ∈ nonObserving D k s := by
  unfold notObserved at h
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  have := (h b hb).1 s hs (a, i) (mem_zipIdx_of_getElem? ha)
  simp only [Bool.or_eq_true, Bool.not_eq_true', hd, Bool.true_eq_false, false_or,
    List.contains_iff_mem] at this
  exact this

/-- In a function S8 accepts, no derived value is the value a typed store writes. -/
theorem notObserved_mstore {D : Derived} {k : Nat} {f : HFunc} (h : notObserved D k f = true)
    {b : HBlock} (hb : b ∈ f.blocks) {s : HStmt} (hs : s ∈ b.body) {a v : Operand} {t : Ty}
    (hi : s.inst = .base (.mstore a v t)) : D.op k v = false := by
  cases hd : D.op k v
  · rfl
  · have := notObserved_stmt h hb hs (i := 1) (a := v) (by simp [hi, HInst.args, HInst.skel, Inst.args]) hd
    simp [nonObserving, hi] at this

/-- In a function S8 accepts, no derived value is the value `evm_mstore` or `evm_mstore8`
    writes. -/
theorem notObserved_evm_mstore {D : Derived} {k : Nat} {f : HFunc} (h : notObserved D k f = true)
    {b : HBlock} (hb : b ∈ f.blocks) {s : HStmt} (hs : s ∈ b.body) {op : EvmOp} {a v : Operand}
    (hop : op = .mstore ∨ op = .mstore8)
    (hi : s.inst = .base (.evm op [a, v])) : D.op k v = false := by
  cases hd : D.op k v
  · rfl
  · have := notObserved_stmt h hb hs (i := 1) (a := v) (by simp [hi, HInst.args, HInst.skel, Inst.args]) hd
    rcases hop with rfl | rfl <;> simp [nonObserving, hi, EvmOp.addrPos] at this <;>
      split at this <;> simp at this

end Fe.Sonatina.Stage3.Place
