import Fe.Sonatina.Steps.Dom
import Fe.Sonatina.Steps.Prim
import Fe.Sonatina.Steps.Eq
import Fe.Sonatina.Steps.Record

/-!
# Well-formed machine IR and strict SSA (design §4.1, review C-6, H-1, M-1)

`Func.wf sig syms f`: the structural rules every snapshot of the machine stage keeps.  Blocks,
the entry first, with distinct ids; the entry has no phis and no slot targets it; every target
is a block; each phi has one operand from each predecessor and none from elsewhere.  Every type
is `i256`, every immediate an `i256` below `2 ^ 256`; every `sym_addr`/`sym_size` names a
symbol of `syms`, and every `get_function_ptr %f` the symbol `%f`; every `call` names a function
of the module (`sig`) with as many parameters as arguments and as many results as the statement
binds; every `return` returns as many values as the function's results; every `br_table` has a
default and distinct immediate keys; no `evm_malloc`, `alloca`, `insert_value`, `extract_value`
or `evm_msize`.  `FuncSnap.wf` adds the instruction ids: one per line, distinct in the function.

`VFunc` is a snapshot with its maps: blocks by id, each block's instruction ids, the block and
line of each instruction id, the definition of each value (`Def`).

`ssa f T` (strict SSA on the reachable set of a dominator tree `T` that `DomTree.valid`
accepts): every value is defined once, over the parameters, phis and statement results; a use
before statement `k` of a reachable block `b` (its terminator for `k` the statement count) is a
parameter, a phi of `b`, a result of a statement of `b` before `k`, or defined in a strict tree
ancestor of `b` (`DomAt`, `useOk_sound`); a phi's operand from a reachable predecessor `p` is a
parameter or defined in an ancestor-or-self of `p` (`phiUseOk_sound`).  Uses in unreachable
blocks, and phi operands from unreachable predecessors, are not checked: they never run.
-/

namespace Fe.Sonatina.Steps

/-! ## Distinct naturals -/

def distinctAux : NatMap Unit → List Nat → Bool
  | _, [] => true
  | seen, x :: xs => (seen.find? x).isNone && distinctAux (seen.insert x ()) xs

/-- The list has no element twice. -/
def distinct (l : List Nat) : Bool := distinctAux .empty l

theorem distinctAux_sound : ∀ (seen : NatMap Unit) (l : List Nat), distinctAux seen l = true →
    l.Nodup ∧ ∀ x ∈ l, seen.find? x = none
  | _, [], _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | seen, x :: xs, h => by
    simp only [distinctAux, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hx, hxs⟩ := distinctAux_sound _ xs h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hx⟩, fun y hy => ?_⟩
    · have := hxs x hm; simp at this
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h.1
      · have := hxs y hy
        rw [NatMap.find?_insert] at this
        split at this
        · cases this
        · exact this

theorem distinct_nodup {l : List Nat} (h : distinct l = true) : l.Nodup :=
  (distinctAux_sound _ _ h).1

/-! ## Well-formed functions -/

/-- `i256`, the machine IR's one type. -/
def _root_.Fe.Sonatina.Ty.word (t : Ty) : Bool := decide (t = .int 256)

/-- An operand of the machine IR: a value, or an `i256` immediate below `2 ^ 256`. -/
def _root_.Fe.Sonatina.Operand.wf : Operand → Bool
  | .var _ => true
  | .imm bits v => bits == 256 && decide (v < 2 ^ 256)

/-- An immediate's value. -/
def _root_.Fe.Sonatina.Operand.immVal? : Operand → Option Nat
  | .imm _ v => some v
  | _ => none

/-- The parameter and result counts of each function of a module. -/
abbrev Sigs := String → Option (Nat × Nat)

def _root_.Fe.Sonatina.Module.sig (M : Module) : Sigs :=
  fun n => (M.func? n).map fun g => (g.params.length, g.rets.length)

/-- An instruction that binds `n` values: of the machine IR, its operands well formed, its
    symbol one of `syms`, its callee a function of `sig` with as many parameters as arguments
    and `n` results, its memory type `i256`; not `evm_msize`, which the semantics leaves
    stuck. -/
def _root_.Fe.Sonatina.Inst.wf (sig : Sigs) (syms : List String) (n : Nat) (i : Inst) : Bool :=
  i.machine && i.args.all Operand.wf && match i with
    | .symAddr s | .symSize s => syms.contains s
    | .funcPtr f => syms.contains s!"%{f}"
    | .evm .msize _ => false
    | .call callee args => sig callee == some (args.length, n)
    | .mload _ ty | .mstore _ _ ty => ty.word
    | _ => true

/-- A terminator of a function with `n` results: its operands well formed; a `return` of `n`
    values; a `br_table` with a default and distinct immediate keys (review C-6). -/
def _root_.Fe.Sonatina.Term.wf (n : Nat) (t : Term) : Bool :=
  t.args.all Operand.wf && match t with
    | .ret vs => vs.length == n
    | .brTable _ d cases => d.isSome && cases.all (·.1.immVal?.isSome) &&
        distinct (cases.filterMap (·.1.immVal?))
    | _ => true

/-- The predecessors of each block. -/
def predMap (f : Func) : NatMap (List Nat) :=
  f.blocks.foldl (fun m b => b.term.succs.foldl (fun m s => m.insert s (b.id :: (m.find? s).getD [])) m)
    .empty

/-- The control flow of `f`: an entry, with no phis; distinct block ids; every target a block,
    and none the entry; each phi with one operand from each predecessor, and none from
    elsewhere. -/
def _root_.Fe.Sonatina.Func.cfgOk (f : Func) : Bool :=
  match f.blocks.head? with
  | none => false
  | some e =>
    let B := NatMap.ofListBy (·.id) f.blocks
    let P := predMap f
    e.phis.isEmpty && distinct (f.blocks.map (·.id)) && f.blocks.all fun b =>
      b.term.succs.all (fun t => t != e.id && (B.find? t).isSome) &&
      b.phis.all fun phi =>
        let ins := phi.incoming.map (·.2)
        let ps := (P.find? b.id).getD []
        distinct ins && ins.all ps.contains && ps.all ins.contains

/-- Every type of `f` is `i256`: parameters, results, phis, statement results. -/
def _root_.Fe.Sonatina.Func.wordTyped (f : Func) : Bool :=
  f.params.all (·.2.word) && f.rets.all Ty.word && f.blocks.all fun b =>
    b.phis.all (·.ty.word) && b.body.all fun s => s.dsts.all (·.2.word)

/-- A well-formed function of the machine IR, in a module of signatures `sig` and a section of
    symbols `syms`. -/
def _root_.Fe.Sonatina.Func.wf (sig : Sigs) (syms : List String) (f : Func) : Bool :=
  f.machine && f.wordTyped && f.cfgOk && f.blocks.all fun b =>
    b.phis.all (·.incoming.all (·.1.wf)) && b.body.all (fun s => s.inst.wf sig syms s.dsts.length) &&
      b.term.wf f.rets.length

/-- Every function of the module is well formed in it. -/
def _root_.Fe.Sonatina.Module.wf (syms : List String) (M : Module) : Bool :=
  M.funcs.all (Func.wf M.sig syms)

/-- The instruction ids of a snapshot: one per line of each block (its phis, statements and
    terminator), all distinct. -/
def FuncSnap.idsOk (s : FuncSnap) : Bool :=
  s.insts.length == s.func.blocks.length &&
    (s.insts.zip s.func.blocks).all (fun ib => ib.1.length == ib.2.phis.length + ib.2.body.length + 1) &&
    distinct s.insts.flatten

def FuncSnap.wf (sig : Sigs) (syms : List String) (s : FuncSnap) : Bool :=
  s.func.wf sig syms && s.idsOk

theorem _root_.Fe.Sonatina.Func.wf_machine {sig : Sigs} {syms : List String} {f : Func}
    (h : f.wf sig syms = true) : f.machine = true := by
  unfold Func.wf at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem _root_.Fe.Sonatina.Func.wf_words {sig : Sigs} {syms : List String} {f : Func}
    (h : f.wf sig syms = true) :
    (∀ p ∈ f.params, p.2 = .int 256) ∧ ∀ b ∈ f.blocks, (∀ phi ∈ b.phis, phi.ty = .int 256) ∧
      ∀ s ∈ b.body, ∀ d ∈ s.dsts, d.2 = .int 256 := by
  unfold Func.wf Func.wordTyped at h
  simp only [Bool.and_eq_true, List.all_eq_true, Ty.word, decide_eq_true_eq] at h
  exact ⟨h.1.1.2.1.1, fun b hb => ⟨(h.1.1.2.2 b hb).1, (h.1.1.2.2 b hb).2⟩⟩

theorem _root_.Fe.Sonatina.Func.wf_ids {sig : Sigs} {syms : List String} {f : Func}
    (h : f.wf sig syms = true) : (f.blocks.map (·.id)).Nodup := by
  unfold Func.wf at h
  simp only [Bool.and_eq_true] at h
  have hc := h.1.2
  unfold Func.cfgOk at hc
  split at hc
  · cases hc
  · simp only [Bool.and_eq_true] at hc
    exact distinct_nodup hc.1.2

theorem _root_.Fe.Sonatina.Func.wf_operands {sig : Sigs} {syms : List String} {f : Func}
    (h : f.wf sig syms = true) {b : Block} (hb : b ∈ f.blocks) :
    (∀ phi ∈ b.phis, ∀ p ∈ phi.incoming, p.1.wf = true) ∧
      (∀ s ∈ b.body, ∀ o ∈ s.inst.args, o.wf = true) ∧ ∀ o ∈ b.term.args, o.wf = true := by
  unfold Func.wf at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hph, hbody⟩, hterm⟩ := h.2 b hb
  refine ⟨hph, fun s hs => ?_, ?_⟩
  · have := hbody s hs
    unfold Inst.wf at this
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this.1.2
  · unfold Term.wf at hterm
    simp only [Bool.and_eq_true, List.all_eq_true] at hterm
    exact hterm.1

theorem _root_.Fe.Sonatina.Module.wf_machine {syms : List String} {M : Module}
    (h : M.wf syms = true) : M.machine = true :=
  List.all_eq_true.mpr fun f hf => Func.wf_machine (List.all_eq_true.mp h f hf)

theorem _root_.Fe.Sonatina.Module.wf_func {syms : List String} {M : Module} (h : M.wf syms = true)
    {name : String} {f : Func} (hf : M.func? name = some f) : f.wf M.sig syms = true :=
  List.all_eq_true.mp h f (List.mem_of_find?_eq_some hf)

/-! ## Functions with their maps -/

/-- Where a value is defined: a parameter, a phi of a block, a result of a block's statement
    (its index). -/
inductive Def where
  | param
  | phi (block : Nat)
  | stmt (block index : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The definitions of `f`, in order: its parameters, then each block's phis and statement
    results. -/
def defList (f : Func) : List (Nat × Def) :=
  f.params.map (fun p => (p.1, .param)) ++ f.blocks.flatMap fun b =>
    b.phis.map (fun phi => (phi.dst, .phi b.id)) ++
      b.body.zipIdx.flatMap fun sk => sk.1.dsts.map fun d => (d.1, .stmt b.id sk.2)

def defsOf (f : Func) : NatMap Def := .ofList (defList f)

/-- A line of a block: a phi, a statement, the terminator. -/
inductive Line where
  | phi (p : Phi)
  | stmt (s : Stmt)
  | term (t : Term)
  deriving Repr

/-- A function with its maps (design §4.1): blocks by id, each block's instruction ids (its
    phis, statements and terminator), the block and line of each instruction id, the
    definition of each value. -/
structure VFunc where
  func : Func
  blocks : NatMap Block
  ids : NatMap (List Nat)
  lines : NatMap (Nat × Nat)
  defs : NatMap Def

def VFunc.of (s : FuncSnap) : VFunc where
  func := s.func
  blocks := .ofListBy (·.id) s.func.blocks
  ids := .ofList ((s.func.blocks.zip s.insts).map fun bi => (bi.1.id, bi.2))
  lines := .ofList ((s.func.blocks.zip s.insts).flatMap fun bi =>
    bi.2.zipIdx.map fun ik => (ik.1, (bi.1.id, ik.2)))
  defs := defsOf s.func

/-- The line at index `k` of a block: its phis first, then its statements, then its
    terminator. -/
def _root_.Fe.Sonatina.Block.line? (b : Block) (k : Nat) : Option Line :=
  match b.phis[k]? with
  | some p => some (.phi p)
  | none => match b.body[k - b.phis.length]? with
    | some s => some (.stmt s)
    | none => if k = b.phis.length + b.body.length then some (.term b.term) else none

/-- The instruction of id `i`: its block and its line. -/
def VFunc.inst? (V : VFunc) (i : Nat) : Option (Nat × Line) :=
  (V.lines.find? i).bind fun bk => (V.blocks.find? bk.1).bind fun blk =>
    (blk.line? bk.2).map (bk.1, ·)

/-! ## Strict SSA -/

/-- A use of the operand before statement `k` of block `b` (its terminator for `k` the
    statement count): a parameter, a phi of `b`, a result of a statement of `b` before `k`, or
    defined in a strict ancestor of `b`. -/
def useOk (D : NatMap Def) (T : DomTree) (b k : Nat) : Operand → Bool
  | .var v => match D.find? v with
    | some .param => true
    | some (.phi d) => d == b || (d != b && T.anc d b)
    | some (.stmt d j) => (d == b && decide (j < k)) || (d != b && T.anc d b)
    | none => false
  | _ => true

/-- A use of the operand by a phi, from predecessor `p`: a parameter, or defined in an
    ancestor-or-self of `p`. -/
def phiUseOk (D : NatMap Def) (T : DomTree) (p : Nat) : Operand → Bool
  | .var v => match D.find? v with
    | some .param => true
    | some (.phi d) => T.anc d p
    | some (.stmt d _) => T.anc d p
    | none => false
  | _ => true

/-- Strict SSA on the blocks `T` claims reachable. -/
def ssa (f : Func) (T : DomTree) : Bool :=
  let D := defsOf f
  distinct ((defList f).map (·.1)) && f.blocks.all fun b => (T.reach.find? b.id).isNone ||
    (b.phis.all fun phi => phi.incoming.all fun op =>
      (T.reach.find? op.2).isNone || phiUseOk D T op.2 op.1) &&
    (b.body.zipIdx.all fun sk => sk.1.inst.args.all (useOk D T b.id sk.2)) &&
    b.term.args.all (useOk D T b.id b.body.length)

/-! ## What the checks give -/

/-- `v` is a phi or a statement result of block `d`, the block `Func.block?` finds. -/
def DefinedIn (f : Func) (d v : Nat) : Prop :=
  ∃ blk, f.block? d = some blk ∧
    (v ∈ blk.phis.map (·.dst) ∨ ∃ s ∈ blk.body, v ∈ s.dsts.map (·.1))

/-- `v`'s definition dominates the point before statement `k` of block `b` (its terminator for
    `k` the statement count): a parameter, a phi of `b`, a result of a statement of `b` before
    `k`, or a definition in a strict tree ancestor of `b`. -/
def DomAt (f : Func) (T : DomTree) (b k v : Nat) : Prop :=
  v ∈ f.params.map (·.1) ∨
  (∃ blk, f.block? b = some blk ∧ (v ∈ blk.phis.map (·.dst) ∨
    ∃ j < k, ∃ s, blk.body[j]? = some s ∧ v ∈ s.dsts.map (·.1))) ∨
  ∃ d, d ≠ b ∧ T.Anc d b ∧ DefinedIn f d v

theorem find_id_of_mem : ∀ {l : List Block}, (l.map (·.id)).Nodup → ∀ {b : Block}, b ∈ l →
    l.find? (·.id == b.id) = some b
  | [], _, _, hb => nomatch hb
  | a :: l, hn, b, hb => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.find?_cons]
    by_cases ha : a.id = b.id
    · have hab : a = b := by
        rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact absurd (by rw [ha]; exact List.mem_map_of_mem hb) hn.1
      subst hab; simp
    · have hb' : b ∈ l := by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd rfl ha
        · exact hb
      simp only [show (a.id == b.id) = false by simpa using ha]
      exact find_id_of_mem hn.2 hb'

/-- With distinct ids, `Func.block?` finds each block by its id. -/
theorem block?_of_mem {f : Func} (hn : (f.blocks.map (·.id)).Nodup) {b : Block}
    (hb : b ∈ f.blocks) : f.block? b.id = some b := find_id_of_mem hn hb

theorem mem_of_lookup {α : Type} : ∀ {l : List (Nat × α)} {k : Nat} {a : α},
    l.lookup k = some a → (k, a) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k', a') :: l, k, a, h => by
    simp only [List.lookup] at h
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at he
      subst he
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem mem_defList {f : Func} {v : Nat} {d : Def} (h : (v, d) ∈ defList f) :
    (d = .param ∧ v ∈ f.params.map (·.1)) ∨
    (∃ b ∈ f.blocks, ∃ phi ∈ b.phis, d = .phi b.id ∧ v = phi.dst) ∨
    (∃ b ∈ f.blocks, ∃ k s, b.body[k]? = some s ∧ d = .stmt b.id k ∧ v ∈ s.dsts.map (·.1)) := by
  simp only [defList, List.mem_append, List.mem_map, List.mem_flatMap, Prod.mk.injEq] at h
  rcases h with ⟨p, hp, rfl, rfl⟩ | ⟨b, hb, ⟨phi, hphi, rfl, rfl⟩ | ⟨sk, hsk, dd, hdd, rfl, rfl⟩⟩
  · exact Or.inl ⟨rfl, List.mem_map_of_mem hp⟩
  · exact Or.inr (Or.inl ⟨b, hb, phi, hphi, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨b, hb, sk.2, sk.1, List.mem_zipIdx_iff_getElem?.mp hsk, rfl,
      List.mem_map_of_mem hdd⟩)

theorem defsOf_mem {f : Func} {v : Nat} {d : Def} (h : (defsOf f).find? v = some d) :
    (v, d) ∈ defList f := by
  rw [defsOf, NatMap.find?_ofList] at h
  exact mem_of_lookup h

/-- A use `useOk` accepts is dominated by its definition. -/
theorem useOk_sound {f : Func} (hn : (f.blocks.map (·.id)).Nodup) {T : DomTree} {b k v : Nat}
    (h : useOk (defsOf f) T b k (.var v) = true) : DomAt f T b k v := by
  rcases hD : (defsOf f).find? v with _ | d <;> simp only [useOk, hD, Bool.false_eq_true] at h
  rcases mem_defList (defsOf_mem hD) with ⟨rfl, hp⟩ | ⟨bb, hbb, phi, hphi, rfl, rfl⟩ |
    ⟨bb, hbb, j, s, hs, rfl, hv⟩
  · exact Or.inl hp
  · have hblk := block?_of_mem hn hbb
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨hne, ha⟩
    · subst h
      exact Or.inr (Or.inl ⟨bb, hblk, Or.inl (List.mem_map_of_mem hphi)⟩)
    · exact Or.inr (Or.inr ⟨bb.id, hne, DomTree.anc_sound ha,
        ⟨bb, hblk, Or.inl (List.mem_map_of_mem hphi)⟩⟩)
  · have hblk := block?_of_mem hn hbb
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    rcases h with ⟨h, hj⟩ | ⟨hne, ha⟩
    · subst h
      exact Or.inr (Or.inl ⟨bb, hblk, Or.inr ⟨j, hj, s, hs, hv⟩⟩)
    · exact Or.inr (Or.inr ⟨bb.id, hne, DomTree.anc_sound ha,
        ⟨bb, hblk, Or.inr ⟨s, List.mem_of_getElem? hs, hv⟩⟩⟩)

/-- A phi's use `phiUseOk` accepts, from `p`, is a parameter or defined in an ancestor-or-self
    of `p`. -/
theorem phiUseOk_sound {f : Func} (hn : (f.blocks.map (·.id)).Nodup) {T : DomTree} {p v : Nat}
    (h : phiUseOk (defsOf f) T p (.var v) = true) :
    v ∈ f.params.map (·.1) ∨ ∃ d, T.Anc d p ∧ DefinedIn f d v := by
  rcases hD : (defsOf f).find? v with _ | d <;> simp only [phiUseOk, hD, Bool.false_eq_true] at h
  rcases mem_defList (defsOf_mem hD) with ⟨rfl, hp⟩ | ⟨bb, hbb, phi, hphi, rfl, rfl⟩ |
    ⟨bb, hbb, j, s, hs, rfl, hv⟩
  · exact Or.inl hp
  · exact Or.inr ⟨bb.id, DomTree.anc_sound h,
      ⟨bb, block?_of_mem hn hbb, Or.inl (List.mem_map_of_mem hphi)⟩⟩
  · exact Or.inr ⟨bb.id, DomTree.anc_sound h,
      ⟨bb, block?_of_mem hn hbb, Or.inr ⟨s, List.mem_of_getElem? hs, hv⟩⟩⟩

/-- What `ssa` checks of a reachable block of `f`. -/
theorem ssa_block {f : Func} {T : DomTree} (hs : ssa f T = true) {b : Block} (hb : b ∈ f.blocks)
    (hr : (T.reach.find? b.id).isSome = true) :
    (∀ phi ∈ b.phis, ∀ op ∈ phi.incoming, (T.reach.find? op.2).isSome = true →
      phiUseOk (defsOf f) T op.2 op.1 = true) ∧
    (∀ k s, b.body[k]? = some s → ∀ o ∈ s.inst.args, useOk (defsOf f) T b.id k o = true) ∧
    ∀ o ∈ b.term.args, useOk (defsOf f) T b.id b.body.length o = true := by
  unfold ssa at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hs
  rcases hs.2 b hb with h | ⟨⟨hph, hbody⟩, hterm⟩
  · simp only [Option.isNone_iff_eq_none] at h; rw [h] at hr; cases hr
  refine ⟨fun phi hphi op hop hr' => ?_, fun k s hks o ho => ?_, hterm⟩
  · rcases hph phi hphi op hop with h | h
    · simp only [Option.isNone_iff_eq_none] at h; rw [h] at hr'; cases hr'
    · exact h
  · exact hbody (s, k) (List.mem_zipIdx_iff_getElem?.mpr hks) o ho

end Fe.Sonatina.Steps
