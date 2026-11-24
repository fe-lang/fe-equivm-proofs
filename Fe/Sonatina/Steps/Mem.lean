import Fe.Sonatina.Interp
import Fe.Sonatina.CheckBlock

/-!
# The memory relation and the order on results

A step of the machine pipeline may leave memory with another size than its input does: an
`mcopy` from beyond the end of memory does not grow it, the stores it replaces do.  Programs
observe memory only through padded reads, so two memories are related when every padded read
of them agrees (`MemEq`).  Worlds are related when they agree on everything else and their
memories are (`WRel`); results of runs when they are equal up to that (`ResRel`); and a run
`x'` approximates `x` (`Approx R x' x`) when, from related worlds, `x'` diverges or ends as `x`
does.  `Approx Eq` is the order `⊑` of the design (`Steps/NOTES.md`).

Mem0: `ByteArray.write` respects `MemEq` in both its source and its destination
(`MemEq.write`), and every primitive the machine IR runs respects `WRel` (`Approx` of itself,
`Approx.runInst` in `Steps/Oracle.lean`).  `evm_malloc` and `alloca` read the size of memory and
do not: the machine IR has neither (`Inst.machine`).
-/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM Fe.Sonatina.Check

/-! ## Bytes -/

theorem getD_ge (a : ByteArray) {i : Nat} (h : a.size ≤ i) : a.data.getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

theorem getD_append (a b : ByteArray) (i : Nat) :
    (a ++ b).data.getD i 0 = if i < a.size then a.data.getD i 0 else b.data.getD (i - a.size) 0 := by
  have hs : a.size = a.data.size := rfl
  simp only [ByteArray.data_append, Array.getD_eq_getD_getElem?, Array.getElem?_append, hs]
  split <;> rfl

theorem getD_zeroes (n i : Nat) : (ByteArray.zeroes n).data.getD i 0 = 0 := by
  simp only [ByteArray.zeroes, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem size_zeroes (n : Nat) : (ByteArray.zeroes n).size = n := by
  simp only [ByteArray.zeroes, ByteArray.size, Array.size_replicate]

/-- A byte of a `copySlice`: the destination's below the offset (or its end), the source's
    copied after it, the destination's after those. -/
theorem getD_copySlice (src : ByteArray) (so : Nat) (dst : ByteArray) (dO len i : Nat) :
    (src.copySlice so dst dO len).data.getD i 0 =
      if i < min dO dst.size then dst.data.getD i 0
      else if i < min dO dst.size + (min (so + len) src.size - so) then
        src.data.getD (so + (i - min dO dst.size)) 0
      else dst.data.getD (i - min dO dst.size - (min (so + len) src.size - so)
        + (dO + min len (src.size - so))) 0 := by
  have hs : ∀ x : ByteArray, x.size = x.data.size := fun _ => rfl
  simp only [ByteArray.copySlice, Array.getD_eq_getD_getElem?, Array.getElem?_append,
    Array.size_append, Array.size_extract, Array.getElem?_extract, hs]
  split_ifs <;> first
    | omega
    | rfl
    | (congr 2; omega)
    | (rw [Array.getElem?_eq_none (by omega)]; rfl)
    | (rw [Array.getElem?_eq_none] <;> first | rfl | omega)
    | (rw [Array.getElem?_eq_none, Array.getElem?_eq_none] <;> first | rfl | omega)
    | skip

/-- A byte of a write: the source's, zero past its end, in the window written; the
    destination's elsewhere, zero past its end. -/
theorem write_getD (src : ByteArray) (sa : Nat) (dst : ByteArray) (da len i : Nat) :
    (src.write sa dst da len).data.getD i 0 =
      if da ≤ i ∧ i < da + len then src.data.getD (sa + (i - da)) 0 else dst.data.getD i 0 := by
  unfold ByteArray.write
  split
  · next h => subst h; simp
  split
  · next hs =>
    rw [getD_copySlice, size_zeroes]
    split_ifs <;> first
      | omega
      | rfl
      | (rw [getD_zeroes, getD_ge _ (by omega)])
      | (rw [getD_ge _ (by omega), getD_ge _ (by omega)])
      | (rw [getD_ge _ (by omega)]; congr 1; omega)
      | (congr 1; omega)
      | skip
  · next hs =>
    rw [getD_copySlice, ByteArray.size_append, ByteArray.size_append, size_zeroes, size_zeroes]
    split_ifs <;> (try rw [getD_append]) <;> (try rw [getD_append]) <;> (try rw [getD_append]) <;>
      (try simp only [getD_zeroes]) <;> split_ifs <;> first
      | omega
      | rfl
      | (rw [getD_ge _ (by omega)])
      | (rw [getD_ge _ (by omega), getD_ge _ (by omega)])
      | (congr 1; omega)
      | (rw [getD_ge _ (by omega)]; congr 1; omega)
      | skip

/-! ## The memory relation -/

/-- Two memories are equal under padded reads. -/
def MemEq (m' m : ByteArray) : Prop := ∀ a n, m'.readWithPadding a n = m.readWithPadding a n

theorem memEq_iff_getD {m' m : ByteArray} : MemEq m' m ↔ ∀ i, m'.data.getD i 0 = m.data.getD i 0 := by
  constructor
  · intro h i
    have e' := readWithPadding_getD m' i 1 0 (by omega)
    have e := readWithPadding_getD m i 1 0 (by omega)
    rw [Nat.add_zero] at e e'
    rw [← e', ← e, h i 1]
  · intro h a n
    exact readWithPadding_congr fun i _ => h (a + i)

theorem MemEq.refl (m : ByteArray) : MemEq m m := fun _ _ => rfl

theorem MemEq.symm {m' m : ByteArray} (h : MemEq m' m) : MemEq m m' := fun a n => (h a n).symm

theorem MemEq.trans {m'' m' m : ByteArray} (h₁ : MemEq m'' m') (h₂ : MemEq m' m) :
    MemEq m'' m := fun a n => (h₁ a n).trans (h₂ a n)

/-- Mem0: a write respects the relation in its source and its destination. -/
theorem MemEq.write {s' s d' d : ByteArray} (hs : MemEq s' s) (hd : MemEq d' d)
    (sa da len : Nat) : MemEq (s'.write sa d' da len) (s.write sa d da len) := by
  rw [memEq_iff_getD] at hs hd ⊢
  intro i
  rw [write_getD, write_getD, hs, hd]

/-! ## Worlds and results -/

/-- Two worlds are related: equal but for their memories, which are equal under padded
    reads. -/
structure WRel (w' w : World) : Prop where
  accounts : w'.accounts = w.accounts
  logs : w'.logs = w.logs
  memory : MemEq w'.memory w.memory
  returnData : w'.returnData = w.returnData
  feed : w'.feed = w.feed
  calls : w'.calls = w.calls

theorem WRel.refl (w : World) : WRel w w := ⟨rfl, rfl, MemEq.refl _, rfl, rfl, rfl⟩

theorem WRel.symm {w' w : World} (h : WRel w' w) : WRel w w' :=
  ⟨h.1.symm, h.2.symm, h.3.symm, h.4.symm, h.5.symm, h.6.symm⟩

theorem WRel.trans {w'' w' w : World} (h₁ : WRel w'' w') (h₂ : WRel w' w) : WRel w'' w :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3, h₁.4.trans h₂.4, h₁.5.trans h₂.5,
    h₁.6.trans h₂.6⟩

/-- A padded read of related worlds. -/
theorem WRel.read {w' w : World} (h : WRel w' w) (a n : Nat) :
    w'.memory.readWithPadding a n = w.memory.readWithPadding a n := h.memory a n

/-- How two runs that left their callers may end alike: with the same exit, a successful halt
    in related worlds. -/
def ExitRel : Exit World → Exit World → Prop
  | .stop d' w', .stop d w => d' = d ∧ WRel w' w
  | .stop _ _, _ | _, .stop _ _ => False
  | e', e => e' = e

theorem ExitRel.refl : ∀ e : Exit World, ExitRel e e
  | .stop _ w => ⟨rfl, WRel.refl w⟩
  | .revert _ | .panic _ | .static | .trap | .oob => rfl

theorem ExitRel.trans {e'' e' e : Exit World} (h₁ : ExitRel e'' e') (h₂ : ExitRel e' e) :
    ExitRel e'' e := by
  cases e'' <;> cases e' <;> cases e <;> simp only [ExitRel, reduceCtorEq, Exit.revert.injEq,
    Exit.panic.injEq] at h₁ h₂ ⊢
  all_goals first | exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩ | exact h₁.trans h₂

/-- The result `r'` of a run is related to `r` by `R` on returned values: `r'` diverges, or both
    exit alike, or both return related values in related worlds. -/
def ResRel {α : Type} (R : α → α → Prop) :
    Option (Except (Exit World) (α × World)) → Option (Except (Exit World) (α × World)) → Prop
  | none, _ => True
  | some (.ok (a', w')), some (.ok (a, w)) => R a' a ∧ WRel w' w
  | some (.error e'), some (.error e) => ExitRel e' e
  | some _, _ => False

theorem ResRel.trans {α : Type} {R : α → α → Prop} (hR : ∀ a b c, R a b → R b c → R a c) :
    ∀ {r'' r' r : Option (Except (Exit World) (α × World))},
    ResRel R r'' r' → ResRel R r' r → ResRel R r'' r
  | none, _, _, _, _ => trivial
  | some (.ok _), some (.ok _), some (.ok _), ⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩ => ⟨hR _ _ _ h₁ h₂, h₁'.trans h₂'⟩
  | some (.error _), some (.error _), some (.error _), h₁, h₂ => ExitRel.trans h₁ h₂
  | some (.ok _), none, _, h, _ | some (.error _), none, _, h, _ => h.elim
  | some (.ok _), some (.ok _), none, _, h | some (.error _), some (.error _), none, _, h => h.elim
  | some (.ok _), some (.error _), _, h, _ | some (.error _), some (.ok _), _, h, _ => h.elim
  | some (.ok _), some (.ok _), some (.error _), _, h
  | some (.error _), some (.error _), some (.ok _), _, h => h.elim

/-- `x'` approximates `x`: from related worlds, `x'` diverges, or ends as `x` does, with
    returned values related by `R`. -/
def Approx {α : Type} (R : α → α → Prop) (x' x : FeM α) : Prop :=
  ∀ I w' w, WRel w' w → ResRel R (x'.exec I w') (x.exec I w)

namespace Approx

variable {α β : Type}

theorem trans {R : α → α → Prop} (hR : ∀ a b c, R a b → R b c → R a c) {x'' x' x : FeM α}
    (h₁ : Approx R x'' x') (h₂ : Approx R x' x) : Approx R x'' x :=
  fun I w'' w hw => ResRel.trans hR (h₁ I w'' w hw) (h₂ I w w (WRel.refl w))

theorem trans_eq {x'' x' x : FeM α} (h₁ : Approx Eq x'' x') (h₂ : Approx Eq x' x) :
    Approx Eq x'' x := trans (fun _ _ _ h h' => h.trans h') h₁ h₂

theorem pure {R : α → α → Prop} {a' a : α} (h : R a' a) :
    Approx R (Pure.pure a' : FeM α) (Pure.pure a) := fun _ _ _ hw => by
  simp only [Fe.M.exec_pure, ResRel]; exact ⟨h, hw⟩

theorem pure_eq (a : α) : Approx Eq (Pure.pure a : FeM α) (Pure.pure a) := pure rfl

theorem diverge {R : α → α → Prop} (x : FeM α) : Approx R Fe.M.diverge x := fun _ _ _ _ => by
  simp only [Fe.M.exec_diverge, ResRel]

theorem stuck {R : α → α → Prop} (x : FeM α) : Approx R Fe.Sonatina.stuck x := diverge x

theorem bind {R : α → α → Prop} {S : β → β → Prop} {x' x : FeM α} {k' k : α → FeM β}
    (hx : Approx R x' x) (hk : ∀ a' a, R a' a → Approx S (k' a') (k a)) :
    Approx S (x' >>= k') (x >>= k) := by
  intro I w' w hw
  have h := hx I w' w hw
  simp only [Fe.M.exec_bind]
  rcases hx' : x'.exec I w' with _ | r'
  · simp only [ResRel]
  rcases hx0 : x.exec I w with _ | r
  · rw [hx', hx0] at h; cases r' <;> exact h.elim
  rw [hx', hx0] at h
  rcases r' with e' | ⟨a', w₁'⟩ <;> rcases r with e | ⟨a, w₁⟩
  · exact h
  · exact h.elim
  · exact h.elim
  · exact hk a' a h.1 I w₁' w₁ h.2

/-- A bind with the same first part. -/
theorem bind_eq {x : FeM α} {k' k : α → FeM β} {S : β → β → Prop} (hx : Approx Eq x x)
    (hk : ∀ a, Approx S (k' a) (k a)) : Approx S (x >>= k') (x >>= k) :=
  bind hx fun a' a h => h ▸ hk a'

theorem read_bind {S : β → β → Prop} {k' k : ExecutionEnv → FeM β}
    (hk : ∀ e, Approx S (k' e) (k e)) : Approx S (MonadReader.read >>= k') (MonadReader.read >>= k) := by
  intro I w' w hw
  simp only [Fe.M.exec_bind, Fe.M.exec_read]
  exact hk I I w' w hw

theorem read : Approx Eq (MonadReader.read : FeM ExecutionEnv) MonadReader.read := by
  intro I w' w hw; simp only [Fe.M.exec_read, ResRel, true_and]; exact hw

theorem get_bind {S : β → β → Prop} {k' k : World → FeM β}
    (hk : ∀ w' w, WRel w' w → Approx S (k' w') (k w)) :
    Approx S (MonadState.get >>= k') (MonadState.get >>= k) := by
  intro I w' w hw
  simp only [Fe.M.exec_bind, Fe.M.exec_get]
  exact hk w' w hw I w' w hw

theorem set {w₁' w₁ : World} (h : WRel w₁' w₁) :
    Approx Eq (MonadStateOf.set w₁' : FeM PUnit) (MonadStateOf.set w₁) := by
  intro I w' w _; simp only [Fe.M.exec_set, ResRel, true_and]; exact h

theorem modify {f : World → World} (h : ∀ w' w, WRel w' w → WRel (f w') (f w)) :
    Approx Eq (modify f : FeM PUnit) (modify f) := by
  intro I w' w hw; simp only [Fe.M.exec_modify, ResRel, true_and]; exact h w' w hw

theorem fail (e : Exit World) (he : ∀ d w, e ≠ .stop d w) :
    Approx Eq (Fe.M.fail e : FeM α) (Fe.M.fail e) := by
  intro I w' w _
  simp only [Fe.M.exec_fail, ResRel]
  cases e with
  | stop d w => exact (he d w rfl).elim
  | _ => rfl

theorem ite {R : α → α → Prop} {c : Prop} [Decidable c] {x' x y' y : FeM α}
    (hx : Approx R x' x) (hy : Approx R y' y) :
    Approx R (if c then x' else y') (if c then x else y) := by
  split <;> assumption

theorem mapM {γ : Type} {f : γ → FeM α} (hf : ∀ a, Approx Eq (f a) (f a)) :
    ∀ xs : List γ, Approx Eq (xs.mapM f) (xs.mapM f)
  | [] => by simpa using pure_eq ([] : List α)
  | a :: xs => by
    rw [List.mapM_cons]
    exact bind_eq (hf a) fun b => bind_eq (mapM hf xs) fun bs => pure_eq _

end Approx

end Fe.Sonatina.Steps

/-! ## Mem0 for the primitives

Each primitive the machine IR runs approximates itself: from worlds that differ in memory
alone, under padded reads, it ends alike.  The model library reads memory only by
`readWithPadding` and writes it only by `ByteArray.write`. -/

namespace Fe.Sonatina.Steps

open Ethereum Fe Fe.EVM

@[simp] theorem wrel_mk {a : AccountMap} {l : LogSeries} {m' m rd : ByteArray} {f : List Supply}
    {c : List Made} : WRel ⟨a, l, m', rd, f, c⟩ ⟨a, l, m, rd, f, c⟩ ↔ MemEq m' m :=
  ⟨fun h => h.memory, fun h => ⟨rfl, rfl, h, rfl, rfl, rfl⟩⟩

/-- Approximation decided on worlds that differ in their memories alone. -/
theorem Approx.of_world {α : Type} {R : α → α → Prop} {x' x : FeM α}
    (h : ∀ I (a : AccountMap) (l : LogSeries) (m' m rd : ByteArray) (f : List Supply)
      (c : List Made), MemEq m' m →
      (∀ p n, m'.readWithPadding p n = m.readWithPadding p n) →
      ResRel R (x'.exec I ⟨a, l, m', rd, f, c⟩) (x.exec I ⟨a, l, m, rd, f, c⟩)) :
    Approx R x' x := by
  intro I w' w hw
  rcases w' with ⟨a', l', m', rd', f', c'⟩
  rcases w with ⟨a, l, m, rd, f, c⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp only at h1 h2 h4 h5 h6
  subst h1 h2 h4 h5 h6
  exact h I a' l' m' m rd' f' c' h3 h3

theorem memEq_write {m' m : ByteArray} (h : MemEq m' m) (src : ByteArray) (sa da len : Nat) :
    MemEq (src.write sa m' da len) (src.write sa m da len) :=
  MemEq.write (MemEq.refl src) h sa da len

/-- Close the goals `Approx.of_world` leaves for a primitive. -/
macro "approx_prim" : tactic => `(tactic| (
  apply Approx.of_world
  intro I a l m' m rd f c hm hr
  simp_all [ResRel, ExitRel, Fe.M.exec_bind, Fe.M.exec_read, Fe.M.exec_get, Fe.M.exec_set,
    Fe.M.exec_pure, Fe.M.exec_modify, Fe.M.exec_fail, Fe.M.exec_stop, Fe.M.exec_ite]
  all_goals (try split_ifs) <;> simp_all [ResRel, ExitRel, memEq_write]))

theorem approx_selfAddress : Approx Eq selfAddress selfAddress := by
  unfold selfAddress; approx_prim
theorem approx_origin : Approx Eq origin origin := by unfold origin; approx_prim
theorem approx_caller : Approx Eq caller caller := by unfold caller; approx_prim
theorem approx_callvalue : Approx Eq callvalue callvalue := by unfold callvalue; approx_prim
theorem approx_gasprice : Approx Eq gasprice gasprice := by unfold gasprice; approx_prim
theorem approx_coinbase : Approx Eq coinbase coinbase := by unfold coinbase; approx_prim
theorem approx_timestamp : Approx Eq timestamp timestamp := by unfold timestamp; approx_prim
theorem approx_blockNumber : Approx Eq blockNumber blockNumber := by
  unfold blockNumber; approx_prim
theorem approx_prevrandao : Approx Eq prevrandao prevrandao := by unfold prevrandao; approx_prim
theorem approx_gaslimit : Approx Eq gaslimit gaslimit := by unfold gaslimit; approx_prim
theorem approx_chainid : Approx Eq chainid chainid := by unfold chainid; approx_prim
theorem approx_basefee : Approx Eq Fe.EVM.basefee Fe.EVM.basefee := by
  unfold Fe.EVM.basefee; approx_prim
theorem approx_blobbasefee : Approx Eq blobbasefee blobbasefee := by
  unfold blobbasefee; approx_prim
theorem approx_calldatasize : Approx Eq calldatasize calldatasize := by
  unfold calldatasize; approx_prim
theorem approx_codesize : Approx Eq codesize codesize := by unfold codesize; approx_prim
theorem approx_calldataload (o : UInt256) : Approx Eq (calldataload o) (calldataload o) := by
  unfold calldataload; approx_prim
theorem approx_cload (o : UInt256) : Approx Eq (cload o) (cload o) := by unfold cload; approx_prim
theorem approx_blockhash (n : UInt256) : Approx Eq (blockhash n) (blockhash n) := by
  unfold blockhash; approx_prim
theorem approx_blobhash (n : UInt256) : Approx Eq (Fe.EVM.blobhash n) (Fe.EVM.blobhash n) := by
  unfold Fe.EVM.blobhash; approx_prim
theorem approx_balance (x : UInt256) : Approx Eq (balance x) (balance x) := by
  unfold balance; approx_prim
theorem approx_selfbalance : Approx Eq selfbalance selfbalance := by
  unfold selfbalance; approx_prim
theorem approx_extcodesize (x : UInt256) : Approx Eq (extcodesize x) (extcodesize x) := by
  unfold extcodesize; approx_prim
theorem approx_extcodehash (x : UInt256) : Approx Eq (extcodehash x) (extcodehash x) := by
  unfold extcodehash; approx_prim
theorem approx_sload (k : UInt256) : Approx Eq (sload k) (sload k) := by unfold sload; approx_prim
theorem approx_tload (k : UInt256) : Approx Eq (tload k) (tload k) := by unfold tload; approx_prim
theorem approx_sstore (k v : UInt256) : Approx Eq (sstore k v) (sstore k v) := by
  unfold sstore; approx_prim
theorem approx_tstore (k v : UInt256) : Approx Eq (tstore k v) (tstore k v) := by
  unfold tstore; approx_prim
theorem approx_mload (p : UInt256) : Approx Eq (mload p) (mload p) := by unfold mload; approx_prim
theorem approx_mstore (p v : UInt256) : Approx Eq (mstore p v) (mstore p v) := by
  unfold mstore; approx_prim
theorem approx_mstore8 (p v : UInt256) : Approx Eq (mstore8 p v) (mstore8 p v) := by
  unfold mstore8; approx_prim
theorem approx_zeroMem (p n : UInt256) : Approx Eq (zeroMem p n) (zeroMem p n) := by
  unfold zeroMem; approx_prim
theorem approx_mcopy (d s n : UInt256) : Approx Eq (mcopy d s n) (mcopy d s n) := by
  unfold mcopy
  exact Approx.modify fun w' w hw => ⟨hw.1, hw.2, MemEq.write hw.3 hw.3 _ _ _, hw.4, hw.5, hw.6⟩
theorem approx_calldatacopy (d o n : UInt256) :
    Approx Eq (Fe.EVM.calldatacopy d o n) (Fe.EVM.calldatacopy d o n) := by
  unfold Fe.EVM.calldatacopy; approx_prim
theorem approx_codecopy (d o n : UInt256) : Approx Eq (codecopy d o n) (codecopy d o n) := by
  unfold codecopy; approx_prim
theorem approx_extcodecopy (x d o n : UInt256) :
    Approx Eq (extcodecopy x d o n) (extcodecopy x d o n) := by
  unfold extcodecopy; approx_prim
theorem approx_returndatasize : Approx Eq returndatasize returndatasize := by
  unfold returndatasize; approx_prim
theorem approx_returndatacopy (d o n : UInt256) :
    Approx Eq (returndatacopy d o n) (returndatacopy d o n) := by
  unfold returndatacopy; approx_prim
theorem approx_keccak256 (p n : UInt256) : Approx Eq (keccak256 p n) (keccak256 p n) := by
  unfold keccak256; approx_prim
theorem approx_emit (t : Array UInt256) (d : ByteArray) : Approx Eq (emit t d) (emit t d) := by
  unfold emit; approx_prim
theorem approx_logData (p n : UInt256) (t : Array UInt256) :
    Approx Eq (logData p n t) (logData p n t) := by
  unfold logData
  exact Approx.get_bind fun w' w hw => by rw [hw.read]; exact approx_emit _ _
theorem approx_next : Approx Eq next next := by
  unfold next
  refine Approx.get_bind fun w' w hw => ?_
  rw [hw.feed]
  cases w.feed with
  | nil => exact Approx.diverge _
  | cons s rest =>
    exact Approx.bind (Approx.set ⟨hw.1, hw.2, hw.3, hw.4, rfl, hw.6⟩) fun _ _ _ =>
      Approx.pure_eq _
theorem approx_gas : Approx Eq gas gas := by
  unfold gas; exact Approx.bind_eq approx_next fun _ => Approx.pure_eq _
theorem approx_message (g : UInt256) (s r t : AccountAddress) (v v' ap al rp rl : UInt256)
    (perm : Bool) : Approx Eq (message g s r t v v' ap al rp rl perm)
      (message g s r t v v' ap al rp rl perm) := by
  unfold message
  refine Approx.read_bind fun I => Approx.bind_eq approx_next fun sp =>
    Approx.get_bind fun w' w hw => ?_
  have hT : messageCall I w' sp g s r t v v' ap al perm = messageCall I w sp g s r t v v' ap al perm := by
    simp only [messageCall, hw.accounts, hw.read]
  simp only [hT, hw.accounts, hw.logs, hw.calls, hw.feed]
  split <;> exact Approx.bind (Approx.set ⟨rfl, rfl, memEq_write hw.3 _ _ _ _, rfl, rfl, rfl⟩) fun _ _ _ =>
    Approx.pure_eq _
theorem approx_call (g a v ap al rp rl : UInt256) :
    Approx Eq (call g a v ap al rp rl) (call g a v ap al rp rl) := by
  unfold call
  exact Approx.read_bind fun _ =>
    Approx.ite (Approx.fail _ (by simp)) (approx_message _ _ _ _ _ _ _ _ _ _ _)
theorem approx_staticcall (g a ap al rp rl : UInt256) :
    Approx Eq (staticcall g a ap al rp rl) (staticcall g a ap al rp rl) := by
  unfold staticcall
  exact Approx.read_bind fun _ => approx_message _ _ _ _ _ _ _ _ _ _ _
theorem approx_delegatecall (g a ap al rp rl : UInt256) :
    Approx Eq (delegatecall g a ap al rp rl) (delegatecall g a ap al rp rl) := by
  unfold delegatecall
  exact Approx.read_bind fun _ => approx_message _ _ _ _ _ _ _ _ _ _ _
theorem approx_callcode (g a v ap al rp rl : UInt256) :
    Approx Eq (callcode g a v ap al rp rl) (callcode g a v ap al rp rl) := by
  unfold callcode
  exact Approx.read_bind fun _ => approx_message _ _ _ _ _ _ _ _ _ _ _
theorem approx_createWith (salt : Option ByteArray) (v p n : UInt256) :
    Approx Eq (createWith salt v p n) (createWith salt v p n) := by
  unfold createWith
  refine Approx.read_bind fun I => Approx.ite (Approx.fail _ (by simp))
    (Approx.ite (Approx.diverge _) (Approx.bind_eq approx_next fun sp =>
      Approx.get_bind fun w' w hw => ?_))
  simp only [hw.accounts, hw.read, hw.logs, hw.calls, hw.feed]
  repeat' split
  all_goals exact Approx.bind (Approx.set ⟨rfl, rfl, hw.3, rfl, rfl, rfl⟩) fun _ _ _ =>
    Approx.pure_eq _
theorem approx_create (v p n : UInt256) : Approx Eq (create v p n) (create v p n) :=
  approx_createWith _ _ _ _
theorem approx_create2 (v p n salt : UInt256) : Approx Eq (create2 v p n salt) (create2 v p n salt) :=
  approx_createWith _ _ _ _
theorem approx_returnData (p n : UInt256) : Approx Eq (returnData p n) (returnData p n) := by
  unfold returnData Fe.M.stop; approx_prim
theorem approx_revertData (p n : UInt256) : Approx Eq (revertData p n) (revertData p n) := by
  unfold revertData Fe.M.revert; approx_prim
theorem approx_stopCall : Approx Eq stopCall stopCall := by unfold stopCall Fe.M.stop; approx_prim
theorem approx_trap : Approx Eq (trap : FeM Empty) trap := by unfold trap; approx_prim
theorem approx_selfdestruct (a : UInt256) :
    Approx Eq (Fe.EVM.selfdestruct a) (Fe.EVM.selfdestruct a) := by
  unfold Fe.EVM.selfdestruct
  refine Approx.read_bind fun I => Approx.ite (Approx.fail _ (by simp))
    (Approx.bind_eq approx_next fun sp => Approx.get_bind fun w' w hw => ?_)
  simp only [hw.accounts]
  exact Approx.bind (Approx.set ⟨rfl, rfl, hw.3, rfl, rfl, rfl⟩) fun _ _ _ => by
    unfold Fe.M.stop; approx_prim

end Fe.Sonatina.Steps
