import FeProofs.Deposit.DepositEvent
import FeProofs.Deposit.Le64
import FeProofs.Deposit.RootFacts
import Reasoning.ExternalCall

/-!
# FeDeposit `deposit()` — the event segment, coupled (statements 17..21)

Statements 17..21 of `deposit` against the EVM trace of `DepositEvent.lean` (pc 1026 → 1592):
`require(node == uint256(deposit_data_root))`, `amount_bytes = le64(amount)`,
`index_bytes = le64(uint64(deposit_count))`, `emit DepositEvent(…)`, and
`require(deposit_count < 4294967295)`.  None of them changes the EVM state; the emitted log is
not part of the refinement (only its static-mode halt is).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

local notation "code" => feDepositBytecode

abbrev uint256StorageTy : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
abbrev uint64StorageTy : StorageType := .elem (.int (.uint ⟨64, by decide⟩))

def eventS17 : Stmt :=
  .require (.binary .eq (.var "node") (.cast (.var "deposit_data_root") uint256StorageTy))
def eventS18 : Stmt := .internalCall "le64" [.var "amount"] "amount_bytes"
def eventS19 : Stmt :=
  .internalCall "le64" [.cast (.storage { base := "deposit_count" }) uint64StorageTy] "index_bytes"
def eventS20 : Stmt :=
  .emit "DepositEvent" [.var "pubkey", .var "withdrawal_credentials", .var "amount_bytes",
    .var "signature", .var "index_bytes"]
def eventS21 : Stmt :=
  .require (.binary .lt (.storage { base := "deposit_count" }) (.intLit 4294967295))

theorem depositBody_drop17 : depositTransition.body.drop 17 =
    eventS17 :: eventS18 :: eventS19 :: eventS20 :: eventS21 :: depositTransition.body.drop 22 :=
  rfl

/-- The Stele locals the event segment needs at its entry. -/
structure EventLocals (L : Store) (node m : UInt256) (pk wc sig : Value) : Prop where
  node : L.get? "node" = some (.int (Int.ofNat node.toNat))
  amount : L.get? "amount" = some (.int (Int.ofNat m.toNat))
  pubkey : L.get? "pubkey" = some pk
  wc : L.get? "withdrawal_credentials" = some wc
  sig : L.get? "signature" = some sig
  count : L.get? "deposit_count" = none
  branch : L.get? "branch" = none

abbrev eventAmountStore (L : Store) (m : UInt256) : Store :=
  L.insert "amount_bytes" (.bytes ⟨(le64Bytes m).toArray⟩)

abbrev eventExitStore (L : Store) (m c : UInt256) : Store :=
  (eventAmountStore L m).insert "index_bytes" (.bytes ⟨(le64Bytes (mask64 c)).toArray⟩)

/-! ## The five statements -/

section Stmts

variable {L : Store} {evm : EVM.State}

theorem eventS17_eval {n r : UInt256}
    (hn : L.get? "node" = some (.int (Int.ofNat n.toNat)))
    (hr : evalExpr? config { contract := contract, locals := L } evm
      (.cast (.var "deposit_data_root") uint256StorageTy) = .ok (.int (Int.ofNat r.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .eq (.var "node") (.cast (.var "deposit_data_root") uint256StorageTy)) =
      .ok (.bool (decide (n = r))) := by
  refine evalBin (by decide) (by decide) (evalVar hn) hr ?_
  simp only [evalBinaryOp?]
  congr 2
  by_cases h : n = r
  · subst h; simp
  · have hne : ¬ n.toNat = r.toNat := fun he => h (u256_inj he)
    simp [h, hne]

theorem le64Call {e : Expr} {m : UInt256} {ret : Ident}
    (he : evalExpr? config { contract := contract, locals := L } evm e = .ok (.int (Int.ofNat m.toNat))) :
    ExecStmt config { contract := contract, locals := L } evm (.internalCall "le64" [e] ret)
      (.ok { contract := contract, locals := L.insert ret (.bytes ⟨(le64Bytes m).toArray⟩) } evm) := by
  obtain ⟨F, hb⟩ := le64Body config { contract := contract, locals := L } rfl evm m
  exact internalCallFunctionReturn (name := "le64") (callee := le64Fn) (evalExprs?_singleton he)
    rfl rfl hb

theorem eventCountCast {s0 : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (hb : L.get? "deposit_count" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.cast (.storage { base := "deposit_count" }) uint64StorageTy) =
      .ok (.int (Int.ofNat (mask64 (eventCount σ I)).toNat)) := by
  rw [evalCastInt (.uint ⟨64, by decide⟩) (evalDepositCount hb), hs.storageRead]
  exact congrArg (fun i => EvalResult.ok (Value.int i)) (normalize_u64_word _)

theorem eventCountLt {s0 : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (hb : L.get? "deposit_count" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .lt (.storage { base := "deposit_count" }) (.intLit 4294967295)) =
      .ok (.bool (decide ((eventCount σ I).toNat < 4294967295))) := by
  have hc := evalDepositCount (L := L) (evm := evm) hb
  rw [hs.storageRead] at hc
  refine evalBin (by decide) (by decide) hc (evalLit _) ?_
  have hlt : decide (Int.ofNat (eventCount σ I).toNat < (4294967295 : Int)) =
      decide ((eventCount σ I).toNat < 4294967295) := decide_eq_decide.mpr Int.ofNat_lt
  show EvalResult.ok (Value.bool (decide (Int.ofNat (eventCount σ I).toNat < (4294967295 : Int)))) = _
  rw [hlt]

theorem eventEmitArgs {node m c : UInt256} {pk wc sig : Value}
    (hE : EventLocals L node m pk wc sig) :
    evalExprs? config { contract := contract, locals := eventExitStore L m c } evm
        [.var "pubkey", .var "withdrawal_credentials", .var "amount_bytes", .var "signature",
          .var "index_bytes"] =
      .ok [pk, wc, .bytes ⟨(le64Bytes m).toArray⟩, sig, .bytes ⟨(le64Bytes (mask64 c)).toArray⟩] := by
  have h1 : (eventExitStore L m c).get? "pubkey" = some pk := by
    store_get; exact hE.pubkey
  have h2 : (eventExitStore L m c).get? "withdrawal_credentials" = some wc := by
    store_get; exact hE.wc
  have h3 : (eventExitStore L m c).get? "amount_bytes" = some (.bytes ⟨(le64Bytes m).toArray⟩) := by
    store_get
  have h4 : (eventExitStore L m c).get? "signature" = some sig := by
    store_get; exact hE.sig
  have h5 : (eventExitStore L m c).get? "index_bytes" =
      some (.bytes ⟨(le64Bytes (mask64 c)).toArray⟩) := store_get_self _ _ _
  simp only [evalExprs?, evalVar h1, evalVar h2, evalVar h3, evalVar h4, evalVar h5, bind,
    EvalResult.bind, pure]

end Stmts

/-! ## The coupled segment -/

/-- **The event segment** (statements 17..21, pc 1026 → 1592): a joint revert (root mismatch or
    full tree), a joint static halt at the event, or both sides at pc 1592 with the count below
    `2^32 - 1`, the Stele continuation running from the exit locals. -/
theorem depositEventSegment {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {L : Store} {p a r0 r1 r2 r3 r4 r5 : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : ℕ} {m : UInt256} {pk wc sig : Value}
    (hR : R.length ≤ 1000)
    (h0 : r0.toNat < 4294967296) (h1 : r1.toNat < 4294967296) (h4 : r4.toNat < 4294967296)
    (hE : EventLocals L (memLoad p mem) m pk wc sig)
    (hroot : evalExpr? config { contract := contract, locals := L } evm
      (.cast (.var "deposit_data_root") uint256StorageTy) = .ok (.int (Int.ofNat (eventRoot I).toNat)))
    (hs : SourceState s0 I σ evm)
    (rd : RD code I g s0 (UInt256.ofNat 1026) (p :: a :: r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: R)
      mem aw rdata σ k C) :
    (RDrev code g s0 ∧ ExecBlock config { contract := contract, locals := L } evm
      (depositTransition.body.drop 17) .reverted) ∨
    (RDstatic code g s0 ∧ ExecBlock config { contract := contract, locals := L } evm
      (depositTransition.body.drop 17) .staticViolation) ∨
    (I.perm = true ∧ ∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      RD code I g s0 (UInt256.ofNat 1592) (memLoad p mem :: eventCount σ I :: r5 :: R)
        mem' aw' rdata σ k' C' ∧
      (eventCount σ I).toNat < 4294967295 ∧
      ∀ res, ExecBlock config
          { contract := contract, locals := eventExitStore L m (eventCount σ I) } evm
          (depositTransition.body.drop 22) res →
        ExecBlock config { contract := contract, locals := L } evm
          (depositTransition.body.drop 17) res) := by
  obtain ⟨hmis, hstat, hbig, hok⟩ := depositEventTrace (ee := I) hR h0 h1 h4 rd
  rw [depositBody_drop17]
  by_cases heq : memLoad p mem = eventRoot I
  swap
  · refine Or.inl ⟨hmis heq, ExecBlock.consRevert (ExecStmt.requireFalse ?_)⟩
    rw [eventS17_eval hE.node hroot]; simp [heq]
  have hs17 : ExecStmt config { contract := contract, locals := L } evm eventS17
      (.ok { contract := contract, locals := L } evm) :=
    ExecStmt.requireTrue (by rw [eventS17_eval hE.node hroot]; simp [heq])
  have hs18 := le64Call (ret := "amount_bytes") (L := L) (evm := evm) (evalVar hE.amount)
  have hs19 := le64Call (ret := "index_bytes") (L := eventAmountStore L m) (evm := evm)
    (eventCountCast hs (by store_get; exact hE.count))
  have hargs := eventEmitArgs (evm := evm) (c := eventCount σ I) hE
  by_cases hperm : I.perm = true
  · have hs20 := ExecStmt.emit (cfg := config)
      (stele := { contract := contract, locals := eventExitStore L m (eventCount σ I) })
      (evm := evm) (name := "DepositEvent") (by rw [hs.env]; exact hperm) hargs
    have hlt := eventCountLt (L := eventExitStore L m (eventCount σ I)) (evm := evm) hs
      (by store_get; exact hE.count)
    by_cases hc : (eventCount σ I).toNat < 4294967295
    · obtain ⟨mem', aw', k', C', rd'⟩ := hok heq hperm hc
      refine Or.inr (Or.inr ⟨hperm, mem', aw', k', C', rd', hc, fun res hrest => ?_⟩)
      exact ExecBlock.consNormal hs17 <| ExecBlock.consNormal hs18 <| ExecBlock.consNormal hs19 <|
        ExecBlock.consNormal hs20 <| ExecBlock.consNormal
          (ExecStmt.requireTrue (by rw [hlt]; simp [hc])) hrest
    · refine Or.inl ⟨hbig heq hperm (by omega), ?_⟩
      exact ExecBlock.consNormal hs17 <| ExecBlock.consNormal hs18 <| ExecBlock.consNormal hs19 <|
        ExecBlock.consNormal hs20 <| ExecBlock.consRevert
          (ExecStmt.requireFalse (by rw [hlt]; simp [hc]))
  · have hpf : I.perm = false := by simpa using hperm
    refine Or.inr (Or.inl ⟨hstat heq hpf, ?_⟩)
    exact ExecBlock.consNormal hs17 <| ExecBlock.consNormal hs18 <| ExecBlock.consNormal hs19 <|
      ExecBlock.consStatic (ExecStmt.emitStatic hargs (by rw [hs.env]; exact hpf))

end FeProofs.Deposit
