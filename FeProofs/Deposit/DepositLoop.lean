import FeProofs.Deposit.Sha256
import FeProofs.Deposit.RootFacts
import FeProofs.Deposit.RuntimeBlocks_001
import FeProofs.Deposit.RuntimeBlocks_002
import FeProofs.Deposit.RuntimeBlocks_003
import FeProofs.Deposit.RuntimeBlocks_004
import FeProofs.Deposit.RuntimeBlocks_005
import FeProofs.Deposit.RuntimeBlocks_006
import FeProofs.Deposit.RuntimeBlocks_007
import FeProofs.Deposit.RuntimeBlocks_008
import FeProofs.Deposit.RuntimeBlocks_009

/-!
# FeDeposit `deposit()` — the Merkle insertion loop

After `deposit_count` is incremented (pc 1582), the bytecode tests the parity of the new count
before entering the loop and again at the end of each round, so the loop body (pc 1624, stack
`[node, size, height]`) only runs for an even `size`: it hashes `branch[height] ‖ node` through
precompile 2 (pc 1644) and continues with the digest, `size >> 1` and `height + 1`; after 32
rounds it panics (pc 1701).  An odd `size` stores `node` in `branch[height]` and returns empty
data (pc 1695).  The Stele loop runs the same branch writes, `sha256_pair` calls and local
updates, then `require(false)`.

`depositLoop` couples the two loops by induction on the remaining rounds, keeping the Stele state
in `SourceState` with the EVM accounts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

abbrev dlCond : Expr := .binary .lt (.var "height") (.intLit 32)

abbrev dlPost : List Stmt :=
  [.assign .localVar { base := "height", steps := [] } (.binary .add (.var "height") (.intLit 1))]

abbrev dlBranchRef : StorageRef := { base := "branch", steps := [.aindex (.var "height")] }

abbrev dlBody : List Stmt :=
  [ .ite (.binary .eq (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "size") (.intLit 1))
        (.intLit 1))
      [ .assign .storage dlBranchRef (.var "node"), .return [] ] [],
    .letDecl "sibling" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.storage dlBranchRef),
    .internalCall "sha256_pair" [.var "sibling", .var "node"] "parent",
    .assign .localVar { base := "node", steps := [] } (.var "parent"),
    .assign .localVar { base := "size", steps := [] } (.binary .div (.var "size") (.intLit 2)) ]

theorem twoWords_size (mem : ByteArray) (b n : UInt256) :
    160 + 32 ≤ (n.toByteArray.write 0 (b.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)
        (UInt256.ofNat 192).toNat 32).size := by
  have h := toByteArray_write_size_ge_off_add32 n
    (b.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) 192 (small_gap _ 192 (by decide))
  exact le_trans (by decide) h

theorem branchLoc {i : Nat} (hi : i < 32) :
    layout { base := "branch", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (uint256Loc (⟨0⟩ + UInt256.ofNat i))) := by
  show some (StorageAddr.leaf _) = _
  simp only [keyWord_ofNat, ulit_toNat' i (lt_of_lt_of_le hi (by decide)), Nat.div_one,
    Nat.mod_one, Nat.zero_mul]
  rfl

/-- `branch[height] = w` for an in-bounds `height`. -/
theorem assignBranch {L : Store} {evm : EVM.State} {i : Nat} (hi : i < 32)
    (hh : L.get? "height" = some (.int (Int.ofNat i))) (hbase : L.get? "branch" = none)
    (w : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage dlBranchRef
        (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (⟨0⟩ + UInt256.ofNat i) w) := by
  have hidx : evalExpr? config { contract := contract, locals := L } evm (.var "height") =
      .ok (.int (Int.ofNat i)) := evalLocalVar hh
  have hty : storageTypeAt? contract.storage { base := "branch", steps := [] } =
      some (.array (.elem uint256Elem) 32) := rfl
  have her : evalStorageRef config { contract := contract, locals := L } evm dlBranchRef =
      .ok { base := "branch", steps := [.aindex (.int (Int.ofNat i))] } := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
      arrayIndexInBounds?, hty, bind, EvalResult.bind, pure, EvalResult.ofOption, hi]
  exact assignStorageRef_storage_scalar_value (ty := .elem uint256Elem) hbase her rfl
    config_storageBackend (branchLoc hi) (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ w)

theorem evalEmptyReturn {fr : Frame} {evm : EVM.State} : evalExprs? config fr evm [] = .ok [] := by
  simp [evalExprs?, pure]

/-- An odd `size` at an in-bounds `height`: the Stele loop stores `node` in `branch[height]` and
    returns. -/
theorem dlOddReturn {L : Store} {evm : EVM.State} {height : Nat} {node size : UInt256}
    (hlt : height < 32) (hperm : evm.executionEnv.perm = true) (hp : size.toNat % 2 = 1)
    (hn : L.get? "node" = some (.int (Int.ofNat node.toNat)))
    (hsz : L.get? "size" = some (.int (Int.ofNat size.toNat)))
    (hh : L.get? "height" = some (.int (Int.ofNat height)))
    (hb : L.get? "branch" = none) :
    ExecForLoop config { contract := contract, locals := L } evm dlCond dlPost dlBody
      (.returned { contract := contract, locals := L }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner (⟨0⟩ + UInt256.ofNat height) node)
        (some [])) :=
  ExecForLoop.bodyReturn (by rw [evalLoopCond hh, decide_eq_true hlt])
    (ExecBlock.consReturn (ExecStmt.iteTrue (by rw [evalParity hsz, decide_eq_true hp])
      (ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (evalLocalVar hn)
        (assignBranch hlt hh hb node)) (ExecBlock.consReturn (ExecStmt.return evalEmptyReturn)))))

/-- The locals after a hashing round's body. -/
abbrev dlL4 (L : Store) (sib : UInt256) (size : UInt256) (out : ByteArray) : Store :=
  (((L.insert "sibling" (.int (Int.ofNat sib.toNat))).insert "parent" (shaDigest out)).insert
    "node" (shaDigest out)).insert
    "size" (.int (Int.ofNat (UInt256.shiftRight size (UInt256.ofNat 1)).toNat))

/-- The locals after a hashing round and the loop's increment. -/
abbrev dlL5 (L : Store) (sib : UInt256) (size : UInt256) (out : ByteArray) (height : Nat) : Store :=
  (dlL4 L sib size out).insert "height" (.int (Int.ofNat (height + 1)))

/-- **One hashing round** (an even `size` at an in-bounds `height`): both sides revert at a
    failing hash, or the EVM stands after the call's checks (pc 1661) with the digest at `0xa0`
    while the Stele loop has run its body and increment. -/
theorem depositRound {I : ExecutionEnv} {g : Sat256} {s0 : State} {height : Nat}
    {node size : UInt256} {L : Store} {evm : EVM.State} {σ : AccountMap} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (hlt : height < 32) (hR : R.length ≤ 1000) (hp0 : size.toNat % 2 = 0)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 1624)
      (node :: size :: UInt256.ofNat height :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hn : L.get? "node" = some (.int (Int.ofNat node.toNat)))
    (hsz : L.get? "size" = some (.int (Int.ofNat size.toNat)))
    (hh : L.get? "height" = some (.int (Int.ofNat height)))
    (hb : L.get? "branch" = none) :
    (RDrev feDepositBytecode g s0 ∧
        ExecBlock config { contract := contract, locals := L } evm dlBody .reverted) ∨
    (∃ (out : ByteArray) (evm' : EVM.State) (σ' : AccountMap) (memN : ByteArray) (awN : UInt256)
        (kN CN : Nat),
      RD feDepositBytecode I g s0 (UInt256.ofNat 1661) (size :: UInt256.ofNat height :: R)
        memN awN out σ' kN CN ∧
      memLoad (UInt256.ofNat 160) memN = calldataWord out 0 ∧
      SourceState s0 I σ' evm' ∧
      ExecBlock config { contract := contract, locals := L } evm dlBody
        (.ok { contract := contract,
               locals := dlL4 L (solcSlotWord σ I (UInt256.ofNat height)) size out } evm') ∧
      ExecBlock config
        { contract := contract,
          locals := dlL4 L (solcSlotWord σ I (UInt256.ofNat height)) size out } evm' dlPost
        (.ok { contract := contract,
               locals := dlL5 L (solcSlotWord σ I (UInt256.ofNat height)) size out height } evm')) := by
  rd_step rd
  obtain ⟨evm', σ', z, out, awN, k3, C3, hcall, hs', rd4, hosz⟩ :=
    staticCallBridge rd hs (by native_decide) (by simp; omega)
  u256_lits at hcall
  rw [pairWords_read _ _ _ 160 192 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hcall
  have hsib : evalExpr? config { contract := contract, locals := L } evm
      (.storage dlBranchRef) =
      .ok (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat)) := by
    rw [evalBranch hlt hh hb, u256_zero_add, hs.storageRead]
  have hparS : evalExpr? config { contract := contract, locals := L } evm
      (.binary .eq (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "size") (.intLit 1))
        (.intLit 1)) = .ok (.bool false) := by
    rw [evalParity hsz, decide_eq_false (by omega)]
  set L1 : Store :=
    L.insert "sibling" (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat))
    with hL1
  have hsibv : evalExpr? config { contract := contract, locals := L1 } evm (.var "sibling") =
      .ok (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat)) :=
    evalLocalVar (store_get_self _ _ _)
  have hnodev : evalExpr? config { contract := contract, locals := L1 } evm (.var "node") =
      .ok (.int (Int.ofNat node.toNat)) :=
    evalLocalVar (by store_get; exact hn)
  rd_checked rd4 z out as hrev hout to 1661
  · refine Or.inl ⟨hrev, ?_⟩
    refine ExecBlock.consNormal (ExecStmt.iteFalse hparS ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsib) ?_
    exact ExecBlock.consRevert (shaPairCall_revert (ret := "parent") rfl hsibv hnodev hcall hout)
  have hload := callOutput_load _ out (UInt256.ofNat 160) hosz hout (twoWords_size mem
    (solcSlotWord σ I (UInt256.ofNat height)) node)
  have hcallS := shaPairCall_ok (ret := "parent") rfl hsibv hnodev hcall hout
  have hbody : ExecBlock config { contract := contract, locals := L } evm dlBody
      (.ok { contract := contract,
             locals := dlL4 L (solcSlotWord σ I (UInt256.ofNat height)) size out } evm') := by
    refine ExecBlock.consNormal (ExecStmt.iteFalse hparS ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsib) ?_
    refine ExecBlock.consNormal hcallS ?_
    refine ExecBlock.consNormal (ExecStmt.assign (Or.inl rfl) (evalLocalVar (store_get_self _ _ _))
      (assignLocal (old := .int (Int.ofNat node.toNat))
        (by store_get; exact hn))) ?_
    refine ExecBlock.consNormal (ExecStmt.assign (Or.inl rfl)
      (evalHalf (by store_get; exact hsz))
      (assignLocal (old := .int (Int.ofNat size.toNat))
        (by store_get; exact hsz))) ?_
    exact ExecBlock.nil
  have hh4 : (dlL4 L (solcSlotWord σ I (UInt256.ofNat height)) size out).get? "height" =
      some (.int (Int.ofNat height)) :=
    (by store_get; exact hh)
  exact Or.inr ⟨out, evm', σ', _, _, _, _, rd4, hload, hs', hbody,
    ExecBlock.consNormal (ExecStmt.assign (Or.inl rfl) (evalInc hh4) (assignLocal hh4))
      ExecBlock.nil⟩

/-- **The insertion loop.**  From the loop body with an even `size` and `32 - height` rounds left,
    the EVM run and the Stele loop end alike: both return after a branch write, both revert at a
    failing hash, or the EVM panics after the last round while the Stele loop finishes (its
    trailing `require(false)` then reverts). -/
theorem depositLoop {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true) :
    ∀ (v height : Nat) (node size : UInt256) (L : Store) (evm : EVM.State) (σ : AccountMap)
      (mem : ByteArray) (aw : UInt256) (rdata : ByteArray) (k C : Nat) (R : List UInt256),
    height + v = 31 → R.length ≤ 1000 → size.toNat % 2 = 0 →
    RD feDepositBytecode I g s0 (UInt256.ofNat 1624) (node :: size :: UInt256.ofNat height :: R)
      mem aw rdata σ k C →
    SourceState s0 I σ evm →
    L.get? "node" = some (.int (Int.ofNat node.toNat)) →
    L.get? "size" = some (.int (Int.ofNat size.toNat)) →
    L.get? "height" = some (.int (Int.ofNat height)) →
    L.get? "branch" = none →
    (∃ σf frf evmf, RDret feDepositBytecode g s0 σf ByteArray.empty ∧
        ExecForLoop config { contract := contract, locals := L } evm dlCond dlPost dlBody
          (.returned frf evmf (some [])) ∧ evmf.accountMap = σf) ∨
    (RDrev feDepositBytecode g s0 ∧
        ExecForLoop config { contract := contract, locals := L } evm dlCond dlPost dlBody .reverted) ∨
    (RDrev feDepositBytecode g s0 ∧ ∃ frf evmf,
        ExecForLoop config { contract := contract, locals := L } evm dlCond dlPost dlBody
          (.ok frf evmf)) := by
  intro v
  induction v with
  | zero =>
    intro height node size L evm σ mem aw rdata k C R hv hR hp0 rd hs hn hsz hh hb
    have h31 : height = 31 := by omega
    subst h31
    have hcondS : evalExpr? config { contract := contract, locals := L } evm dlCond =
        .ok (.bool true) := by
      rw [evalLoopCond hh]; rfl
    rcases depositRound (by decide) hR hp0 rd hs hn hsz hh hb with
      ⟨hrev, hbody⟩ | ⟨out, evm', σ', memN, awN, kN, CN, rd4, hload, hs', hbody, hpost⟩
    · exact Or.inr (Or.inl ⟨hrev, ExecForLoop.bodyRevert hcondS hbody⟩)
    rd_run rd4
    exact Or.inr (Or.inr ⟨rd4, _, _, ExecForLoop.iterate hcondS hbody hpost
      (ExecForLoop.falseDone (by rw [evalLoopCond (store_get_self _ _ _)]; rfl))⟩)
  | succ v ih =>
    intro height node size L evm σ mem aw rdata k C R hv hR hp0 rd hs hn hsz hh hb
    have hlt : height + 1 < 32 := by omega
    have hcondS : evalExpr? config { contract := contract, locals := L } evm dlCond =
        .ok (.bool true) := by
      rw [evalLoopCond hh, decide_eq_true (by omega)]
    rcases depositRound (by omega) hR hp0 rd hs hn hsz hh hb with
      ⟨hrev, hbody⟩ | ⟨out, evm', σ', memN, awN, kN, CN, rd4, hload, hs', hbody, hpost⟩
    · exact Or.inr (Or.inl ⟨hrev, ExecForLoop.bodyRevert hcondS hbody⟩)
    have hsucc := ofNat_succ_add height (show height + 1 < UInt256.size from
      lt_of_lt_of_le hlt (by decide))
    have hcondE : UInt256.isZero (UInt256.lt (UInt256.ofNat 1 + UInt256.ofNat height)
        (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
      rw [hsucc, ult_one (by
        rw [ulit_toNat' (height + 1) (lt_of_lt_of_le hlt (by decide)), ulit_toNat' 32 (by decide)]
        exact hlt)]
      decide
    rd_step rd4 using [hcondE]
    rw [hload, hsucc] at rd4
    have hpermE : evm'.executionEnv.perm = true := by rw [hs'.env]; exact hperm
    set L5 : Store := dlL5 L (solcSlotWord σ I (UInt256.ofNat height)) size out height with hL5
    have hn5 : L5.get? "node" = some (.int (Int.ofNat (calldataWord out 0).toNat)) := by
      store_get
    have hsz5 : L5.get? "size" =
        some (.int (Int.ofNat (UInt256.shiftRight size (UInt256.ofNat 1)).toNat)) := by
      store_get
    have hh5 : L5.get? "height" = some (.int (Int.ofNat (height + 1))) := store_get_self _ _ _
    have hb5 : L5.get? "branch" = none := by
      store_get; exact hb
    by_cases hp : (UInt256.shiftRight size (UInt256.ofNat 1)).toNat % 2 = 1
    · have hland : UInt256.land (UInt256.shiftRight size (UInt256.ofNat 1)) (UInt256.ofNat 1) =
          UInt256.ofNat 1 := u256_inj (by rw [land_one_toNat, hp]; rfl)
      rd_run rd4 using [hland, hperm]
      rw [show ((⟨0⟩ : UInt256).toNat) = 0 from rfl, byteArray_readWithPadding_zero] at rd4
      refine Or.inl ⟨_, _, _, rd4, ExecForLoop.iterate hcondS hbody hpost
        (dlOddReturn hlt hpermE hp hn5 hsz5 hh5 hb5), ?_⟩
      have hw := (hs'.storageWrite (UInt256.ofNat (height + 1)) (calldataWord out 0)).accounts
      rw [u256_zero_add, hs'.env]
      exact hw.symm
    · have hp0' : (UInt256.shiftRight size (UInt256.ofNat 1)).toNat % 2 = 0 := by omega
      have hland : UInt256.land (UInt256.shiftRight size (UInt256.ofNat 1)) (UInt256.ofNat 1) =
          UInt256.ofNat 0 := u256_inj (by rw [land_one_toNat, hp0']; rfl)
      rd_run rd4 to 1624 using [hland]
      rcases ih (height + 1) (calldataWord out 0) (UInt256.shiftRight size (UInt256.ofNat 1))
          L5 evm' σ' _ _ _ _ _ R (by omega) hR hp0' rd4 hs' hn5 hsz5 hh5 hb5 with
        ⟨σf, frf, evmf, hret, hloop, hacc⟩ | ⟨hrev, hloop⟩ | ⟨hrev, frf, evmf, hloop⟩
      · exact Or.inl ⟨σf, frf, evmf, hret, ExecForLoop.iterate hcondS hbody hpost hloop, hacc⟩
      · exact Or.inr (Or.inl ⟨hrev, ExecForLoop.iterate hcondS hbody hpost hloop⟩)
      · exact Or.inr (Or.inr ⟨hrev, frf, evmf, ExecForLoop.iterate hcondS hbody hpost hloop⟩)

abbrev dcRef : StorageRef := { base := "deposit_count", steps := [] }

/-- `deposit()`'s statements 22–25: the count update, the insertion loop and the final
    `require(false)`. -/
abbrev depositTailStmts : List Stmt :=
  [ .letDecl "size" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.binary .add (.storage dcRef) (.intLit 1)),
    .assign .storage dcRef (.var "size"),
    .for [.letDecl "height" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
      dlCond dlPost dlBody,
    .require (.boolLit false) ]

theorem depositTailStmts_eq : (contract.transitions[1]!).body.drop 22 = depositTailStmts := by
  rfl

theorem countSucc_toNat {count : UInt256} (hlt : count.toNat < 2 ^ 32 - 1) :
    (UInt256.ofNat 1 + count).toNat = count.toNat + 1 := by
  have hsz : 4294967296 ≤ UInt256.size := by decide
  rw [uadd_toNat, ulit_toNat' 1 (by decide), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **`deposit()` from the count update on** (pc 1582, statement 22): both sides store the
    incremented count and run the insertion loop; the Stele `require(false)` matches the panic of
    an exhausted loop. -/
theorem depositTail {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true)
    {node count x2 : UInt256} {L : Store} {evm : EVM.State} {σ : AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 1582) (node :: count :: x2 :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hcount : solcSlotWord σ I (UInt256.ofNat 32) = count)
    (hlt : count.toNat < 2 ^ 32 - 1)
    (hn : L.get? "node" = some (.int (Int.ofNat node.toNat)))
    (hb : L.get? "branch" = none) (hdc : L.get? "deposit_count" = none) :
    (∃ σf frf evmf, RDret feDepositBytecode g s0 σf ByteArray.empty ∧
        ExecBlock config { contract := contract, locals := L } evm depositTailStmts
          (.returned frf evmf (some [])) ∧ evmf.accountMap = σf) ∨
    (RDrev feDepositBytecode g s0 ∧
        ExecBlock config { contract := contract, locals := L } evm depositTailStmts .reverted) := by
  set w : UInt256 := UInt256.ofNat 1 + count with hw
  have hwNat : w.toNat = count.toNat + 1 := countSucc_toNat hlt
  have hcode : evm.executionEnv.codeOwner = I.codeOwner := by rw [hs.env]
  -- statement 22: size = deposit_count + 1
  have hread : evalExpr? config { contract := contract, locals := L } evm (.storage dcRef) =
      .ok (.int (Int.ofNat count.toNat)) := by
    rw [evalDepositCount hdc, hs.storageRead, hcount]
  have hsizeE : evalExpr? config { contract := contract, locals := L } evm
      (.binary .add (.storage dcRef) (.intLit 1)) = .ok (.int (Int.ofNat w.toNat)) := by
    rw [evalExpr?]
    · simp only [hread, EvalResult.bind, bind]
      rw [show evalExpr? config { contract := contract, locals := L } evm (.intLit 1) =
        .ok (.int 1) by simp [evalExpr?, pure]]
      simp only [evalBinaryOp?, hwNat]
      rfl
    all_goals intro h; cases h
  set L1 : Store := L.insert "size" (.int (Int.ofNat w.toNat)) with hL1
  -- statement 23: deposit_count = size
  have hassign : assignStorageRef? config { contract := contract, locals := L1 } evm .storage dcRef
      (.int (Int.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := L1 },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 32) w) :=
    assignStorageRef_storage_scalar_value (ty := .elem uint256Elem)
      (by store_get; exact hdc) (by simp only [evalStorageRef, evalStorageRefSteps]; rfl) rfl
      config_storageBackend (loc := uint256Loc (UInt256.ofNat 32)) rfl (Or.inl ⟨_, rfl⟩)
      (storageLocStore_uint256 evm _ w)
  rw [hcode] at hassign
  set evm1 := Stele.EVM.storageStore evm I.codeOwner (UInt256.ofNat 32) w with hevm1
  have hs1 := hs.storageWrite (UInt256.ofNat 32) w
  have hpermE : evm.executionEnv.perm = true := by rw [hs.env]; exact hperm
  have h22 : ExecStmt config { contract := contract, locals := L } evm
      (.letDecl "size" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.binary .add (.storage dcRef) (.intLit 1)))
      (.ok { contract := contract, locals := L1 } evm) := ExecStmt.letDecl hsizeE
  have h23 : ExecStmt config { contract := contract, locals := L1 } evm
      (.assign .storage dcRef (.var "size")) (.ok { contract := contract, locals := L1 } evm1) :=
    ExecStmt.assign (Or.inr hpermE) (evalLocalVar (store_get_self _ _ _)) hassign
  set L2 : Store := L1.insert "height" (.int 0) with hL2
  have hinit : ExecBlock config { contract := contract, locals := L1 } evm1
      [.letDecl "height" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
      (.ok { contract := contract, locals := L2 } evm1) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, pure])) ExecBlock.nil
  have hn2 : L2.get? "node" = some (.int (Int.ofNat node.toNat)) := by
    store_get; exact hn
  have hsz2 : L2.get? "size" = some (.int (Int.ofNat w.toNat)) := by
    store_get
  have hh2 : L2.get? "height" = some (.int (Int.ofNat 0)) := store_get_self _ _ _
  have hb2 : L2.get? "branch" = none := by
    store_get; exact hb
  by_cases hp : w.toNat % 2 = 1
  · -- an odd count: `branch[0] = node` and return
    have hland : UInt256.land (UInt256.ofNat 1 + count) (UInt256.ofNat 1) = UInt256.ofNat 1 :=
      u256_inj (by rw [land_one_toNat, hp]; rfl)
    rd_run rd using [hland, hperm]
    rw [show ((⟨0⟩ : UInt256).toNat) = 0 from rfl, byteArray_readWithPadding_zero] at rd
    have hpermE1 : evm1.executionEnv.perm = true := by rw [hs1.env]; exact hperm
    refine Or.inl ⟨_, _, _, rd, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consReturn (ExecStmt.for hinit
        (dlOddReturn (by decide) hpermE1 hp hn2 hsz2 hh2 hb2)))), ?_⟩
    have hw' := (hs1.storageWrite (UInt256.ofNat 0) node).accounts
    rw [u256_zero_add, hs1.env]
    exact hw'.symm
  have hp0 : w.toNat % 2 = 0 := by omega
  have hland : UInt256.land (UInt256.ofNat 1 + count) (UInt256.ofNat 1) = UInt256.ofNat 0 :=
    u256_inj (by rw [land_one_toNat, hp0]; rfl)
  rd_run rd to 1624 using [hland, hperm]
  have hloop := depositLoop hperm 31 0 node w L2 evm1 _ mem aw rdata _ _ R (by rfl) hR hp0 rd hs1
    hn2 hsz2 hh2 hb2
  rcases hloop with ⟨σf, frf, evmf, hret, hfor, hacc⟩ | ⟨hrev, hfor⟩ | ⟨hrev, frf, evmf, hfor⟩
  · exact Or.inl ⟨σf, frf, evmf, hret, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consReturn (ExecStmt.for hinit hfor))), hacc⟩
  · exact Or.inr ⟨hrev, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consRevert (ExecStmt.for hinit hfor)))⟩
  · exact Or.inr ⟨hrev, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consNormal (ExecStmt.for hinit hfor)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure])))))⟩

end FeProofs.Deposit
