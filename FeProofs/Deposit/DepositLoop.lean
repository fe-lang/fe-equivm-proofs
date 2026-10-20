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
import FeProofs.Deposit.RuntimeBlocks_010

/-!
# FeDeposit `deposit()` — the Merkle insertion loop

After `deposit_count` is incremented, the bytecode loops at pc 1605 over the stack
`[node, size, height]`: an odd `size` stores `node` in `branch[height]` and returns empty data
(pc 1627); an even one hashes `branch[height] ‖ node` through precompile 2 (pc 1654) and continues
with the digest, `size >> 1` and `height + 1`; after 32 rounds it panics (pc 1688).  The Stele loop
runs the same branch writes, `sha256_pair` calls and local updates, then `require(false)`.

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

/-- The two words the loop stores at `0xa0` and `0xc0` are the 64-byte call payload. -/
theorem twoWords_read (mem : ByteArray) (b n : UInt256) :
    (n.toByteArray.write 0 (b.toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)
        (UInt256.ofNat 192).toNat 32).readWithPadding (UInt256.ofNat 160).toNat
        (UInt256.ofNat 64).toNat = b.toByteArray ++ n.toByteArray := by
  rw [show (UInt256.ofNat 160).toNat = 160 from rfl, show (UInt256.ofNat 192).toNat = 192 from rfl,
    show (UInt256.ofNat 64).toNat = 32 + 32 from rfl]
  have h0 := toByteArray_write_size_ge_off_add32 b mem 160 (small_gap mem 160 (by decide))
  have h1 := toByteArray_write_size_ge_off_add32 n (b.toByteArray.write 0 mem 160 32) 192
    (small_gap _ 192 (by decide))
  rw [byteArray_readWithPadding_split _ 160 32 32 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega),
    toByteArray_write_read_below_of_gap n _ 192 160 (by omega) (by omega)
      (small_gap _ 192 (by decide)),
    toByteArray_write_read_back_of_gap b mem 160 (small_gap mem 160 (by decide)),
    show 160 + 32 = 192 from rfl,
    toByteArray_write_read_back_of_gap n _ 192 (small_gap _ 192 (by decide))]

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

/-- **The insertion loop.**  From the loop head with `32 - height` rounds left, the EVM run and the
    Stele loop end alike: both return after a branch write, both revert at a failing hash, or the
    EVM panics after the last round while the Stele loop finishes (its trailing `require(false)`
    then reverts). -/
theorem depositLoop {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true) :
    ∀ (v height : Nat) (node size : UInt256) (L : Store) (evm : EVM.State) (σ : AccountMap)
      (mem : ByteArray) (aw : UInt256) (rdata : ByteArray) (k C : Nat) (R : List UInt256),
    height + v = 32 → R.length ≤ 1000 →
    RD feDepositBytecode I g s0 (UInt256.ofNat 1605) (node :: size :: UInt256.ofNat height :: R)
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
    intro height node size L evm σ mem aw rdata k C R hv hR rd hs hn hsz hh hb
    have h32 : height = 32 := by omega
    subst h32
    refine Or.inr (Or.inr ⟨?_, _, _, ExecForLoop.falseDone (by rw [evalLoopCond hh]; rfl)⟩)
    rd_run rd
    exact rd
  | succ v ih =>
    intro height node size L evm σ mem aw rdata k C R hv hR rd hs hn hsz hh hb
    have hlt : height < 32 := by omega
    have hcondE : UInt256.isZero (UInt256.lt (UInt256.ofNat height) (UInt256.ofNat 32)) =
        UInt256.ofNat 0 := by
      rw [ult_one (by rw [ulit_toNat' height (lt_of_lt_of_le hlt (by decide)), ulit_toNat' 32 (by decide)]; exact hlt)]
      decide
    have hcondS : evalExpr? config { contract := contract, locals := L } evm dlCond =
        .ok (.bool true) := by
      rw [evalLoopCond hh, decide_eq_true hlt]
    rd_step rd using [hcondE]
    have hpermE : evm.executionEnv.perm = true := by rw [hs.env]; exact hperm
    by_cases hp : size.toNat % 2 = 1
    · have hland : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 1 :=
        u256_inj (by rw [land_one_toNat, hp]; rfl)
      rd_run rd using [hland, hperm]
      rw [show ((⟨0⟩ : UInt256).toNat) = 0 from rfl, byteArray_readWithPadding_zero] at rd
      have hret : ExecBlock config { contract := contract, locals := L } evm dlBody
          (.returned { contract := contract, locals := L }
            (Stele.EVM.storageStore evm evm.executionEnv.codeOwner (⟨0⟩ + UInt256.ofNat height) node)
            (some [])) :=
        ExecBlock.consReturn (ExecStmt.iteTrue (by rw [evalParity hsz, decide_eq_true hp])
          (ExecBlock.consNormal (ExecStmt.assign (Or.inr hpermE) (evalLocalVar hn)
            (assignBranch hlt hh hb node)) (ExecBlock.consReturn (ExecStmt.return evalEmptyReturn))))
      refine Or.inl ⟨_, _, _, rd, ExecForLoop.bodyReturn hcondS hret, ?_⟩
      have hw := (hs.storageWrite (UInt256.ofNat height) node).accounts
      rw [u256_zero_add, hs.env]
      exact hw.symm
    · have hp0 : size.toNat % 2 = 0 := by omega
      have hland : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 0 :=
        u256_inj (by rw [land_one_toNat, hp0]; rfl)
      rd_run rd using [hland]
      obtain ⟨evm', σ', z, out, aw', k3, C3, hcall, hs', rd4, hosz⟩ :=
        staticCallBridge rd hs (by native_decide) (by simp; omega)
      rw [twoWords_read, ← pairPayload_eq, ← precompile2_eq] at hcall
      have hsib : evalExpr? config { contract := contract, locals := L } evm
          (.storage dlBranchRef) =
          .ok (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat)) := by
        rw [evalBranch hlt hh hb, u256_zero_add, hs.storageRead]
      have hparS : evalExpr? config { contract := contract, locals := L } evm
          (.binary .eq (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "size") (.intLit 1))
            (.intLit 1)) = .ok (.bool false) := by
        rw [evalParity hsz, decide_eq_false hp]
      set L1 : Store :=
        L.insert "sibling" (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat))
        with hL1
      have hsibv : evalExpr? config { contract := contract, locals := L1 } evm (.var "sibling") =
          .ok (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat height)).toNat)) :=
        evalLocalVar (store_get_self _ _ _)
      have hnodev : evalExpr? config { contract := contract, locals := L1 } evm (.var "node") =
          .ok (.int (Int.ofNat node.toNat)) :=
        evalLocalVar (by store_get; exact hn)
      rd_checked rd4 z out as hrev hout to 1605
      · refine Or.inr (Or.inl ⟨hrev, ExecForLoop.bodyRevert hcondS ?_⟩)
        refine ExecBlock.consNormal (ExecStmt.iteFalse hparS ExecBlock.nil) ?_
        refine ExecBlock.consNormal (ExecStmt.letDecl hsib) ?_
        exact ExecBlock.consRevert (shaPairCall_revert (ret := "parent") rfl hsibv hnodev hcall hout)
      have hload : ∀ M : ByteArray, 160 + 32 ≤ M.size →
          memLoad (UInt256.ofNat 160) (callOutputMem M out (UInt256.ofNat 160) (UInt256.ofNat 32)) =
            calldataWord out 0 :=
        fun M hM => callOutput_load M out (UInt256.ofNat 160) hosz hout hM
      rw [hload _ (twoWords_size _ _ _),
        ofNat_succ_add height (show height + 1 < UInt256.size from lt_of_lt_of_le (Nat.succ_lt_succ hlt) (by decide))] at rd4
      have hcallS := shaPairCall_ok (ret := "parent") rfl hsibv hnodev hcall hout
      set L4 : Store := ((L1.insert "parent" (shaDigest out)).insert "node" (shaDigest out)).insert
        "size" (.int (Int.ofNat (UInt256.shiftRight size (UInt256.ofNat 1)).toNat)) with hL4
      set L5 : Store := L4.insert "height" (.int (Int.ofNat (height + 1))) with hL5
      have hih := ih (height + 1) (calldataWord out 0) (UInt256.shiftRight size (UInt256.ofNat 1))
        L5 evm' σ' _ _ _ _ _ R (by omega) hR rd4 hs'
        (by store_get)
        (by store_get)
        (store_get_self _ _ _)
        (by store_get; exact hb)
      have hbody : ExecBlock config { contract := contract, locals := L } evm dlBody
          (.ok { contract := contract, locals := L4 } evm') := by
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
      have hh4 : L4.get? "height" = some (.int (Int.ofNat height)) :=
        (by store_get; exact hh)
      have hpost : ExecBlock config { contract := contract, locals := L4 } evm' dlPost
          (.ok { contract := contract, locals := L5 } evm') :=
        ExecBlock.consNormal (ExecStmt.assign (Or.inl rfl) (evalInc hh4) (assignLocal hh4))
          ExecBlock.nil
      rcases hih with ⟨σf, frf, evmf, hret, hloop, hacc⟩ | ⟨hrev, hloop⟩ | ⟨hrev, frf, evmf, hloop⟩
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

/-- **`deposit()` from the count update on** (pc 1592, statement 22): both sides store the
    incremented count and run the insertion loop; the Stele `require(false)` matches the panic of
    an exhausted loop. -/
theorem depositTail {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true)
    {node count x2 : UInt256} {L : Store} {evm : EVM.State} {σ : AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 1592) (node :: count :: x2 :: R)
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
  obtain ⟨k1, C1, rd1⟩ := feDepositBlocks.feDeposit_block_1592 (by simp; omega) hperm rd
  simp only [feDepositBlocks.feDeposit_block_1592_stack] at rd1
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
  have hloop := depositLoop hperm 32 0 node w L2 evm1 _ mem aw rdata k1 C1 R (by rfl) hR rd1 hs1
    (by store_get; exact hn)
    (by store_get)
    (store_get_self _ _ _)
    (by store_get; exact hb)
  rcases hloop with ⟨σf, frf, evmf, hret, hfor, hacc⟩ | ⟨hrev, hfor⟩ | ⟨hrev, frf, evmf, hfor⟩
  · exact Or.inl ⟨σf, frf, evmf, hret, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consReturn (ExecStmt.for hinit hfor))), hacc⟩
  · exact Or.inr ⟨hrev, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consRevert (ExecStmt.for hinit hfor)))⟩
  · exact Or.inr ⟨hrev, ExecBlock.consNormal h22 (ExecBlock.consNormal h23
      (ExecBlock.consNormal (ExecStmt.for hinit hfor)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure])))))⟩

end FeProofs.Deposit
