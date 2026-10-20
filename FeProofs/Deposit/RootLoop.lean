import FeProofs.Deposit.RootTrace
import FeProofs.Deposit.RootFacts
import FeProofs.Deposit.Sha256

/-!
# FeDeposit `get_deposit_root()` — one loop iteration, EVM and Stele together

At loop iteration `i < 32` the EVM sits at pc 1866 with stack `[size, node, i, count]` and the
Stele loop has `height = i`, `node`, `size` in its locals.  One iteration either reverts on both
sides (the precompile call failed or returned fewer than 32 bytes) or reaches iteration `i + 1`
with `node := sha256(left ++ right)` (the precompile's first output word) and `size := size / 2`
on both sides, with the account maps kept in sync by `SourceState`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

abbrev uint256Ty : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

def rootCond : Expr := .binary .lt (.var "height") (.intLit 32)

def rootPost : List Stmt :=
  [.assign .localVar { base := "height" } (.binary .add (.var "height") (.intLit 1))]

def rootParity : Expr :=
  .binary .eq (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "size") (.intLit 1)) (.intLit 1)

def rootOdd : List Stmt :=
  [.letDecl "sibling" (some uint256Ty) (.storage { base := "branch", steps := [.aindex (.var "height")] }),
   .internalCall "sha256_pair" [.var "sibling", .var "node"] "parent",
   .assign .localVar { base := "node" } (.var "parent")]

def rootEven : List Stmt :=
  [.letDecl "zero" (some uint256Ty) (.storage { base := "zero_hashes", steps := [.aindex (.var "height")] }),
   .internalCall "sha256_pair" [.var "node", .var "zero"] "parent",
   .assign .localVar { base := "node" } (.var "parent")]

def rootLoopBody : List Stmt :=
  [.ite rootParity rootOdd rootEven,
   .assign .localVar { base := "size" } (.binary .div (.var "size") (.intLit 2))]

/-- The Stele locals at loop iteration `i`. -/
structure RootLocals (L : Store) (i : Nat) (node size count : UInt256) : Prop where
  count : L.get? "count" = some (.int (Int.ofNat count.toNat))
  height : L.get? "height" = some (.int (Int.ofNat i))
  node : L.get? "node" = some (.int (Int.ofNat node.toNat))
  size : L.get? "size" = some (.int (Int.ofNat size.toNat))
  branch : L.get? "branch" = none
  zero : L.get? "zero_hashes" = none

/-- The loop's frame with locals `L`. -/
abbrev fr (L : Store) : Frame := { contract := contract, locals := L }

/-- The locals after binding the odd lane's sibling word. -/
abbrev sibStore (L : Store) (a : UInt256) : Store := L.insert "sibling" (.int (Int.ofNat a.toNat))

/-- The locals after binding the even lane's zero-subtree word. -/
abbrev zeroStore (L : Store) (a : UInt256) : Store := L.insert "zero" (.int (Int.ofNat a.toNat))

local notation "code" => feDepositBytecode

/-- The outcome of one loop iteration on both sides: a joint revert, or iteration `i + 1`. -/
def RootStep (s0 : State) (I : ExecutionEnv) (g : Sat256) (evm : EVM.State) (L : Store) (i : Nat)
    (size count : UInt256) : Prop :=
  (RDrev code g s0 ∧
    ExecBlock config { contract := contract, locals := L } evm rootLoopBody .reverted) ∨
  (∃ (node' : UInt256) (σ' : AccountMap) (evm' : EVM.State) (mem' rdata' : ByteArray)
      (aw' : UInt256) (k' C' : ℕ) (L1 L2 : Store),
    RD code I g s0 (UInt256.ofNat 1866)
      [UInt256.shiftRight size (UInt256.ofNat 1), node', UInt256.ofNat (i + 1), count]
      mem' aw' rdata' σ' k' C' ∧
    SourceState s0 I σ' evm' ∧
    ExecBlock config { contract := contract, locals := L } evm rootLoopBody
      (.ok { contract := contract, locals := L1 } evm') ∧
    ExecBlock config { contract := contract, locals := L1 } evm' rootPost
      (.ok { contract := contract, locals := L2 } evm') ∧
    RootLocals L2 (i + 1) node' (UInt256.shiftRight size (UInt256.ofNat 1)) count)

/-- After a lane's hash: halve `size`, advance `height`, and re-establish the invariant. -/
theorem rootFinish {evm' : EVM.State} {L1 : Store} {i : Nat} {d size count : UInt256}
    (hcount : L1.get? "count" = some (.int (Int.ofNat count.toNat)))
    (hheight : L1.get? "height" = some (.int (Int.ofNat i)))
    (hnode : L1.get? "node" = some (.int (Int.ofNat d.toNat)))
    (hsize : L1.get? "size" = some (.int (Int.ofNat size.toNat)))
    (hbranch : L1.get? "branch" = none) (hzero : L1.get? "zero_hashes" = none) :
    ∃ L2 L3,
      ExecStmt config { contract := contract, locals := L1 } evm'
        (.assign .localVar { base := "size" } (.binary .div (.var "size") (.intLit 2)))
        (.ok { contract := contract, locals := L2 } evm') ∧
      ExecBlock config { contract := contract, locals := L2 } evm' rootPost
        (.ok { contract := contract, locals := L3 } evm') ∧
      RootLocals L3 (i + 1) d (UInt256.shiftRight size (UInt256.ofNat 1)) count := by
  refine ⟨L1.insert "size" (.int (Int.ofNat (UInt256.shiftRight size (UInt256.ofNat 1)).toNat)),
    (L1.insert "size" (.int (Int.ofNat (UInt256.shiftRight size (UInt256.ofNat 1)).toNat))).insert
      "height" (.int (Int.ofNat (i + 1))), ?_, ?_, ?_⟩
  · exact ExecStmt.assign (Or.inl rfl) (evalHalf hsize) (assignLocal hsize)
  · refine ExecBlock.consNormal (ExecStmt.assign (Or.inl rfl)
      (evalInc (by store_get; exact hheight))
      (assignLocal (by store_get; exact hheight))) ExecBlock.nil
  · refine ⟨?_, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
    · store_get; exact hcount
    · store_get; exact hnode
    · store_get
    · store_get; exact hbranch
    · store_get; exact hzero

theorem ofNat_toNat_lt32 {i : Nat} (hi : i < 32) : (UInt256.ofNat i).toNat = i :=
  ulit_toNat' i (lt_of_lt_of_le hi (by decide))

/-- One odd-lane iteration (`size` odd): hash `branch[height] ++ node`. -/
theorem rootOddStep {s0 : State} {I : ExecutionEnv} {g : Sat256} {evm : EVM.State} {L : Store}
    {i : Nat} {node size count : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : ℕ}
    (hi : i < 32) (hL : RootLocals L i node size count) (hodd : size.toNat % 2 = 1)
    (hs : SourceState s0 I σ evm)
    (rd : RD code I g s0 (UInt256.ofNat 1866) [size, node, UInt256.ofNat i, count]
      mem aw rdata σ k C) :
    RootStep s0 I g evm L i size count := by
  have rd1 := rootHeadContinue (by rw [ofNat_toNat_lt32 hi]; exact hi) rd
  have hland : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 1 := by
    apply u256_inj; rw [land_one_toNat, hodd]; rfl
  obtain ⟨gw, k2, C2, rd2⟩ := rootOddPre hland rd1
  obtain ⟨evm', σ', z, out, aw', k3, C3, hcall, hs', rd3, hout⟩ :=
    staticCallBridge rd2 hs (by native_decide) (by simp)
  have hpc : UInt256.ofNat 1908 + (⟨1⟩ : UInt256) = UInt256.ofNat 1909 := by decide
  rw [hpc] at rd3
  have hpost := rootLoopPost (UInt256.ofNat 1909) (Or.inl rfl) hout rd3
  -- the call's payload is `branch[height] ++ node`
  have hpay : ((UInt256.toByteArray node).write 0
      ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat i))).write 0 mem 160 32) 192 32
      ).readWithPadding (UInt256.ofNat 160).toNat (UInt256.ofNat 64).toNat =
      pairPayload (solcSlotWord σ I (UInt256.ofNat i)) node := by
    rw [pairPayload_eq]; exact rootPayload mem _ node
  have hcall' : callViaEVM evm (EVM.address precompile2) 0
      (pairPayload (solcSlotWord σ I (UInt256.ofNat i)) node) (z, evm', out) false := by
    rw [precompile2_eq, ← hpay]; exact hcall
  -- Stele: the sibling read, the parity test, and the hash call's arguments
  have hsib := evalBranch (evm := evm) hi hL.height hL.branch
  rw [hs.storageRead, u256_zero_add] at hsib
  have hlet := ExecStmt.letDecl (ty := some uint256Ty) (name := "sibling") hsib
  have hcond : evalExpr? config { contract := contract, locals := L } evm rootParity =
      .ok (.bool true) := by
    rw [rootParity, evalParity hL.size, hodd]; rfl
  have ha : evalExpr? config (fr (sibStore L (solcSlotWord σ I (UInt256.ofNat i))))
      evm (.var "sibling") = .ok (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat i)).toNat)) :=
    evalVar (store_get_self _ _ _)
  have hb : evalExpr? config (fr (sibStore L (solcSlotWord σ I (UInt256.ofNat i))))
      evm (.var "node") = .ok (.int (Int.ofNat node.toNat)) :=
    evalVar (by store_get; exact hL.node)
  by_cases hok : z = true ∧ 32 ≤ out.size
  · obtain ⟨rfl, hlen⟩ := hok
    have hsha := shaPairCall_ok (ret := "parent") rfl ha hb hcall' hlen
    -- `node := parent`
    have hparent := (store_get_self (L.insert "sibling"
      (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat i)).toNat))) "parent" (shaDigest out))
    have hnodeOld : ((L.insert "sibling"
        (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat i)).toNat))).insert "parent"
        (shaDigest out)).get? "node" = some (.int (Int.ofNat node.toNat)) := by
      store_get; exact hL.node
    have hasg := ExecStmt.assign (cfg := config) (origin := .localVar) (Or.inl rfl)
      (evalVar (c := contract) (evm := evm') hparent) (assignLocal (c := contract) hnodeOld)
    have hodd' : ExecBlock config { contract := contract, locals := L } evm rootOdd _ :=
      ExecBlock.consNormal hlet (ExecBlock.consNormal hsha (ExecBlock.consNormal hasg ExecBlock.nil))
    obtain ⟨L2, L3, hsize, hpostB, hL3⟩ := rootFinish (evm' := evm') (i := i)
      (d := calldataWord out 0) (size := size) (count := count)
      (L1 := (((L.insert "sibling"
        (.int (Int.ofNat (solcSlotWord σ I (UInt256.ofNat i)).toNat))).insert "parent"
        (shaDigest out)).insert "node" (shaDigest out)))
      (by store_get; exact hL.count)
      (by store_get; exact hL.height)
      (store_get_self _ _ _)
      (by store_get; exact hL.size)
      (by store_get; exact hL.branch)
      (by store_get; exact hL.zero)
    obtain ⟨k4, C4, rd4⟩ := hpost.2 rfl hlen
    have hmem : 224 ≤ ((UInt256.toByteArray node).write 0
        ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat i))).write 0 mem 160 32) 192 32).size :=
      toByteArray_write_size_ge_off_add32 node _ 192 (lt_usize _ (by omega))
    have hload : memLoad (UInt256.ofNat 160) (callOutputMem ((UInt256.toByteArray node).write 0
        ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat i))).write 0 mem 160 32) 192 32)
        out (UInt256.ofNat 160) (UInt256.ofNat 32)) = calldataWord out 0 :=
      callOutput_load _ out (UInt256.ofNat 160) hout hlen (by change 160 + 32 ≤ _; omega)
    rw [hload, ofNat_succ_add i (lt_of_lt_of_le (by omega : i + 1 < 33) (by decide))] at rd4
    exact Or.inr ⟨calldataWord out 0, σ', evm', _, out, _, k4, C4, L2, L3, rd4, hs',
      ExecBlock.consNormal (ExecStmt.iteTrue hcond hodd') (ExecBlock.consNormal hsize ExecBlock.nil),
      hpostB, hL3⟩
  · have hsha := shaPairCall_revert (ret := "parent") rfl ha hb hcall' hok
    have hbad : z = false ∨ out.size < 32 := by
      cases z
      · exact Or.inl rfl
      · exact Or.inr (Nat.lt_of_not_le (fun h => hok ⟨rfl, h⟩))
    exact Or.inl ⟨hpost.1 hbad, ExecBlock.consRevert (ExecStmt.iteTrue hcond
      (ExecBlock.consNormal hlet (ExecBlock.consRevert hsha)))⟩

/-- One even-lane iteration (`size` even): hash `node ++ zero_hashes[height]`. -/
theorem rootEvenStep {s0 : State} {I : ExecutionEnv} {g : Sat256} {evm : EVM.State} {L : Store}
    {i : Nat} {node size count : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : ℕ}
    (hi : i < 32) (hL : RootLocals L i node size count) (heven : size.toNat % 2 = 0)
    (hs : SourceState s0 I σ evm)
    (rd : RD code I g s0 (UInt256.ofNat 1866) [size, node, UInt256.ofNat i, count]
      mem aw rdata σ k C) :
    RootStep s0 I g evm L i size count := by
  have rd1 := rootHeadContinue (by rw [ofNat_toNat_lt32 hi]; exact hi) rd
  have hland : UInt256.land size (UInt256.ofNat 1) = UInt256.ofNat 0 := by
    apply u256_inj; rw [land_one_toNat, heven]; rfl
  obtain ⟨gw, k2, C2, rd2⟩ := rootEvenPre hland rd1
  obtain ⟨evm', σ', z, out, aw', k3, C3, hcall, hs', rd3, hout⟩ :=
    staticCallBridge rd2 hs (by native_decide) (by simp)
  have hpc : UInt256.ofNat 1957 + (⟨1⟩ : UInt256) = UInt256.ofNat 1958 := by decide
  rw [hpc] at rd3
  have hpost := rootLoopPost (UInt256.ofNat 1958) (Or.inr rfl) hout rd3
  -- the call's payload is `node ++ zero_hashes[height]`
  have hpay : ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat 33 + UInt256.ofNat i))).write 0
      ((UInt256.toByteArray node).write 0 mem 160 32) 192 32
      ).readWithPadding (UInt256.ofNat 160).toNat (UInt256.ofNat 64).toNat =
      pairPayload node (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i)) := by
    rw [pairPayload_eq]; exact rootPayload mem node _
  have hcall' : callViaEVM evm (EVM.address precompile2) 0
      (pairPayload node (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))) (z, evm', out) false := by
    rw [precompile2_eq, ← hpay]; exact hcall
  -- Stele: the zero-subtree read, the parity test, and the hash call's arguments
  have hzh := evalZeroHash (evm := evm) hi hL.height hL.zero
  rw [hs.storageRead] at hzh
  have hlet := ExecStmt.letDecl (ty := some uint256Ty) (name := "zero") hzh
  have hcond : evalExpr? config { contract := contract, locals := L } evm rootParity =
      .ok (.bool false) := by
    rw [rootParity, evalParity hL.size, heven]; rfl
  have ha : evalExpr? config (fr (zeroStore L (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))))
      evm (.var "node") = .ok (.int (Int.ofNat node.toNat)) :=
    evalVar (by store_get; exact hL.node)
  have hb : evalExpr? config (fr (zeroStore L (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))))
      evm (.var "zero") = .ok (.int (Int.ofNat (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i)).toNat)) :=
    evalVar (store_get_self _ _ _)
  by_cases hok : z = true ∧ 32 ≤ out.size
  · obtain ⟨rfl, hlen⟩ := hok
    have hsha := shaPairCall_ok (ret := "parent") rfl ha hb hcall' hlen
    -- `node := parent`
    have hparent := (store_get_self (zeroStore L (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))) "parent" (shaDigest out))
    have hnodeOld : ((zeroStore L (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))).insert "parent"
        (shaDigest out)).get? "node" = some (.int (Int.ofNat node.toNat)) := by
      store_get; exact hL.node
    have hasg := ExecStmt.assign (cfg := config) (origin := .localVar) (Or.inl rfl)
      (evalVar (c := contract) (evm := evm') hparent) (assignLocal (c := contract) hnodeOld)
    have heven' : ExecBlock config { contract := contract, locals := L } evm rootEven _ :=
      ExecBlock.consNormal hlet (ExecBlock.consNormal hsha (ExecBlock.consNormal hasg ExecBlock.nil))
    obtain ⟨L2, L3, hsize, hpostB, hL3⟩ := rootFinish (evm' := evm') (i := i)
      (d := calldataWord out 0) (size := size) (count := count)
      (L1 := (((zeroStore L (solcSlotWord σ I (⟨33⟩ + UInt256.ofNat i))).insert "parent"
        (shaDigest out)).insert "node" (shaDigest out)))
      (by store_get; exact hL.count)
      (by store_get; exact hL.height)
      (store_get_self _ _ _)
      (by store_get; exact hL.size)
      (by store_get; exact hL.branch)
      (by store_get; exact hL.zero)
    obtain ⟨k4, C4, rd4⟩ := hpost.2 rfl hlen
    have hmem : 224 ≤ ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat 33 + UInt256.ofNat i))).write 0
        ((UInt256.toByteArray node).write 0 mem 160 32) 192 32).size :=
      toByteArray_write_size_ge_off_add32 _ _ 192 (lt_usize _ (by omega))
    have hload : memLoad (UInt256.ofNat 160) (callOutputMem
        ((UInt256.toByteArray (solcSlotWord σ I (UInt256.ofNat 33 + UInt256.ofNat i))).write 0
        ((UInt256.toByteArray node).write 0 mem 160 32) 192 32)
        out (UInt256.ofNat 160) (UInt256.ofNat 32)) = calldataWord out 0 :=
      callOutput_load _ out (UInt256.ofNat 160) hout hlen (by change 160 + 32 ≤ _; omega)
    rw [hload, ofNat_succ_add i (lt_of_lt_of_le (by omega : i + 1 < 33) (by decide))] at rd4
    exact Or.inr ⟨calldataWord out 0, σ', evm', _, out, _, k4, C4, L2, L3, rd4, hs',
      ExecBlock.consNormal (ExecStmt.iteFalse hcond heven') (ExecBlock.consNormal hsize ExecBlock.nil),
      hpostB, hL3⟩
  · have hsha := shaPairCall_revert (ret := "parent") rfl ha hb hcall' hok
    have hbad : z = false ∨ out.size < 32 := by
      cases z
      · exact Or.inl rfl
      · exact Or.inr (Nat.lt_of_not_le (fun h => hok ⟨rfl, h⟩))
    exact Or.inl ⟨hpost.1 hbad, ExecBlock.consRevert (ExecStmt.iteFalse hcond
      (ExecBlock.consNormal hlet (ExecBlock.consRevert hsha)))⟩

/-- The whole hashing loop from iteration `i`: a joint revert, or both sides at iteration 32. -/
theorem rootLoop {s0 : State} {I : ExecutionEnv} {g : Sat256} {count : UInt256} :
    ∀ (n i : Nat) (evm : EVM.State) (L : Store) (node size : UInt256) (mem rdata : ByteArray)
      (aw : UInt256) (σ : AccountMap) (k C : ℕ),
    i + n = 32 → RootLocals L i node size count → SourceState s0 I σ evm →
    RD code I g s0 (UInt256.ofNat 1866) [size, node, UInt256.ofNat i, count] mem aw rdata σ k C →
    (RDrev code g s0 ∧
      ExecForLoop config (fr L) evm rootCond rootPost rootLoopBody .reverted) ∨
    (∃ (node' size' : UInt256) (σ' : AccountMap) (evm' : EVM.State) (mem' rdata' : ByteArray)
        (aw' : UInt256) (k' C' : ℕ) (L' : Store),
      RD code I g s0 (UInt256.ofNat 1866) [size', node', UInt256.ofNat 32, count]
        mem' aw' rdata' σ' k' C' ∧
      SourceState s0 I σ' evm' ∧
      ExecForLoop config (fr L) evm rootCond rootPost rootLoopBody (.ok (fr L') evm') ∧
      RootLocals L' 32 node' size' count) := by
  intro n
  induction n with
  | zero =>
      intro i evm L node size mem rdata aw σ k C hi hL hs rd
      have hi32 : i = 32 := by omega
      subst hi32
      exact Or.inr ⟨node, size, σ, evm, mem, rdata, aw, k, C, L, rd, hs,
        ExecForLoop.falseDone (by rw [rootCond, evalLoopCond hL.height]; rfl), hL⟩
  | succ n ih =>
      intro i evm L node size mem rdata aw σ k C hi hL hs rd
      have hlt : i < 32 := by omega
      have hcond : evalExpr? config (fr L) evm rootCond = .ok (.bool true) := by
        rw [rootCond, evalLoopCond hL.height]; simp [hlt]
      have hstep : RootStep s0 I g evm L i size count := by
        rcases Nat.mod_two_eq_zero_or_one size.toNat with h | h
        · exact rootEvenStep hlt hL h hs rd
        · exact rootOddStep hlt hL h hs rd
      rcases hstep with ⟨hrev, hbody⟩ |
        ⟨node', σ', evm', mem', rdata', aw', k', C', L1, L2, rd', hs', hbody, hpost, hL2⟩
      · exact Or.inl ⟨hrev, ExecForLoop.bodyRevert hcond hbody⟩
      · rcases ih (i + 1) evm' L2 node' _ mem' rdata' aw' σ' k' C' (by omega) hL2 hs' rd' with
          ⟨hrev, hloop⟩ | ⟨node'', size'', σ'', evm'', mem'', rdata'', aw'', k'', C'', L', rd'',
            hs'', hloop, hL'⟩
        · exact Or.inl ⟨hrev, ExecForLoop.iterate hcond hbody hpost hloop⟩
        · exact Or.inr ⟨node'', size'', σ'', evm'', mem'', rdata'', aw'', k'', C'', L', rd'', hs'',
            ExecForLoop.iterate hcond hbody hpost hloop, hL'⟩

end FeProofs.Deposit
