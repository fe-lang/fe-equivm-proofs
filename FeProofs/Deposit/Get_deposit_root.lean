import FeProofs.Deposit.Dispatch
import FeProofs.Deposit.RootLoop
import FeProofs.Deposit.Le64
import FeProofs.Common.Basic

/-!
# FeDeposit `get_deposit_root()`

Arm entry pc 1853: call-value check, `count := SLOAD(32)`, the 32-iteration hashing loop
(`RootLoop.lean`), then the SSZ length mix-in `sha256(node ++ u64_chunk(count))` (pc 2084) and the
return of its digest.  Every precompile call is coupled to the spec's `sha256_pair` through
`Sha256.lean`; a failed call or a short output reverts on both sides.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

local notation "code" => feDepositBytecode

abbrev u64Ty : StorageType := .elem (.int (.uint ⟨64, by decide⟩))

def rootInit : List Stmt := [.letDecl "height" (some uint256Ty) (.intLit 0)]

theorem rootBody_eq : get_deposit_rootTransition.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "count" (some uint256Ty) (.storage { base := "deposit_count" }),
      .letDecl "node" (some uint256Ty) (.intLit 0),
      .letDecl "size" (some uint256Ty) (.var "count"),
      .for rootInit rootCond rootPost rootLoopBody,
      .internalCall "u64_chunk" [.cast (.var "count") u64Ty] "length_chunk",
      .internalCall "sha256_pair" [.var "node", .var "length_chunk"] "root",
      .return [.var "root"] ] := rfl

/-- The locals after the body's three `let`s, with `count = c`. -/
abbrev rootPrefixStore (c : UInt256) : Store :=
  (((∅ : Store).insert "count" (.int (Int.ofNat c.toNat))).insert "node" (.int 0)).insert "size"
    (.int (Int.ofNat c.toNat))

theorem feDepositGet_deposit_rootBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feDepositSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feDepositSelBytes 3) rfl hsel
  have hne : ∀ j, j < 3 → ¬ selIs I (feDepositSelBytes j) := fun j hj hj' => by
    have heq := (byteArray_eq_of_beq hsel).trans (byteArray_eq_of_beq hj').symm
    interval_cases j
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
  have hd := feDepositDispatch_get_deposit_root (hne 0 (by omega)) (hne 1 (by omega))
    (hne 2 (by omega)) hsel
  have hdec : config.externalABI.decodeCalldata? (get_deposit_rootTransition.params.map Param.name)
      (transitionSignature get_deposit_rootTransition).paramTypes I.calldata = some ∅ := by
    show decodeCalldata [] [] I.calldata = some ∅
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := feDepositReachGet_deposit_rootBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact RDrev.reEquivDispatchedRevert hcode (rootCallvalue hwv rd) hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  obtain ⟨k1, C1, rd1⟩ := rootPrologue hwv rd
  -- the body's prefix: `require`, `count`, `node`, `size`, and the loop's `height := 0`
  have hs0 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := SourceState.init
  have hcount := evalDepositCount (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (by simp)
  rw [hs0.storageRead] at hcount
  have hreq := ExecStmt.requireTrue (cfg := config) (stele := fr ∅)
    (evalCallvalueEq_true (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv))
  have hletCount := ExecStmt.letDecl (cfg := config) (stele := fr ∅) (name := "count")
    (ty := some uint256Ty) hcount
  have hletNode := ExecStmt.letDecl (cfg := config)
    (stele := fr ((∅ : Store).insert "count" (.int (Int.ofNat (countWord σ I).toNat))))
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (name := "node") (ty := some uint256Ty)
    (expr := .intLit 0) (value := .int 0) (by simp [evalExpr?, pure])
  have hletSize := ExecStmt.letDecl (cfg := config)
    (stele := fr (((∅ : Store).insert "count" (.int (Int.ofNat (countWord σ I).toNat))).insert
      "node" (.int 0)))
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (name := "size") (ty := some uint256Ty)
    (evalVar (by rw [get_ins_ne (k := "node") (a := "count") (by decide)]
                 exact store_get_self _ _ _))
  have hinit : ExecBlock config (fr (rootPrefixStore (countWord σ I)))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) rootInit
      (.ok (fr ((rootPrefixStore (countWord σ I)).insert "height" (.int 0)))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, pure])) ExecBlock.nil
  have hL0 : RootLocals ((rootPrefixStore (countWord σ I)).insert "height" (.int 0)) 0 ⟨0⟩
      (countWord σ I) (countWord σ I) := by
    refine ⟨?_, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [get_ins_ne (by decide), get_ins_ne (by decide),
        get_ins_ne (by decide)]; exact store_get_self _ _ _
    · rw [get_ins_ne (by decide), get_ins_ne (by decide)]
      exact store_get_self _ _ _
    · rw [get_ins_ne (by decide)]; exact store_get_self _ _ _
    · simp
    · simp
  rcases rootLoop (count := countWord σ I) 32 0 _ _ ⟨0⟩ (countWord σ I) _ _ _ _ _ _ rfl hL0 hs0
      rd1 with
    ⟨hrev, hloop⟩ |
    ⟨node', size', σ', evm', mem', rdata', aw', k', C', L', rd2, hs', hloop, hL'⟩
  · exact RDrev.reEquivExecutionRevert hcode hrev hd hdec (by
      rw [rootBody_eq]
      exact ExecFuncBody.execBlockRevert <|
        ExecBlock.consNormal hreq <| ExecBlock.consNormal hletCount <|
        ExecBlock.consNormal hletNode <| ExecBlock.consNormal hletSize <|
        ExecBlock.consRevert (ExecStmt.for hinit hloop))
  -- the loop exit and the length mix-in call
  have rd3 := feDepositBlocks.feDeposit_block_1991 (by simp) (rootHeadExit (by decide) rd2)
  simp only [feDepositBlocks.feDeposit_block_1991_stack] at rd3
  obtain ⟨evm'', σ'', z, out, aw'', k'', C'', hcall, hs'', rd4, hout⟩ :=
    staticCallBridge rd3 hs' (by native_decide) (by simp)
  have hpc : UInt256.ofNat 2084 + (⟨1⟩ : UInt256) = UInt256.ofNat 2085 := by decide
  rw [hpc] at rd4
  have hpost := rootExitPost (R := []) (by simp) hout rd4
  have hpay : (feDepositBlocks.feDeposit_block_1991_memory (mem := mem') (x1 := node')
      (x3 := countWord σ I)).readWithPadding (UInt256.ofNat 160).toNat (UInt256.ofNat 64).toNat =
      pairPayload node' (u64ChunkWord (mask64 (countWord σ I))) := by
    rw [pairPayload_eq, ← evmChunk_eq]; exact rootPayload mem' node' _
  have hcall' : callViaEVM evm' (EVM.address precompile2) 0
      (pairPayload node' (u64ChunkWord (mask64 (countWord σ I)))) (z, evm'', out) false := by
    rw [precompile2_eq, ← hpay]; exact hcall
  -- Stele: `length_chunk := u64_chunk(uint64(count))`, then the final hash
  have hargs : evalExprs? config (fr L') evm' [.cast (.var "count") u64Ty] =
      .ok [.int (Int.ofNat (mask64 (countWord σ I)).toNat)] := by
    refine evalExprs?_singleton ?_
    rw [evalCastInt (.uint ⟨64, by decide⟩) (evalVar hL'.count), normalize_u64_word]
  obtain ⟨F, hchunkBody⟩ := u64ChunkBody config (fr L') evm' (mask64 (countWord σ I))
  have hchunk := internalCallFunctionReturn (name := "u64_chunk") (retVar := "length_chunk")
    (callee := u64ChunkFn) hargs rfl rfl hchunkBody
  have ha : evalExpr? config (fr (L'.insert "length_chunk"
      (.int (Int.ofNat (u64ChunkWord (mask64 (countWord σ I))).toNat)))) evm' (.var "node") =
      .ok (.int (Int.ofNat node'.toNat)) :=
    evalVar (by rw [get_ins_ne (by decide)]; exact hL'.node)
  have hb : evalExpr? config (fr (L'.insert "length_chunk"
      (.int (Int.ofNat (u64ChunkWord (mask64 (countWord σ I))).toNat)))) evm' (.var "length_chunk") =
      .ok (.int (Int.ofNat (u64ChunkWord (mask64 (countWord σ I))).toNat)) :=
    evalVar (store_get_self _ _ _)
  by_cases hok : z = true ∧ 32 ≤ out.size
  · obtain ⟨rfl, hlen⟩ := hok
    have hsha := shaPairCall_ok (ret := "root") rfl ha hb hcall' hlen
    have hret := ExecStmt.return (cfg := config) (evm := evm'')
      (stele := fr ((L'.insert "length_chunk"
        (.int (Int.ofNat (u64ChunkWord (mask64 (countWord σ I))).toNat))).insert "root"
        (shaDigest out)))
      (evalExprs?_singleton (evalVar (store_get_self _ _ _)))
    have hmem : 224 ≤ (feDepositBlocks.feDeposit_block_1991_memory (mem := mem') (x1 := node')
        (x3 := countWord σ I)).size :=
      toByteArray_write_size_ge_off_add32 _ _ 192 (lt_usize _ (by omega))
    have rret := hpost.2 rfl hlen
    have hload : memLoad (UInt256.ofNat 160) (callOutputMem
        (feDepositBlocks.feDeposit_block_1991_memory (mem := mem') (x1 := node')
          (x3 := countWord σ I)) out (UInt256.ofNat 160) (UInt256.ofNat 32)) = calldataWord out 0 :=
      callOutput_load _ out (UInt256.ofNat 160) hout hlen (by change 160 + 32 ≤ _; omega)
    rw [hload] at rret
    refine RDret.reEquivExecutionGen (cs := fr ((L'.insert "length_chunk"
        (.int (Int.ofNat (u64ChunkWord (mask64 (countWord σ I))).toNat))).insert "root"
        (shaDigest out))) hcode rret hd hdec ?_ hs''.accounts
      (returnEquiv_of_encode (uint256ReturnEncoding (calldataWord out 0)))
    rw [rootBody_eq]
    exact ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal hreq <| ExecBlock.consNormal hletCount <|
      ExecBlock.consNormal hletNode <| ExecBlock.consNormal hletSize <|
      ExecBlock.consNormal (ExecStmt.for hinit hloop) <| ExecBlock.consNormal hchunk <|
      ExecBlock.consNormal hsha <| ExecBlock.consReturn hret
  · have hsha := shaPairCall_revert (ret := "root") rfl ha hb hcall' hok
    have hbad : z = false ∨ out.size < 32 := by
      cases z
      · exact Or.inl rfl
      · exact Or.inr (Nat.lt_of_not_le (fun h => hok ⟨rfl, h⟩))
    refine RDrev.reEquivExecutionRevert hcode (hpost.1 hbad) hd hdec ?_
    rw [rootBody_eq]
    exact ExecFuncBody.execBlockRevert <|
      ExecBlock.consNormal hreq <| ExecBlock.consNormal hletCount <|
      ExecBlock.consNormal hletNode <| ExecBlock.consNormal hletSize <|
      ExecBlock.consNormal (ExecStmt.for hinit hloop) <| ExecBlock.consNormal hchunk <|
      ExecBlock.consRevert hsha

end FeProofs.Deposit
