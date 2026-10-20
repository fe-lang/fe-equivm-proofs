import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.ApproveStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `approve(address,uint256)`

Arm entry pc 79: the call-value check (revert block 86), the two-word head check at pc 90, the
`spender` canonicality check (`SHR 160`) at pc 103, then block 113: the nested-mapping slot
`keccak256(spender ‖ keccak256(caller ‖ 1))`, the `SSTORE`, `LOG3 Approval` and the 32-byte
`true` return.  Under `STATICCALL` the `SSTORE` halts with a static-mode violation, matching the
Stele storage assignment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- The argument store `approve(address,uint256)` decodes. -/
abbrev approveLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "value" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))

/-- The Stele slot of `allowance[msg.sender][spender]`. -/
abbrev approveSlot (I : ExecutionEnv) : UInt256 :=
  approveMapSlot (calldataWord I.calldata 4) (approveMapSlot (UInt256.ofNat I.source.val) (UInt256.ofNat 1))

theorem feERC20ApproveDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some (approveLocals I) := by
  show decodeCalldata ["spender", "value"] [.elem .address, abiUInt256] I.calldata = _
  exact decodeCalldata_addr_uint256_ok hsz68 hbig hcanon

theorem feERC20ApproveDecode_none {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (h : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size ∨
      (68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
        ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)) :
    config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [.elem .address, abiUInt256] I.calldata = _
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact decodeCalldata_addr_uint256_none_short hsz4 h
  · exact decodeCalldata_addr_uint256_none_huge h
  · exact decodeCalldata_addr_uint256_none_noncanon h1 h2 h3

theorem approveLocals_spender (I : ExecutionEnv) :
    (approveLocals I).get? "spender" =
      some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) := by
  rw [approveLocals, store_get_ne _ _ (by decide), store_get_self]

theorem approveLocals_value (I : ExecutionEnv) :
    (approveLocals I).get? "value" = some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) := by
  rw [approveLocals, store_get_self]

theorem approveEval_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveLocals I } evm (.var "spender") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveLocals_spender]

theorem approveEval_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveLocals I } evm (.var "value") =
      .ok (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveLocals_value]

theorem approveRef_eval (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := approveLocals I } evm
      { base := "allowance", steps := [.mindex (.env .caller), .mindex (.var "spender")] } =
      .ok { base := "allowance", steps := [.mindex (.address evm.executionEnv.source),
        .mindex (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))] } := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, envValue, valueToKey?,
    approveEval_spender, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := approveLocals I } evm .storage
        { base := "allowance", steps := [.mindex (.env .caller), .mindex (.var "spender")] }
        (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) =
      .ok ({ contract := contract, locals := approveLocals I },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot I)
          (calldataWord I.calldata 36)) := by
  refine assignStorageRef_storage_scalar (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (hbase := by simp [approveLocals]) (her := approveRef_eval evm I)
    (hty := rfl) (hbackend := approveConfig_storageBackend)
    (hloc := approveAllowanceLoc _ _) (hleaf := Or.inl ⟨_, rfl⟩) ?_
  rw [keyValueToWord_address_of_canonical _ hcanon, keyValueToWord_address, hsrc]
  exact storageLocStore_uint256 evm _ _

/-- `approve(address,uint256)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem feERC20ApproveBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 0) rfl hsel
  have hd := feERC20Dispatch_approve hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachApproveBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feERC20Blocks.feERC20_block_79_taken (by simp) (by rw [hwv]; decide)
      (by jump_dest) rd
    simp only [feERC20Blocks.feERC20_block_79_taken_stack] at rd1
    by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨hlen, hhi⟩ := hok
      have rd2 := feERC20Blocks.feERC20_block_90_fallthrough (by simp)
        (solcDecodeLenCheckOk_4_64 hlen hhi hsize) rd1
      by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have rd3 := feERC20Blocks.feERC20_block_103_fallthrough (by simp)
          (approveShr160_eq_zero hcanon) rd2
        simp only [feERC20Blocks.feERC20_block_103_fallthrough_stack] at rd3
        let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hcv : evalExpr? config { contract := contract, locals := approveLocals I } evmS
            (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
          evalCallvalueEq_true (by simp only [evmS, initState]; exact hwv)
        have hval := approveEval_value evmS I
        have hassign := approveAssign evmS I (by simp only [evmS, initState]) hcanon
        by_cases hperm : I.perm = true
        · have rret := feERC20Blocks.feERC20_block_113 (by simp) hperm rd3
          rw [approvePair_keccak, approvePair_keccak, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl,
            toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rret
          have hbody : ExecTransitionBody config contract evmS (approveLocals I) approveTransition.body
              (.returned { contract := contract, locals := approveLocals I }
                (Stele.EVM.storageStore evmS evmS.executionEnv.codeOwner (approveSlot I)
                  (calldataWord I.calldata 36)) (some [(.bool true)])) := by
            refine ExecFuncBody.execBlockRet ?_
            refine ExecBlock.consNormal (ExecStmt.requireTrue hcv) ?_
            refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) hval hassign) ?_
            refine ExecBlock.consNormal (ExecStmt.emit (by simpa [evmS, initState] using hperm)
              (by simp [evalExprs?, approveEval_spender, approveEval_value, evalExpr?, envValue,
                EvalResult.bind, bind, pure]; rfl)) ?_
            exact ExecBlock.consReturn
              (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))
          exact rret.reEquivExecutionGen hcode hd (feERC20ApproveDecode_ok hlen hhi hcanon) hbody
            (by rw [storageStore_accountMap]; rfl)
            (returnEquiv_of_encode boolTrueReturnEncoding)
        · have hpf : I.perm = false := by simpa using hperm
          let r0 := rd3
          have r1 := r0.caller (by native_decide) (by evm_ov)
          have r2 := r1.dup1 (by native_decide) (by evm_ov)
          have r3 := r2.push0 (by native_decide) (by evm_ov)
          have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
          have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
          have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
          have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
          have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
          have r9 := r8.push0 (by native_decide) (by evm_ov)
          have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
          have r11 := r10.dup3 (by native_decide) (by evm_ov)
          have r12 := r11.push0 (by native_decide) (by evm_ov)
          have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
          have r14 := r13.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
          have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
          have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
          have r17 := r16.push0 (by native_decide) (by evm_ov)
          have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
          have r19 := r18.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
          have r20 := r19.calldataload (by native_decide) (by evm_ov)
          have r21 := r20.dup1 (by native_decide) (by evm_ov)
          have r22 := r21.swap2 (by native_decide) (by evm_ov)
          have rs := r22.sstoreStatic hpf (by native_decide) (by evm_ov)
          exact RDstatic.reEquivStaticHalt hcode rs hd (feERC20ApproveDecode_ok hlen hhi hcanon)
            (ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
              (ExecBlock.consStatic (ExecStmt.assignStatic hval hassign
                (by show I.perm = false; exact hpf)))))
      · have rd3 := feERC20Blocks.feERC20_block_103_taken (by simp)
          (approveShr160_ne_zero (Nat.le_of_not_lt hcanon)) (by jump_dest) rd2
        exact RDrev.reEquivDecodingFailed hcode
          (feERC20Blocks.feERC20_block_86 (by simp [feERC20Blocks.feERC20_block_103_taken_stack]) rd3)
          hd (feERC20ApproveDecode_none hsz (Or.inr (Or.inr ⟨hlen, hhi, hcanon⟩)))
    · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 64) = ⟨1⟩ := by
        rcases hbad with h | h
        · exact solcDecodeLenCheckShort_4_64 hsz h hsize
        · exact solcDecodeLenCheckHuge_4_64 h hsize
      have rd2 := feERC20Blocks.feERC20_block_90_taken (by simp)
        (by rw [hslt]; decide) (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode (feERC20Blocks.feERC20_block_86 (by simp) rd2)
        hd (feERC20ApproveDecode_none hsz (by omega))
  · have rd1 := feERC20Blocks.feERC20_block_79_fallthrough (by simp)
      (isZero_eq_zero_of_ne hwv) rd
    exact RDrev.reEquivDispatchedRevert hcode
      (feERC20Blocks.feERC20_block_86 (by simp [feERC20Blocks.feERC20_block_79_fallthrough_stack]) rd1)
      hd fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.ERC20
