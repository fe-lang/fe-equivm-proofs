import FeProofs.WETH9.Dispatch
import FeProofs.WETH9.MapStorage
import FeProofs.Common.Basic

/-!
# FeWETH9 `deposit()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 640; reach lemma `feWETH9ReachDepositBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- The slot of `balanceOf[msg.sender]`. -/
abbrev callerBalanceSlot (I : ExecutionEnv) : UInt256 := mapSlot (UInt256.ofNat I.source.val) ⟨3⟩

/-- `balanceOf[msg.sender] += msg.value`, the body of `deposit()` and of the fallback: with write
permission it stores the wrapping sum, and in static mode the store halts. -/
theorem depositBody {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    (ht : t.body = depositTransition.body) :
    (I.perm = true → ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      t.body (.returned { contract := contract, locals := ∅ }
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
          (callerBalanceSlot I)
          (UInt256.add (solcSlotWordAt (callerBalanceSlot I) σ I) I.weiValue)) none)) ∧
    (I.perm = false → ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      t.body .staticViolation) := by
  rw [ht]
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hread := balanceOf_read (L := ∅) (evm := evm) (by simp)
    (Reasoning.VyperDispatch.evalExpr_caller evm)
  rw [keyValueToWord_address, storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  have heval : evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .add (.storage { base := "balanceOf", steps := [.mindex (.env .caller)] })
        (.env .callvalue)) =
      .ok (.int (Int.ofNat (solcSlotWordAt (callerBalanceSlot I) σ I).toNat +
        Int.ofNat I.weiValue.toNat)) := by
    simp only [evalExpr?, hread, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
    rfl
  have hassign := balanceOf_assign_int (L := ∅) (evm := evm) (by simp)
    (Reasoning.VyperDispatch.evalExpr_caller evm)
    (Int.ofNat (solcSlotWordAt (callerBalanceSlot I) σ I).toNat + Int.ofNat I.weiValue.toNat)
  rw [keyValueToWord_address, wordOfInt_add_words] at hassign
  constructor
  · intro hperm
    exact ExecFuncBody.execBlockOK (assignStorageBlock heval hassign hperm)
  · intro hperm
    exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
      (ExecStmt.assignStatic heval hassign (by simpa [evm, initState] using hperm)))

/-- `deposit()`: the theorem `Correct.lean` routes selector 9 to. -/
theorem feWETH9DepositBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 9) rfl hsel
  have hd := feWETH9Dispatch_deposit hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachDepositBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  have hdec : config.externalABI.decodeCalldata? (depositTransition.params.map Param.name)
      (transitionSignature depositTransition).paramTypes I.calldata = some ∅ :=
    show decodeCalldata [] [] I.calldata = some ∅ from decodeCalldata_empty_ok hsz
  by_cases hperm : I.perm = true
  · rd_run rd
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide), byteArray_readWithPadding_zero] at rd
    refine RDret.reEquivExecutionGenSel hcode rd hd hdec ((depositBody rfl).1 hperm) ?_
      (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))
    rw [storageStore_accountMap, u256_add_comm]
    rfl
  have hpf : I.perm = false := by simpa using hperm
  rd_run rd
  exact RDstatic.reEquivStaticHaltSel hcode rd hd hdec ((depositBody rfl).2 hpf)

/-- From the fallback entry (pc 723), reached with the selector word or nothing on the stack:
`balanceOf[msg.sender] += msg.value`, then `RETURN(0, 0)`. -/
theorem feWETH9FallbackFrom723 {σ σ₀ A I} {g : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = feWETH9Bytecode) (hR : R.length ≤ 1)
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 723) R ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ k C)
    (hnosel : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hnorecv : receiveDispatchMsg contract I.calldata = none := by
    simp [receiveDispatchMsg, contract, Syntax.contractSyntax]
  by_cases hperm : I.perm = true
  · rd_run rd using [hR]
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide), byteArray_readWithPadding_zero] at rd
    refine RDret.reEquivFallback hcode rd hnosel hnorecv rfl rfl rfl ((depositBody rfl).1 hperm) ?_
      (.abi (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide)))
    rw [storageStore_accountMap, u256_add_comm]
    rfl
  have hpf : I.perm = false := by simpa using hperm
  rd_run rd using [hR]
  exact RDstatic.reEquivFallbackStaticHalt hcode rd hnosel hnorecv rfl rfl rfl
    ((depositBody rfl).2 hpf)

/-- Calldata shorter than a selector, or matching none, runs the payable fallback. -/
theorem feWETH9FallbackBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 11 → (feWETH9SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hnosel : selectorDispatchMsg contract I.calldata = none := by
    rw [selectorDispatchMsg_eq_dispatchList, transitions_eq]
    refine dispatchList_none_of_all_ne ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nameSelectorOf]; exact hnm 0 (by omega)
    · rw [approveSelectorOf]; exact hnm 1 (by omega)
    · rw [totalSupplySelectorOf]; exact hnm 2 (by omega)
    · rw [transferFromSelectorOf]; exact hnm 3 (by omega)
    · rw [withdrawSelectorOf]; exact hnm 4 (by omega)
    · rw [decimalsSelectorOf]; exact hnm 5 (by omega)
    · rw [balanceOfSelectorOf]; exact hnm 6 (by omega)
    · rw [symbolSelectorOf]; exact hnm 7 (by omega)
    · rw [transferSelectorOf]; exact hnm 8 (by omega)
    · rw [depositSelectorOf]; exact hnm 9 (by omega)
    · rw [allowanceSelectorOf]; exact hnm 10 (by omega)
  have rd := RD.initState (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  by_cases hsz : 4 ≤ I.calldata.size
  · have hc := lt_four_eq_zero_of_ge hsz hsize
    have n0 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨117300739⟩ = ⟨0⟩ := by
      have e := nameEvmSelector hsz
      simp only [hnm 0 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n1 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨157198259⟩ = ⟨0⟩ := by
      have e := approveEvmSelector hsz
      simp only [hnm 1 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n2 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨404098525⟩ = ⟨0⟩ := by
      have e := totalSupplyEvmSelector hsz
      simp only [hnm 2 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n3 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨599290589⟩ = ⟨0⟩ := by
      have e := transferFromEvmSelector hsz
      simp only [hnm 3 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n4 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨773487949⟩ = ⟨0⟩ := by
      have e := withdrawEvmSelector hsz
      simp only [hnm 4 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n5 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨826074471⟩ = ⟨0⟩ := by
      have e := decimalsEvmSelector hsz
      simp only [hnm 5 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n6 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨1889567281⟩ = ⟨0⟩ := by
      have e := balanceOfEvmSelector hsz
      simp only [hnm 6 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n7 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨2514000705⟩ = ⟨0⟩ := by
      have e := symbolEvmSelector hsz
      simp only [hnm 7 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n8 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨2835717307⟩ = ⟨0⟩ := by
      have e := transferEvmSelector hsz
      simp only [hnm 8 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n9 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨3504541104⟩ = ⟨0⟩ := by
      have e := depositEvmSelector hsz
      simp only [hnm 9 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    have n10 : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) ⟨3714247998⟩ = ⟨0⟩ := by
      have e := allowanceEvmSelector hsz
      simp only [hnm 10 (by omega), Bool.false_eq_true, if_false] at e
      rw [uInt256_eq_comm] at e
      exact e
    rd_run rd to 723 using [hc, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]
    exact feWETH9FallbackFrom723 hcode (by simp) rd hnosel
  · rd_run rd to 723 using [lt_four_ne_zero_of_lt (by omega)]
    exact feWETH9FallbackFrom723 hcode (by simp) rd hnosel

end FeProofs.WETH9
