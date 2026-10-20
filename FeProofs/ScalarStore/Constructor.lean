import FeProofs.ScalarStore.Storage
import FeProofs.ScalarStore.CreationBlocks_001
import FeProofs.ScalarStore.CreationBlocks_002
import FeProofs.Common.CtorUInt256
import Reasoning.VyperCalls

/-!
# FeScalarStore constructor correctness

The initcode rejects call value, requires at least 140 bytes of code (the initcode alone), takes
`max(mload(0x40), 0x60) = 0x60` as its scratch pointer, copies the argument bytes there, requires
at least one word of them, stores that word in slot 0, and returns the 80-byte runtime.  Under the
canonical deployment the argument bytes are exactly the encoded `uint256`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs.ScalarStore

/-- The ABI-encoded constructor argument. -/
abbrev ctorTail (w : UInt256) : ByteArray := (EVM.Word.toBytesBE w).toByteArray

theorem feScalarStoreCreation_size : feScalarStoreCreationBytecode.size = 140 := by native_decide

theorem ctorCode_size (w : UInt256) : (feScalarStoreCreationBytecode ++ ctorTail w).size = 172 := by
  rw [ByteArray.size_append, feScalarStoreCreation_size, word_toBytesBE_toByteArray_size]

/-- Memory after `CODECOPY(0x60, 140, 32)` into empty memory. -/
abbrev ctorArgMem (w : UInt256) : ByteArray :=
  (feScalarStoreCreationBytecode ++ ctorTail w).write (UInt256.ofNat 140).toNat ByteArray.empty
    (UInt256.ofNat 96).toNat (UInt256.sub (UInt256.ofNat 172) (UInt256.ofNat 140)).toNat

theorem ctorArgMem_eq (w : UInt256) :
    ctorArgMem w = ByteArray.zeroes 96 ++ ctorTail w := by
  unfold ctorArgMem
  rw [show (UInt256.ofNat 140).toNat = 140 from rfl, show (UInt256.ofNat 96).toNat = 96 from rfl,
    show (UInt256.sub (UInt256.ofNat 172) (UInt256.ofNat 140)).toNat = 32 by decide,
    write_from_gap_eq _ _ 140 96 32 (by decide) (by have := ctorCode_size w; omega)
      (by simp) (by simp only [ByteArray.size_empty]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size),
    extract_append_right' _ _ 140 (140 + 32) feScalarStoreCreation_size.symm
      (by rw [feScalarStoreCreation_size, word_toBytesBE_toByteArray_size])]
  simp [ByteArray.empty_append]

theorem ctorArgMem_load (w : UInt256) : memLoad (UInt256.ofNat 96) (ctorArgMem w) = w := by
  have hsz : (ctorArgMem w).size = 128 := by
    rw [ctorArgMem_eq, ByteArray.size_append, ByteArray_zeroes_size, word_toBytesBE_toByteArray_size]
  refine memLoad_of_read _ 96 w (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 96 (by omega), ctorArgMem_eq,
    extract_append_right' _ _ 96 (96 + 32) (by rw [ByteArray_zeroes_size])
      (by rw [ByteArray_zeroes_size, word_toBytesBE_toByteArray_size]),
    ctorTail, word_toBytesBE_toByteArray_eq_toByteArray]

theorem ctorRuntime_read (w : UInt256) :
    ((feScalarStoreCreationBytecode ++ ctorTail w).write (UInt256.ofNat 60).toNat (ctorArgMem w)
      (⟨0⟩ : UInt256).toNat (UInt256.ofNat 80).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 80).toNat = feScalarStoreBytecode := by
  rw [show (UInt256.ofNat 60).toNat = 60 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 80).toNat = 80 from rfl,
    write0_read_back_from_gen _ _ 60 80 (by decide) (by have := ctorCode_size w; omega) (by decide),
    extract_append_left _ _ _ _ (by rw [feScalarStoreCreation_size])]
  native_decide

set_option maxHeartbeats 1000000 in
theorem feScalarStoreCtorRet {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (w : UInt256) (hcode : I.code = feScalarStoreCreationBytecode ++ ctorTail w)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    RDret (feScalarStoreCreationBytecode ++ ctorTail w) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ w) feScalarStoreBytecode := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 using [hwv, ctorCode_size w, (by native_decide)]
  simp only [ctorCode_size] at rd0
  rwa [ctorArgMem_load, ctorRuntime_read] at rd0

theorem feScalarStoreCtorRev {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {tail : ByteArray} (hcode : I.code = feScalarStoreCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (feScalarStoreCreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 using [isZero_eq_zero_of_ne hwv]
  exact rd0

/-- The constructor's argument store. -/
abbrev ctorLocals (i : Int) : Store :=
  Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) [.int i])

theorem ctorLocals_initial (i : Int) : (ctorLocals i).get? "initial" = some (.int i) := by
  simp [ctorLocals, contract, Syntax.contractSyntax]

theorem ctorLocals_stored (i : Int) : (ctorLocals i).get? "stored" = none := by
  simp [ctorLocals, contract, Syntax.contractSyntax]

theorem feScalarStoreCtorBody_ok (evm : EVM.State) (i : Int) (h0 : 0 ≤ i)
    (hlt : i < Int.ofNat (EVM.twoPow 256))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (ctorLocals i) contract.ctor.body
      (.returned { contract := contract, locals := ctorLocals i }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (EVM.word i.toNat)) none) := by
  have hval : evalExpr? config { contract := contract, locals := ctorLocals i } evm (.var "initial") =
      .ok (.int (Int.ofNat (EVM.word i.toNat).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((ctorLocals i).get? "initial") = _
    rw [ctorLocals_initial, constructorUInt256Word_toNat i h0 hlt]
    simp [EvalResult.ofOption, Int.toNat_of_nonneg h0]
  exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue
    (evalCallvalueEq_true hwv)) (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm)
      hval (stored_write (ctorLocals_stored i) _)) ExecBlock.nil))

theorem feScalarStoreConstructorCorrect :
    typedConstructorRefinement config feScalarStoreCreationBytecode contract
      (fun _ => feScalarStoreBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  obtain ⟨i, rfl, h0, hlt, hd⟩ := FeProofs.uint256CtorDeployment_shape hdeploy
  rw [hd] at hcode
  have hexec : ∀ {res}, ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (ctorLocals i) contract.ctor.body res → steleCtorExec config contract [.int i] σ σ₀ g A I res :=
    fun hbody => steleCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (argsStore := ctorLocals i) rfl rfl rfl hbody
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases feScalarStoreCtorRet (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A)
        (EVM.word i.toNat) hcode hwv hperm with hoog | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas (Xi_error_of_X (g := g) (by
        rw [← hcode] at hoog
        simpa [initState, Sat256.ofUInt256] using hoog))
    · have hxi := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX
        simpa [initState, Sat256.ofUInt256] using hX)
      rw [hacc] at hxi
      exact typedConstructorRefinementFor.execution hxi
        (hexec (feScalarStoreCtorBody_ok _ i h0 hlt hwv hperm))
        (ctorResultEquiv.success rfl rfl (by rw [storageStore_accountMap]; rfl) rfl)
  · rcases (feScalarStoreCtorRev (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A)
        hcode hwv).xiResult hcode with hoog | ⟨g', o, hrev⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
    · exact typedConstructorRefinementFor.execution (by simpa using hrev)
        (hexec (bodyReverts_nonPayable hwv)) (ctorResultEquiv.revert rfl rfl)

end FeProofs.ScalarStore
