import FeProofs.Deposit.CtorLoop

/-!
# FeDeposit constructor correctness

The initcode rejects call value, runs the `zero_hashes` loop (`CtorLoop.lean`), and returns the
2307-byte runtime with `CODECOPY(0, 83, 2307)`.  The Stele constructor is
`require(msg.value == 0)` followed by the same `for` loop.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

theorem ctorCode_eq : ctorCode = feDepositCreationBytecode := by
  show feDepositCreationBytecode ++ ByteArray.empty = _
  rw [ByteArray.append_empty]

/-- The final `CODECOPY(0, 83, 2307)` reads back as the runtime, whatever memory held. -/
theorem ctorRuntime_read (mem : ByteArray) :
    (feDepositCreationBytecode.write (UInt256.ofNat 83).toNat mem (⟨0⟩ : UInt256).toNat
        (UInt256.ofNat 2307).toNat).readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat 2307).toNat = feDepositBytecode := by
  rw [show (UInt256.ofNat 83).toNat = 83 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 2307).toNat = 2307 from rfl,
    write0_read_back_from_gen _ _ 83 2307 (by decide) (by native_decide) (by decide)]
  native_decide

theorem feDepositConstructorCorrect :
    typedConstructorRefinement config feDepositCreationBytecode contract
      (fun _ => feDepositBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  have hlen := emptyCtorDeployment_args_length (cfg := config) rfl rfl hdeploy
  rw [show contract.ctor.params = [] from rfl] at hlen
  have hargs : args = [] := List.length_eq_zero_iff.mp hlen
  subst hargs
  rw [emptyCtorDeployment_eq_initcode (cfg := config) rfl rfl hdeploy] at hcode
  have hcode' : I.code = ctorCode := by rw [ctorCode_eq]; exact hcode
  have rd0 := RD.initState (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode'
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hwv' : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue = ⟨0⟩ := hwv
    rd_run rd0 to 5 using [hwv]
    have rd5' : RD ctorCode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 5) [UInt256.ofNat 0] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ _ _ :=
      rd0
    have hinit : ExecBlock config { contract := contract, locals := ∅ }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ctorInit
        (.ok { contract := contract, locals := (∅ : Store).insert "height" (.int 0) }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
      ExecBlock.consNormal (ExecStmt.letDecl (evalLit 0)) ExecBlock.nil
    rcases ctorLoop hperm 31 0 rfl (L := (∅ : Store).insert "height" (.int 0))
        (store_get_self _ _ _) (by simp) rd5' SourceState.init with
      ⟨hrev, hloop⟩ | ⟨σf, evmf, Lf, mem', rdata', aw', k', C', hsf, rd71, hloop⟩
    · rw [ctorCode_eq] at hrev
      refine RDrev.constructorRefinementEmptyParams hrev hcode rfl ?_
      rw [ctorBody_eq]
      exact ExecFuncBody.execBlockRevert <|
        ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) <|
          ExecBlock.consRevert (ExecStmt.for hinit hloop)
    · rd_step rd71
      rw [ByteArray.append_empty, ctorRuntime_read] at rd71
      have hbody : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          contract.ctor.body (.returned { contract := contract, locals := Lf } evmf none) := by
        rw [ctorBody_eq]
        exact ExecFuncBody.execBlockOK <|
          ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) <|
            ExecBlock.consNormal (ExecStmt.for hinit hloop) ExecBlock.nil
      exact RDret.constructorRefinementEmptyParams rd71 hcode rfl hbody hsf.accounts
  · rd_run rd0 using [hwv]
    rw [ByteArray.append_empty] at rd0
    refine RDrev.constructorRefinementEmptyParams rd0 hcode rfl ?_
    rw [ctorBody_eq]
    exact bodyReverts_nonPayable hwv

end FeProofs.Deposit
