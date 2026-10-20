import FeProofs.ERC20.CtorBody

/-!
# FeERC20 constructor correctness

Creation-code equivalence: the initcode trace (`CtorTrace.lean`: argument decode, the
`balanceOf[msg.sender]` and `totalSupply` stores, the runtime return) against the Stele
constructor body (`CtorBody.lean`), under the canonical `uint256` deployment.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

theorem feERC20ConstructorCorrect :
    typedConstructorRefinement config feERC20CreationBytecode contract
      (fun _ => feERC20Bytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  obtain ⟨i, rfl, h0, hlt, hd⟩ := FeProofs.uint256CtorDeployment_shape hdeploy
  rw [hd] at hcode
  have hexec : ∀ {res}, ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (ctorLocals i) contract.ctor.body res → steleCtorExec config contract [.int i] σ σ₀ g A I res :=
    fun hbody => steleCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (argsStore := ctorLocals i) rfl rfl rfl hbody
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases feERC20CtorRet (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A)
        (EVM.word i.toNat) hcode hwv hperm with hoog | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas (Xi_error_of_X (g := g) (by
        rw [← hcode] at hoog
        simpa [initState, Sat256.ofUInt256] using hoog))
    · have hxi := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX
        simpa [initState, Sat256.ofUInt256] using hX)
      rw [hacc] at hxi
      exact typedConstructorRefinementFor.execution hxi
        (hexec (feERC20CtorBody_ok _ i h0 hlt hwv hperm))
        (ctorResultEquiv.success rfl rfl (by
          rw [ctorKey_slot, ← keyValueToWord_address]
          simp only [ctorPost, storageStore_accountMap]
          rfl) rfl)
  · rcases (feERC20CtorRev (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A)
        hcode hwv).xiResult hcode with hoog | ⟨g', o, hrev⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
    · exact typedConstructorRefinementFor.execution (by simpa using hrev)
        (hexec (bodyReverts_nonPayable hwv)) (ctorResultEquiv.revert rfl rfl)

end FeProofs.ERC20
