import Reasoning.Constructor

/-!
# Fe constructor glue

Fe constructors reject call value before running their body.  A constructor without parameters
or statements therefore has the Stele body `require(msg.value == 0)`, and its initcode either
reverts (non-zero call value) or returns the runtime code without touching storage.

-- LIBRARY CANDIDATE: `Reasoning/Constructor.lean`, beside `emptyConstructorCorrect_of_RDret`
-- (the non-payable twin of the payable empty-constructor wrapper).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Common

/-- An empty non-payable constructor refines its Stele spec when the initcode returns the
    runtime code under zero call value (preserving the accounts) and reverts otherwise. -/
theorem nonpayableEmptyConstructorCorrect
    {cfg : Config} {contract : ContractDecl} {initcode runtimeCode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [.require (.binary .eq (.env .callvalue) (.intLit 0))])
    (hret : ∀ {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256},
      I.code = initcode → I.weiValue = ⟨0⟩ →
      RDret initcode g (initState σ σ₀ g A I) σ runtimeCode)
    (hrev : ∀ {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256},
      I.code = initcode → I.weiValue ≠ ⟨0⟩ →
      RDrev initcode g (initState σ σ₀ g A I))
    (himm : contract.immutables = [] := by rfl) :
    typedConstructorRefinement cfg initcode contract (fun _ => runtimeCode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata _hperm
  have hlen := emptyCtorDeployment_args_length hself hparams hdeploy
  rw [hparams] at hlen
  have hargs : args = [] := List.length_eq_zero_iff.mp hlen
  subst hargs
  rw [emptyCtorDeployment_eq_initcode hself hparams hdeploy] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hb : ExecTransitionBody cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        contract.ctor.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) none) := by
      rw [hbody]
      exact ExecFuncBody.execBlockOK <|
        ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
          simp only [initState]; exact hwv))) ExecBlock.nil
    exact (hret (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode hwv)
      |>.constructorRefinementEmptyParams hcode hparams hb rfl himm
  · refine (hrev (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode hwv)
      |>.constructorRefinementEmptyParams hcode hparams ?_ himm
    rw [hbody]
    exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.Common
