import FeProofs.WETH9.CtorStore

/-!
# FeWETH9 constructor correctness

Creation-code equivalence for any initial storage: the initcode trace (`CtorTrace.lean`: the
call-value check, `store` of `name` and `symbol` with their old-word clearing loops, the `decimals`
byte and the runtime return) against the Stele constructor body (`CtorStore.lean`).  A `name` or
`symbol` head whose length contradicts its flag reverts on both sides; otherwise both sides leave
the same account map (`steleDecimals_accountMap`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

open Ctor

theorem feWETH9ConstructorCorrect :
    typedConstructorRefinement config feWETH9CreationBytecode contract (fun _ => feWETH9Bytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  have hlen := emptyCtorDeployment_args_length (cfg := config) rfl rfl hdeploy
  rw [show contract.ctor.params = [] from rfl] at hlen
  obtain rfl : args = [] := List.length_eq_zero_iff.mp hlen
  rw [emptyCtorDeployment_eq_initcode (cfg := config) rfl rfl hdeploy] at hcode
  have hcode' : I.code = ctorCode := by rw [ctorCode, ByteArray.append_empty]; exact hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · obtain ⟨hbad0, hok0⟩ := feWETH9CtorEvm (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      hcode' hwv hperm
    by_cases hb0 : strHeadBad (solcSlotWord σ I ⟨0⟩)
    · exact RDrev.constructorRefinementEmptyParams (hbad0 hb0) hcode' rfl
        (ctorBody_nameRevert hwv hb0)
    obtain ⟨hbad1, hok1⟩ := hok0 hb0
    have hS1 : Stele.EVM.storageLoad (steleName (initState σ σ₀ (Sat256.ofUInt256 g) A I))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨1⟩ =
          solcSlotWord (nameMap σ I) I ⟨1⟩ := by
      rw [storageLoad_eq_solcSlotWord, steleName, steleStrWrite_accountMap _ _ (Or.inl rfl)]
      rfl
    by_cases hb1 : strHeadBad (solcSlotWord (nameMap σ I) I ⟨1⟩)
    · exact RDrev.constructorRefinementEmptyParams (hbad1 hb1) hcode' rfl
        (ctorBody_symbolRevert hwv hperm hb0 (by rw [hS1]; exact hb1))
    · exact RDret.constructorRefinementEmptyParams (hok1 hb1) hcode' rfl
        (ctorBody_ok hwv hperm hb0 (by rw [hS1]; exact hb1))
        steleDecimals_accountMap.symm
  · refine RDrev.constructorRefinementEmptyParams (feWETH9CtorRev hcode' hwv) hcode' rfl ?_
    rw [ctorBody_eq]
    exact bodyReverts_nonPayable hwv

end FeProofs.WETH9
