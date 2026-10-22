import FeProofs.WETH9.Dispatch
import FeProofs.Common.Basic

/-!
# FeWETH9 `totalSupply()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 272; reach lemma `feWETH9ReachTotalSupplyBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- `totalSupply()`: the theorem `Correct.lean` routes selector 2 to. -/
theorem feWETH9TotalSupplyBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 2) rfl hsel
  have hd := feWETH9Dispatch_totalSupply hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachTotalSupplyBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd using [hwv]
  have rd := rd.selfbalance (by native_decide) (by simp)
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hret : evalExpr? config { contract := contract, locals := ∅ }
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.env .selfbalance) =
        .ok (.int (Int.ofNat (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)).toNat)) := by
    simp only [evalExpr?, envValue, initState, State.lookupAccount, Option.option, pure]
    cases σ.get? I.codeOwner <;> rfl
  exact RDret.reEquivExecutionSel hcode rd hd
    (show decodeCalldata [] [] I.calldata = some ∅ from decodeCalldata_empty_ok hsz)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hret)
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.WETH9
