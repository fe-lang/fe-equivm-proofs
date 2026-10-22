import FeProofs.WETH9.Dispatch

/-!
# FeWETH9 `balanceOf(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 523; reach lemma `feWETH9ReachBalanceOfBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem feWETH9BalanceOfBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 6) rfl hsel
  sorry

end FeProofs.WETH9
