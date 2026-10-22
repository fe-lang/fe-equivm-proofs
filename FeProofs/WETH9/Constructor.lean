import FeProofs.WETH9.Common

/-!
# FeWETH9 constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

theorem feWETH9ConstructorCorrect :
    typedConstructorRefinement config feWETH9CreationBytecode contract (fun _ => feWETH9Bytecode) := by
  sorry

end FeProofs.WETH9
