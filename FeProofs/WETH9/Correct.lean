import FeProofs.WETH9.Constructor
import FeProofs.WETH9.Name
import FeProofs.WETH9.Approve
import FeProofs.WETH9.TotalSupply
import FeProofs.WETH9.TransferFrom
import FeProofs.WETH9.Withdraw
import FeProofs.WETH9.Decimals
import FeProofs.WETH9.BalanceOf
import FeProofs.WETH9.Symbol
import FeProofs.WETH9.Transfer
import FeProofs.WETH9.Deposit
import FeProofs.WETH9.Allowance
import Stele.Refine

/-!
# FeWETH9 correctness capstone

The selector case split routes each selector to its per-function `…Body` lemma; calldata that
matches no selector, or is shorter than one, runs the payable fallback (`Deposit.lean`).  The
runtime refinement holds under `feWETH9StorageWF` (`StringGetter.lean`): on a zero-value `name()` or
`symbol()` call, the stored string's ABI encoding is shorter than `2^64` bytes, as it is in any
deployed FeWETH9.  The constructor, which holds for any initial storage, is packaged into the
whole-contract refinement.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

theorem feWETH9NoSelectorMatches {I : ExecutionEnv}
    (h0 : ¬ selIs I (feWETH9SelBytes 0)) (h1 : ¬ selIs I (feWETH9SelBytes 1)) (h2 : ¬ selIs I (feWETH9SelBytes 2)) (h3 : ¬ selIs I (feWETH9SelBytes 3)) (h4 : ¬ selIs I (feWETH9SelBytes 4)) (h5 : ¬ selIs I (feWETH9SelBytes 5)) (h6 : ¬ selIs I (feWETH9SelBytes 6)) (h7 : ¬ selIs I (feWETH9SelBytes 7)) (h8 : ¬ selIs I (feWETH9SelBytes 8)) (h9 : ¬ selIs I (feWETH9SelBytes 9)) (h10 : ¬ selIs I (feWETH9SelBytes 10)) :
    ∀ i, i < 11 → (feWETH9SelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs] using h0
  · simpa [selIs] using h1
  · simpa [selIs] using h2
  · simpa [selIs] using h3
  · simpa [selIs] using h4
  · simpa [selIs] using h5
  · simpa [selIs] using h6
  · simpa [selIs] using h7
  · simpa [selIs] using h8
  · simpa [selIs] using h9
  · simpa [selIs] using h10

theorem feWETH9Correct :
    runtimeRefinementWithWF feWETH9StorageWF noGasBound config feWETH9Bytecode contract := by
  refine ⟨fun σ σ₀ g A I hcode hsize hwf _ ↦ ?_⟩
  by_cases h0 : selIs I (feWETH9SelBytes 0)
  · exact feWETH9NameBody hcode hsize h0 hwf
  · by_cases h1 : selIs I (feWETH9SelBytes 1)
    · exact feWETH9ApproveBody hcode hsize h1
    · by_cases h2 : selIs I (feWETH9SelBytes 2)
      · exact feWETH9TotalSupplyBody hcode hsize h2
      · by_cases h3 : selIs I (feWETH9SelBytes 3)
        · exact feWETH9TransferFromBody hcode hsize h3
        · by_cases h4 : selIs I (feWETH9SelBytes 4)
          · exact feWETH9WithdrawBody hcode hsize h4
          · by_cases h5 : selIs I (feWETH9SelBytes 5)
            · exact feWETH9DecimalsBody hcode hsize h5
            · by_cases h6 : selIs I (feWETH9SelBytes 6)
              · exact feWETH9BalanceOfBody hcode hsize h6
              · by_cases h7 : selIs I (feWETH9SelBytes 7)
                · exact feWETH9SymbolBody hcode hsize h7 hwf
                · by_cases h8 : selIs I (feWETH9SelBytes 8)
                  · exact feWETH9TransferBody hcode hsize h8
                  · by_cases h9 : selIs I (feWETH9SelBytes 9)
                    · exact feWETH9DepositBody hcode hsize h9
                    · by_cases h10 : selIs I (feWETH9SelBytes 10)
                      · exact feWETH9AllowanceBody hcode hsize h10
                      · exact feWETH9FallbackBody hcode hsize (feWETH9NoSelectorMatches h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

theorem feWETH9ContractCorrect :
    contractRefinementWF feWETH9StorageWF noGasBound config feWETH9CreationBytecode contract :=
  contractRefinementWF.of_constant feWETH9ConstructorCorrect feWETH9Correct

end FeProofs.WETH9
