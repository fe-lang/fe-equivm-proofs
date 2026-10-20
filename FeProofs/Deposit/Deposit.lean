import FeProofs.Deposit.DepositRest
import FeProofs.Deposit.DepositCalls

/-!
# FeDeposit `deposit(bytes,bytes,bytes,bytes32)`

Per-function proof: the front (`depositFront`: dispatcher arm, decode, value checks, statements
1–8) via `depositBody_of_rest`, then the hashing calls 1–3 (`calls123`) and the rest of the body
(`depositRest`: hashing calls 4–7, the event, the count update and the insertion loop).
Dispatcher arm entry: pc 154; reach lemma `feDepositReachDepositBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- `deposit(bytes,bytes,bytes,bytes32)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem feDepositDepositBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 64) (hsel : selIs I (feDepositSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I :=
  depositBody_of_calls123 hcode hsize hsmall hsel fun hok hargs hp rd => calls123 hok hargs hp rd

end FeProofs.Deposit
