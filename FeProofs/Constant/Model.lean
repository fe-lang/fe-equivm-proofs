import Fe.EVM.Refine

/-!
# FeConstant model

Written by hand, in the shape the exporter should print: one definition per `recv` arm and one
for the runtime entry.

```fe
pub contract FeConstant {
    recv FeConstantMsg {
        Answer -> u256 { 42 }
    }
}
```
-/

open Ethereum Fe Fe.EVM

namespace FeProofs.Constant.Model

/-- `Answer -> u256 { 42 }` -/
def answer : FeM UInt256 := pure ⟨42⟩

/-- `sol("answer()")` -/
def answerSelector : ByteArray := ⟨#[0x85, 0xbb, 0x7d, 0x69]⟩

/-- The runtime entry: match the selector, reject call value, run the arm, encode its result.
    Calldata with no selector, or with one no arm declares, reverts with no data. -/
def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then
    M.revert ByteArray.empty
  else if answerSelector == cd.extract 0 4 then
    nonPayable
    let result ← answer
    return result.toByteArray
  else
    M.revert ByteArray.empty

def contract : ContractModel := ⟨runtime⟩

end FeProofs.Constant.Model
