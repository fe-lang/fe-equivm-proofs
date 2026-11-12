import Fe.EVM.Storage
import Fe.EVM.Refine

/-!
# FeCodeScalar model

Written by hand, in the shape the exporter prints.

```fe
pub contract FeCodeScalar {
    value: u256

    init(initial: u256) uses (mut value) { value = initial }

    recv FeCodeScalarMsg {
        Get -> u256 uses (value) { value }
    }
}
```

`value` is immutable: the deployed code is the runtime bytecode followed by its word.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.CodeScalar.Model

/-- `Get -> u256 uses (value) { value }`: the one immutable word, at the end of the code. -/
def get : FeM UInt256 := do cload (← immutableAt 1 0)

/-- `sol("get()")` -/
def getSelector : ByteArray := ⟨#[0x6d, 0x4c, 0xe6, 0x3c]⟩

/-- The constructor: reject call value and decode one word from the argument bytes.  `init`
    sets `value` to it, so the word is the bytes the deployed code ends with. -/
def init (args : ByteArray) : FeM ByteArray := do
  nonPayable
  if args.size < 32 then
    M.revert ByteArray.empty
  else
    return (uInt256OfByteArray (args.readBytes 0 32)).toByteArray

/-- The runtime entry.  The arm rejects call value and takes no arguments. -/
def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then
    M.revert ByteArray.empty
  else if getSelector == cd.extract 0 4 then
    nonPayable
    let result ← get
    return result.toByteArray
  else
    M.revert ByteArray.empty

def contract : ContractModel := { init := init, runtime := runtime, immutables := 32 }

end FeProofs.CodeScalar.Model
