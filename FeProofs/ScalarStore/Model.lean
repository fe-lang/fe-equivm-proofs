import Fe.EVM.Refine

/-!
# FeScalarStore model

Written by hand, in the shape the exporter should print.

```fe
pub contract FeScalarStore {
    mut stored: u256

    init(initial: u256) uses (mut stored) { stored = initial }

    recv FeScalarStoreMsg {
        Get -> u256 uses (stored) { stored }
        Set { value } uses (mut stored) { stored = value }
    }
}
```
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ScalarStore.Model

/-- The storage root of the contract field `stored`. -/
def storedSlot : UInt256 := ⟨0⟩

/-- `init(initial: u256) uses (mut stored) { stored = initial }` -/
def initBody (initial : UInt256) : FeM Unit := sstore storedSlot initial

/-- `Get -> u256 uses (stored) { stored }` -/
def get : FeM UInt256 := sload storedSlot

/-- `Set { value } uses (mut stored) { stored = value }` -/
def set (value : UInt256) : FeM Unit := sstore storedSlot value

/-- `sol("set(uint256)")` -/
def setSelector : ByteArray := ⟨#[0x60, 0xfe, 0x47, 0xb1]⟩

/-- `sol("get()")` -/
def getSelector : ByteArray := ⟨#[0x6d, 0x4c, 0xe6, 0x3c]⟩

/-- The constructor: reject call value, decode one word from the argument bytes, run `init`. -/
def init (args : ByteArray) : FeM Unit := do
  nonPayable
  if args.size < 32 then
    M.revert ByteArray.empty
  else
    initBody (uInt256OfByteArray (args.readBytes 0 32))

/-- The runtime entry.  Each arm rejects call value, then checks that the calldata holds its
    argument words, with Solidity's signed length check. -/
def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then
    M.revert ByteArray.empty
  else if setSelector == cd.extract 0 4 then
    nonPayable
    if BadHead cd 1 then
      M.revert ByteArray.empty
    else
      set (uInt256OfByteArray (cd.readBytes 4 32))
      return ByteArray.empty
  else if getSelector == cd.extract 0 4 then
    nonPayable
    let result ← get
    return result.toByteArray
  else
    M.revert ByteArray.empty

def contract : ContractModel := ⟨init, runtime⟩

end FeProofs.ScalarStore.Model
