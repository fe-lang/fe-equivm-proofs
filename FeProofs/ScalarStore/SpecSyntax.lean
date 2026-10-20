import Stele.Notation

/-!
# FeScalarStore surface spec

One `uint256` field in slot 0, initialized by the constructor; `set(uint256)` overwrites it and
`get()` returns it.  Fe rejects call value on every entry point, including the constructor.
Transitions are listed in the dispatcher's compare order.
-/

open Stele Stele.Notation

namespace FeProofs.ScalarStore.Syntax

def contractSyntax : ContractDecl := solidity% contract FeScalarStore {
  uint256 stored;

  constructor(uint256 initial) {
    stored = initial;
  }

  function set(uint256 value) external {
    stored = value;
  }

  function get() external returns (uint256) {
    return stored;
  }
}

end FeProofs.ScalarStore.Syntax
