import Stele.Notation

/-!
# FeIdentity surface spec

`identity(uint256)` returns its argument.  Fe rejects call value on every entry point, including
the constructor, so both carry the implicit non-payable guard.
-/

open Stele Stele.Notation

namespace FeProofs.Identity.Syntax

def contractSyntax : ContractDecl := solidity% contract FeIdentity {
  constructor() { }

  function identity(uint256 value) external returns (uint256) {
    return value;
  }
}

end FeProofs.Identity.Syntax
