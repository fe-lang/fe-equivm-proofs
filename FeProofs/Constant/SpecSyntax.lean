import Stele.Notation

/-!
# FeConstant surface spec

`answer()` returns the constant `42`.  Fe rejects call value on every entry point, including
the constructor, so both carry the implicit non-payable guard.
-/

open Stele Stele.Notation

namespace FeProofs.Constant.Syntax

def contractSyntax : ContractDecl := solidity% contract FeConstant {
  constructor() { }

  function answer() external returns (uint256) {
    return 42;
  }
}

end FeProofs.Constant.Syntax
