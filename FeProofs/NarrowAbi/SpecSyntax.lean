import Stele.Notation

/-!
# FeNarrowAbi surface spec

Identity messages over `int8`, `uint8`, `bool`, and `address`.  Fe decodes each argument with
Solidity's canonical checks (a non-canonical word reverts) and returns its canonical encoding.
Fe rejects call value on every entry point, including the constructor.  Transitions are listed in
selector order.
-/

open Stele Stele.Notation

namespace FeProofs.NarrowAbi.Syntax

def contractSyntax : ContractDecl := solidity% contract FeNarrowAbi {
  constructor() { }

  function echo_i8(int8 value) external returns (int8) {
    return value;
  }

  function echo_u8(uint8 value) external returns (uint8) {
    return value;
  }

  function echo_bool(bool value) external returns (bool) {
    return value;
  }

  function echo_address(address value) external returns (address) {
    return value;
  }
}

end FeProofs.NarrowAbi.Syntax
