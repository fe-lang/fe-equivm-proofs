import Stele.Notation

/-!
# FePackedStore surface spec

`StoragePackedArray<8>` field at slot 0: lane `i` is byte `i` of word `keccak256(0)`.  Lanes 0 and
1 are the two `uint8` fields `lane0`/`lane1` (their location is the custom layout in `Spec.lean`).
Setters truncate to eight bits; getters zero-extend.  Fe rejects call value on every entry point,
including the constructor.  Transitions are listed in selector order.
-/

open Stele Stele.Notation

namespace FeProofs.PackedStore.Syntax

def contractSyntax : ContractDecl := solidity% contract FePackedStore {
  uint8 lane0;
  uint8 lane1;

  constructor() { }

  function get1() external returns (uint256) {
    return uint256(lane1);
  }

  function get0() external returns (uint256) {
    return uint256(lane0);
  }

  function setBoth(uint256 first, uint256 second) external {
    lane0 = uint8(first);
    lane1 = uint8(second);
  }

  function set1(uint256 value) external {
    lane1 = uint8(value);
  }

  function set0(uint256 value) external {
    lane0 = uint8(value);
  }
}

end FeProofs.PackedStore.Syntax
