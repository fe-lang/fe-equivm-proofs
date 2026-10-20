import Stele.Notation

/-!
# FeIndexedPackedStore surface spec

Fe's `StoragePackedArray<8>` field at slot 0, indexed at run time and bounded by an explicit
`index < 64` check.  Element `i` is byte `i % 32` of word `keccak256(0) + i / 32` (see `Spec.lean`).
`setTwo` checks its second index only after the first write, so a bad second index reverts the
whole call.  Fe rejects call value on every entry point, including the constructor.  Transitions are
listed in the dispatcher's compare order.
-/

open Stele Stele.Notation

namespace FeProofs.IndexedPackedStore.Syntax

def contractSyntax : ContractDecl := solidity% contract FeIndexedPackedStore {
  uint8[64] pack;

  constructor() { }

  function set(uint256 index, uint256 value) external {
    require(index < 64);
    pack[index] = uint8(value);
  }

  function setTwo(uint256 first_index, uint256 first_value, uint256 second_index,
      uint256 second_value) external {
    require(first_index < 64);
    pack[first_index] = uint8(first_value);
    require(second_index < 64);
    pack[second_index] = uint8(second_value);
  }

  function get(uint256 index) external returns (uint256) {
    require(index < 64);
    return uint256(pack[index]);
  }
}

end FeProofs.IndexedPackedStore.Syntax
