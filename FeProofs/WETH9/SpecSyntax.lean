import Stele.Notation

/-!
# FeWETH9 surface spec

`src/lib.fe` is canonical WETH9 (`gnosis/canonical-weth`, `contracts/WETH9.sol`) written in Fe,
with WETH9's storage layout: `name` and `symbol` (Solidity strings) in slots 0 and 1, `decimals` in
slot 2, `balanceOf` in slot 3 and `allowance` (a Fe map of maps, whose entries derive their slots
like a Solidity nested mapping) in slot 4.

The contract is EquiVM's `Benchmarks/WETH9/SpecSyntax.lean` verbatim, in the same order, which is
also Fe's dispatcher order (ascending selector).  Only the configuration differs (`Spec.lean`):
- strings use the Solidity 0.8 storage semantics, under which a length header that contradicts its
  short/long flag reverts (Fe's `SolString` panics with `0x22`); solc 0.5.16 decodes any header;
- calldata is decoded strictly, so a non-canonical `address` argument reverts as in Fe; solc 0.5.16
  masks it.

Logs and revert payloads are outside the refinement relation, and like EquiVM's spec this one has no
events.
-/

open Stele Stele.Notation

namespace FeProofs.WETH9.Syntax

def contractSyntax : ContractDecl := solidity% contract WETH9 {
  string name;
  string symbol;
  uint8 decimals;
  mapping(address => uint256) balanceOf;
  mapping(address => mapping(address => uint256)) allowance;

  constructor() {
    name = "Wrapped Ether";
    symbol = "WETH";
    decimals = 18;
  }

  function name() external returns (string) {
    return name;
  }

  function approve(address guy, uint256 wad) external returns (bool) {
    allowance[msg.sender][guy] = wad;
    return true;
  }

  function totalSupply() external returns (uint256) {
    return address(this).balance;
  }

  function transferFrom(address src, address dst, uint256 wad) external returns (bool) {
    require(balanceOf[src] >= wad);
    if (src != msg.sender && allowance[src][msg.sender] != type(uint256).max) {
      require(allowance[src][msg.sender] >= wad);
      allowance[src][msg.sender] = allowance[src][msg.sender] - wad;
    }
    balanceOf[src] = balanceOf[src] - wad;
    balanceOf[dst] = balanceOf[dst] + wad;
    return true;
  }

  function withdraw(uint256 wad) external {
    require(balanceOf[msg.sender] >= wad);
    balanceOf[msg.sender] = balanceOf[msg.sender] - wad;
    (bool success, bytes memory _data) = msg.sender.call{value: wad}(new bytes(0));
    require(success);
  }

  function decimals() external returns (uint8) {
    return decimals;
  }

  function balanceOf(address owner) external returns (uint256) {
    return balanceOf[owner];
  }

  function symbol() external returns (string) {
    return symbol;
  }

  function transfer(address dst, uint256 wad) external returns (bool) {
    var _ok = transferFrom(msg.sender, dst, wad);
    return _ok;
  }

  function deposit() external payable {
    balanceOf[msg.sender] = balanceOf[msg.sender] + msg.value;
  }

  function allowance(address owner, address guy) external returns (uint256) {
    return allowance[owner][guy];
  }

  fallback() external payable {
    balanceOf[msg.sender] = balanceOf[msg.sender] + msg.value;
  }
}

end FeProofs.WETH9.Syntax
