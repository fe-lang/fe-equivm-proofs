import Stele.Notation

/-!
# FeERC20 surface spec

`FeERC20.fe` is the EquiVM `ERC20` example token written in Fe.  Its storage layout is the
Solidity one: `balanceOf` in slot 0, `allowance` in slot 1 (a Fe map of maps, whose entries
derive their slots like a Solidity nested mapping), `totalSupply` in slot 2.

The declarations, constructor and function bodies are those of EquiVM's `Examples/ERC20/SpecSyntax.lean`
verbatim; only the order differs, since transitions are listed in the dispatcher's compare order
(ascending selector).  Fe rejects call value on every entry point, including the constructor, as
the implicit non-payable guards do.  Logs and revert payloads are outside the refinement relation.
-/

open Stele Stele.Notation

namespace FeProofs.ERC20.Syntax

def contractSyntax : ContractDecl := solidity% contract FeERC20 {
  mapping(address => uint256) balanceOf;                     -- slot 0
  mapping(address => mapping(address => uint256)) allowance; -- slot 1
  uint256 totalSupply;                                      -- slot 2

  event Transfer(address indexed «from», address indexed «to», uint256 value);
  event Approval(address indexed owner, address indexed spender, uint256 value);

  constructor(uint256 initialSupply) {
    balanceOf[msg.sender] = initialSupply;
    totalSupply = initialSupply;
    emit Transfer(address(0), msg.sender, initialSupply);
  }

  function approve(address spender, uint256 value) external returns (bool) {
    allowance[msg.sender][spender] = value;

    emit Approval(msg.sender, spender, value);
    return true;
  }

  function totalSupply() external view returns (uint256) {
    return totalSupply;
  }

  function transferFrom(address «from», address «to», uint256 value) external returns (bool) {
    uint256 currentAllowance = allowance[«from»][msg.sender];
    require(currentAllowance >= value, "ERC20: insufficient allowance");
    require(balanceOf[«from»] >= value, "ERC20: insufficient balance");

    allowance[«from»][msg.sender] = currentAllowance - value;
    balanceOf[«from»] = (balanceOf[«from»] - value) as uint256;
    balanceOf[«to»] = (balanceOf[«to»] + value) as uint256;

    emit Transfer(«from», «to», value);
    return true;
  }

  function balanceOf(address owner) external view returns (uint256) {
    return balanceOf[owner];
  }

  function transfer(address «to», uint256 value) external returns (bool) {
    require(balanceOf[msg.sender] >= value, "ERC20: insufficient balance");

    balanceOf[msg.sender] -= value;
    balanceOf[«to»] = (balanceOf[«to»] + value) as uint256;

    emit Transfer(msg.sender, «to», value);
    return true;
  }

  function allowance(address owner, address spender) external view returns (uint256) {
    return allowance[owner][spender];
  }
}

end FeProofs.ERC20.Syntax
