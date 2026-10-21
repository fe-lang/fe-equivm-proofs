import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.ERC20.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feERC20CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.ERC20.feERC20CreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.ERC20.feERC20CreationBytecode

end feERC20CreationBlocks
