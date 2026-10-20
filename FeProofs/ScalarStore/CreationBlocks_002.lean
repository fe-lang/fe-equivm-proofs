import Reasoning.Reach
import Reasoning.Initcode
import FeProofs.ScalarStore.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feScalarStoreCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode FeProofs.ScalarStore.feScalarStoreCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left FeProofs.ScalarStore.feScalarStoreCreationBytecode

end feScalarStoreCreationBlocks
