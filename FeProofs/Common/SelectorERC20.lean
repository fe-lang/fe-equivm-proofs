import Ethereum.Semantics

/-! Kernel-checked selector hashes shared by contract certificates. -/

namespace FeProofs.Common.SelectorERC20

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Selector hash of `approve(address,uint256)`. -/
theorem approveSelectorHash :
    (Ethereum.KEC (String.toByteArray "approve(address,uint256)")).extract 0 4 = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ := by
  decide +kernel

/-- Selector hash of `totalSupply()`. -/
theorem totalSupplySelectorHash :
    (Ethereum.KEC (String.toByteArray "totalSupply()")).extract 0 4 = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ := by
  decide +kernel

/-- Selector hash of `transferFrom(address,address,uint256)`. -/
theorem transferFromSelectorHash :
    (Ethereum.KEC (String.toByteArray "transferFrom(address,address,uint256)")).extract 0 4 = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ := by
  decide +kernel

/-- Selector hash of `balanceOf(address)`. -/
theorem balanceOfSelectorHash :
    (Ethereum.KEC (String.toByteArray "balanceOf(address)")).extract 0 4 = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ := by
  decide +kernel

/-- Selector hash of `transfer(address,uint256)`. -/
theorem transferSelectorHash :
    (Ethereum.KEC (String.toByteArray "transfer(address,uint256)")).extract 0 4 = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := by
  decide +kernel

/-- Selector hash of `allowance(address,address)`. -/
theorem allowanceSelectorHash :
    (Ethereum.KEC (String.toByteArray "allowance(address,address)")).extract 0 4 = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ := by
  decide +kernel

end FeProofs.Common.SelectorERC20
