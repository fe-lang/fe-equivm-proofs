import FeProofs.Common.Selectors

/-!
# FeERC20 selectors

The selector table follows `contract.transitions` order. Kernel-checked facts reuse the
shared token signatures. `Common.lean` bridges each Stele transition's signature string
to its table entry and defines the calldata selector predicate.
-/

namespace FeProofs.ERC20

/-- Function selectors in `contract.transitions` order (6 entries). -/
def feERC20SelBytes : Nat → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩  -- approve(address,uint256)
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩  -- totalSupply()
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩  -- transferFrom(address,address,uint256)
  | 3 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩  -- balanceOf(address)
  | 4 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩  -- transfer(address,uint256)
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩  -- allowance(address,address)

/-- `keccak256("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
theorem approveSelectorFact :
    (Ethereum.KEC (String.toByteArray "approve(address,uint256)")).extract 0 4 = feERC20SelBytes 0 := by
  exact FeProofs.Selectors.approve

/-- `keccak256("totalSupply()")[0:4] = 0x18160ddd`. -/
theorem totalSupplySelectorFact :
    (Ethereum.KEC (String.toByteArray "totalSupply()")).extract 0 4 = feERC20SelBytes 1 := by
  exact FeProofs.Selectors.totalSupply

/-- `keccak256("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
theorem transferFromSelectorFact :
    (Ethereum.KEC (String.toByteArray "transferFrom(address,address,uint256)")).extract 0 4 = feERC20SelBytes 2 := by
  exact FeProofs.Selectors.transferFrom

/-- `keccak256("balanceOf(address)")[0:4] = 0x70a08231`. -/
theorem balanceOfSelectorFact :
    (Ethereum.KEC (String.toByteArray "balanceOf(address)")).extract 0 4 = feERC20SelBytes 3 := by
  exact FeProofs.Selectors.balanceOf

/-- `keccak256("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
theorem transferSelectorFact :
    (Ethereum.KEC (String.toByteArray "transfer(address,uint256)")).extract 0 4 = feERC20SelBytes 4 := by
  exact FeProofs.Selectors.transfer

/-- `keccak256("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
theorem allowanceSelectorFact :
    (Ethereum.KEC (String.toByteArray "allowance(address,address)")).extract 0 4 = feERC20SelBytes 5 := by
  exact FeProofs.Selectors.allowance

end FeProofs.ERC20
