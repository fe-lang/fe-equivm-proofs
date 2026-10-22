import FeProofs.Common.Selectors

/-!
# FeWETH9 selectors

The selector table follows `contract.transitions` order. Kernel-checked facts reuse the
shared token signatures. `Common.lean` bridges each Stele transition's signature string
to its table entry and defines the calldata selector predicate.
-/

namespace FeProofs.WETH9

/-- Function selectors in `contract.transitions` order (11 entries). -/
def feWETH9SelBytes : Nat → ByteArray
  | 0 => ⟨#[0x06, 0xfd, 0xde, 0x03]⟩  -- name()
  | 1 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩  -- approve(address,uint256)
  | 2 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩  -- totalSupply()
  | 3 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩  -- transferFrom(address,address,uint256)
  | 4 => ⟨#[0x2e, 0x1a, 0x7d, 0x4d]⟩  -- withdraw(uint256)
  | 5 => ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩  -- decimals()
  | 6 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩  -- balanceOf(address)
  | 7 => ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩  -- symbol()
  | 8 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩  -- transfer(address,uint256)
  | 9 => ⟨#[0xd0, 0xe3, 0x0d, 0xb0]⟩  -- deposit()
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩  -- allowance(address,address)

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak256("name()")[0:4] = 0x06fdde03`. -/
theorem nameSelectorFact :
    (Ethereum.KEC (String.toByteArray "name()")).extract 0 4 = feWETH9SelBytes 0 := by
  decide +kernel

/-- `keccak256("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
theorem approveSelectorFact :
    (Ethereum.KEC (String.toByteArray "approve(address,uint256)")).extract 0 4 = feWETH9SelBytes 1 := by
  exact FeProofs.Selectors.approve

/-- `keccak256("totalSupply()")[0:4] = 0x18160ddd`. -/
theorem totalSupplySelectorFact :
    (Ethereum.KEC (String.toByteArray "totalSupply()")).extract 0 4 = feWETH9SelBytes 2 := by
  exact FeProofs.Selectors.totalSupply

/-- `keccak256("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
theorem transferFromSelectorFact :
    (Ethereum.KEC (String.toByteArray "transferFrom(address,address,uint256)")).extract 0 4 = feWETH9SelBytes 3 := by
  exact FeProofs.Selectors.transferFrom

/-- `keccak256("withdraw(uint256)")[0:4] = 0x2e1a7d4d`. -/
theorem withdrawSelectorFact :
    (Ethereum.KEC (String.toByteArray "withdraw(uint256)")).extract 0 4 = feWETH9SelBytes 4 := by
  decide +kernel

/-- `keccak256("decimals()")[0:4] = 0x313ce567`. -/
theorem decimalsSelectorFact :
    (Ethereum.KEC (String.toByteArray "decimals()")).extract 0 4 = feWETH9SelBytes 5 := by
  decide +kernel

/-- `keccak256("balanceOf(address)")[0:4] = 0x70a08231`. -/
theorem balanceOfSelectorFact :
    (Ethereum.KEC (String.toByteArray "balanceOf(address)")).extract 0 4 = feWETH9SelBytes 6 := by
  exact FeProofs.Selectors.balanceOf

/-- `keccak256("symbol()")[0:4] = 0x95d89b41`. -/
theorem symbolSelectorFact :
    (Ethereum.KEC (String.toByteArray "symbol()")).extract 0 4 = feWETH9SelBytes 7 := by
  decide +kernel

/-- `keccak256("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
theorem transferSelectorFact :
    (Ethereum.KEC (String.toByteArray "transfer(address,uint256)")).extract 0 4 = feWETH9SelBytes 8 := by
  exact FeProofs.Selectors.transfer

/-- `keccak256("deposit()")[0:4] = 0xd0e30db0`. -/
theorem depositSelectorFact :
    (Ethereum.KEC (String.toByteArray "deposit()")).extract 0 4 = feWETH9SelBytes 9 := by
  decide +kernel

/-- `keccak256("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
theorem allowanceSelectorFact :
    (Ethereum.KEC (String.toByteArray "allowance(address,address)")).extract 0 4 = feWETH9SelBytes 10 := by
  exact FeProofs.Selectors.allowance

end FeProofs.WETH9
