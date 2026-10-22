import Ethereum.SpongeHash.Keccak256

/-!
# Shared token selectors

These closed facts depend only on the ABI signature, not on a contract's transition order or
storage layout. ERC20 and WETH9 use the same six signatures. Their selector tables refer to
these proofs so that each hash is checked once, even when both contracts are rebuilt.

The proofs use kernel evaluation, with the same recursion and heartbeat settings as the
contract selector files. No native evaluation is needed.
-/

namespace FeProofs.Selectors

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem approve :
    (Ethereum.KEC (String.toByteArray "approve(address,uint256)")).extract 0 4 =
      ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ := by
  decide +kernel

theorem totalSupply :
    (Ethereum.KEC (String.toByteArray "totalSupply()")).extract 0 4 =
      ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ := by
  decide +kernel

theorem transferFrom :
    (Ethereum.KEC (String.toByteArray "transferFrom(address,address,uint256)")).extract 0 4 =
      ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ := by
  decide +kernel

theorem balanceOf :
    (Ethereum.KEC (String.toByteArray "balanceOf(address)")).extract 0 4 =
      ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ := by
  decide +kernel

theorem transfer :
    (Ethereum.KEC (String.toByteArray "transfer(address,uint256)")).extract 0 4 =
      ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := by
  decide +kernel

theorem allowance :
    (Ethereum.KEC (String.toByteArray "allowance(address,address)")).extract 0 4 =
      ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ := by
  decide +kernel

end FeProofs.Selectors
