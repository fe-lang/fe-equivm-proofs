import Ethereum.Semantics

/-! Kernel-checked selector hashes shared by contract certificates. -/

namespace FeProofs.Common.SelectorGet

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Selector hash of `get()`. -/
theorem getSelectorHash :
    (Ethereum.KEC (String.toByteArray "get()")).extract 0 4 = ⟨#[0x6d, 0x4c, 0xe6, 0x3c]⟩ := by
  decide +kernel

end FeProofs.Common.SelectorGet
