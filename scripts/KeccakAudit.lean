import FeProofs.Common.Selectors

/-! Run after applying the Keccak patch and building the project:
`lake env lean scripts/KeccakAudit.lean`.

The equivalence theorem may use Lean's standard axioms. The shared concrete facts must
remain kernel-checked, with no `sorryAx` or `native_decide` axioms.
-/

#print axioms Ethereum.Keccak256.hash_eq_referenceHash
#print axioms FeProofs.Selectors.approve
#print axioms FeProofs.Selectors.totalSupply
#print axioms FeProofs.Selectors.transferFrom
#print axioms FeProofs.Selectors.balanceOf
#print axioms FeProofs.Selectors.transfer
#print axioms FeProofs.Selectors.allowance
