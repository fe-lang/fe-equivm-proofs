import Ethereum.Semantics
import Fe.Core

/-!
# The EVM world of a Fe model

A contract's model runs in the EVM's own state types, so a certificate needs no relation
between two representations of storage.
-/

namespace Fe.EVM

open Ethereum

/-- The part of the EVM state a contract's model reads and writes. -/
structure World where
  accounts : AccountMap
  logs : LogSeries

/-- The world a message call starts in. -/
def World.init (σ : AccountMap) (A : Substate) : World := ⟨σ, A.logSeries⟩

abbrev Env := ExecutionEnv

/-- The model monad on the EVM. -/
abbrev FeM := Fe.M Env World

/-- The calldata of the current call. -/
def calldata : FeM ByteArray := do return (← read).calldata

/-- An entry point that takes no value reverts when sent some. -/
def nonPayable : FeM Unit := do
  if (← read).weiValue ≠ ⟨0⟩ then Fe.M.revert ByteArray.empty

end Fe.EVM
