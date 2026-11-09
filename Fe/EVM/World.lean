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

/-- Calldata is too short to hold `words` argument words after the selector, or so long that
    Solidity's signed length check rejects it. -/
def BadHead (cd : ByteArray) (words : Nat) : Prop :=
  cd.size < 4 + 32 * words ∨ 2 ^ 255 + 4 ≤ cd.size

instance (cd : ByteArray) (words : Nat) : Decidable (BadHead cd words) := by
  unfold BadHead; infer_instance

/-- The word at `slot` of the current contract's storage. -/
def sload (slot : UInt256) : FeM UInt256 := do
  let env ← read
  let w ← get
  return w.accounts.get? env.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD slot ⟨0⟩)

/-- The account map after the contract at `owner` stores `val` at `slot`.  A zero erases the
    slot, as the EVM does. -/
def storeWord (owner : AccountAddress) (σ : AccountMap) (slot val : UInt256) : AccountMap :=
  σ.get? owner |>.option σ fun acc =>
    σ.insert owner
      (if val == default then { acc with storage := acc.storage.erase slot }
       else { acc with storage := acc.storage.insert slot val })

/-- Store `val` at `slot` of the current contract's storage.  Under a static call it fails. -/
def sstore (slot val : UInt256) : FeM Unit := do
  let env ← read
  if env.perm then
    modify fun w => { w with accounts := storeWord env.codeOwner w.accounts slot val }
  else
    Fe.M.fail .static

end Fe.EVM
