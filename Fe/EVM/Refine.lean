import Fe.EVM.World

/-!
# Refinement of a Fe contract model by EVM bytecode

`Refines p bytecode model`: on every message call the bytecode either runs out of gas, or does
what the model does, as far as profile `p` observes.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM

/-- What a result observes.  `P0`: outcome kind, return data, account map.  `P1` adds event logs
    and revert payloads.  Neither observes gas. -/
inductive Profile where
  | P0
  | P1

/-- The return data of a panic, Solidity's `Panic(uint256)`.  To confirm against Fe's lowering
    when the first panic path is ported. -/
def panicData (code : Nat) : ByteArray :=
  ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (UInt256.ofNat code).toByteArray

abbrev EvmResult :=
  Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))

/-- The EVM result agrees with the model's run.  A model run that diverges agrees with nothing,
    so only running out of gas can match it. -/
def Agrees (p : Profile) (evm : EvmResult) : Option (Except Fail (ByteArray × World)) → Prop
  | none => False
  | some (.ok (out, w)) =>
      ∃ g' A', evm = .ok (.success (w.accounts, g', A') out) ∧ (p = .P1 → A'.logSeries = w.logs)
  | some (.error (.revert data)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = data)
  | some (.error (.panic code)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = panicData code)
  | some (.error .static) => evm = .error .StaticModeViolation

/-- A contract's model: its runtime entry, from calldata to return data. -/
structure ContractModel where
  runtime : FeM ByteArray

/-- Refinement at fixed inputs. -/
def RefinesFor (p : Profile) (m : ContractModel) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass
    ∨ Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A))

/-- The runtime bytecode refines the model on every message call. -/
def Refines (p : Profile) (bytecode : ByteArray) (m : ContractModel) : Prop :=
  ∀ σ σ₀ g A I, I.code = bytecode → I.calldata.size < UInt256.size →
    RefinesFor p m σ σ₀ g A I

end Fe.EVM
