import Fe.EVM.World

/-!
# Refinement of a Fe contract model by EVM bytecode

`Refines p bytecode model`: on every message call the bytecode either runs out of gas, or does
what the model does, as far as profile `p` observes.  A model that calls other contracts or
reads its gas takes those inputs from a feed, and does what the bytecode does under some feed.
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
    so only running out of gas can match it.  A run that stops from inside a callee is a success,
    like one that returns.  A read past the end of the return data is the EVM's invalid memory
    access. -/
def Agrees (p : Profile) (evm : EvmResult) :
    Option (Except (Exit World) (ByteArray × World)) → Prop
  | none => False
  | some (.ok (out, w)) | some (.error (.stop out w)) =>
      ∃ g' A', evm = .ok (.success (w.accounts, g', A') out) ∧ (p = .P1 → A'.logSeries = w.logs)
  | some (.error (.revert data)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = data)
  | some (.error (.panic code)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = panicData code)
  | some (.error .static) => evm = .error .StaticModeViolation
  | some (.error .trap) => evm = .error .InvalidInstruction
  | some (.error .oob) => evm = .error .InvalidMemoryAccess

/-- One model run ends as another does: with the same exit, or successfully with the same return
    data, accounts and logs, whether each returns or stops.  Memory may differ. -/
inductive EndsAs : Option (Except (Exit World) (ByteArray × World)) →
    Option (Except (Exit World) (ByteArray × World)) → Prop
  | stop_ok {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) : EndsAs (some (.error (.stop out w'))) (some (.ok (out, w)))
  | exit (f : Exit World) : EndsAs (some (.error f)) (some (.error f))
  | ok_ok {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) : EndsAs (some (.ok (out, w'))) (some (.ok (out, w)))
  | diverge : EndsAs none none

/-- A result that agrees with a run agrees with any run that ends as it does. -/
theorem Agrees.of_endsAs {p : Profile} {evm : EvmResult}
    {a b : Option (Except (Exit World) (ByteArray × World))} (h : EndsAs a b)
    (hb : Agrees p evm b) : Agrees p evm a := by
  cases h with
  | stop_ok ha hl => simpa only [Agrees, ha, hl] using hb
  | exit f => exact hb
  | ok_ok ha hl => simpa only [Agrees, ha, hl] using hb
  | diverge => exact hb

/-- A contract's model: its constructor, from the argument bytes that follow the creation code,
    and its runtime entry, from calldata to return data. -/
structure ContractModel where
  init : ByteArray → FeM Unit
  runtime : FeM ByteArray

/-- Refinement at fixed inputs: the bytecode runs out of gas, or some feed makes the model end
    as the bytecode does.  The feed is what the model cannot compute: the gas and the substate
    of each call it makes. -/
def RefinesFor (p : Profile) (m : ContractModel) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass
    ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A feed))

/-- A certificate of a model that never consults the context, stated without a feed, is one. -/
theorem RefinesFor.closed {p : Profile} {m : ContractModel} {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (h : Ξ σ σ₀ g A I = .error .OutOfGass
      ∨ Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A))) :
    RefinesFor p m σ σ₀ g A I :=
  h.imp id fun h => ⟨[], h⟩

/-- The runtime bytecode refines the model on every message call that `admits` holds of. -/
def RefinesOn (p : Profile) (bytecode : ByteArray) (m : ContractModel)
    (admits : ExecutionEnv → Prop) : Prop :=
  ∀ σ σ₀ g A I, I.code = bytecode → admits I → RefinesFor p m σ σ₀ g A I

/-- The runtime bytecode refines the model on every message call. -/
def Refines (p : Profile) (bytecode : ByteArray) (m : ContractModel) : Prop :=
  RefinesOn p bytecode m fun I => I.calldata.size < UInt256.size

/-- Calldata shorter than `2 ^ 64` bytes.  Fe's std reads a calldata length as a `u64`, and its
    backend assumes the length fits, so a model exported from std and the bytecode agree only on
    such calls.  No transaction comes near the bound. -/
def CalldataFits (I : ExecutionEnv) : Prop := I.calldata.size < 2 ^ 64

/-- Deployment: run with any valid argument bytes after it, the creation bytecode does what the
    model's constructor does, under some feed, and returns the runtime bytecode. -/
def RefinesDeploy (p : Profile) (creation runtime : ByteArray) (m : ContractModel)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → I.perm = true →
    Ξ σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I)
          ((m.init args >>= fun _ => pure runtime).exec I (World.init σ A feed))

/-- A deployment certificate of a constructor that never consults the context, stated without a
    feed, is one. -/
theorem RefinesDeploy.closed {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop}
    (h : ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → I.perm = true →
      Ξ σ σ₀ g A I = .error .OutOfGass
        ∨ Agrees p (Ξ σ σ₀ g A I)
            ((m.init args >>= fun _ => pure runtime).exec I (World.init σ A))) :
    RefinesDeploy p creation runtime m validArgs :=
  fun σ σ₀ g A I args hargs hcode hperm =>
    (h σ σ₀ g A I args hargs hcode hperm).imp id fun h => ⟨[], h⟩

/-- How a certificate is used: a property of the accounts the model can end with, shown for
    every feed, holds of the accounts the bytecode ends with. -/
theorem RefinesFor.accounts {p : Profile} {m : ContractModel} {σ σ₀ σ' : AccountMap}
    {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    {P : AccountMap → Prop} (h : RefinesFor p m σ σ₀ g A I)
    (hP : ∀ feed out w, m.runtime.exec I (World.init σ A feed) = some (.ok (out, w))
      ∨ m.runtime.exec I (World.init σ A feed) = some (.error (.stop out w)) → P w.accounts)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) : P σ' := by
  rcases h with hoog | ⟨feed, hag⟩
  · rw [hrun] at hoog; cases hoog
  cases hm : m.runtime.exec I (World.init σ A feed) with
  | none => rw [hm] at hag; exact hag.elim
  | some res =>
    rw [hm] at hag
    cases res with
    | error f =>
      cases f with
      | revert data => obtain ⟨_, _, h, _⟩ := hag; rw [hrun] at h; cases h
      | panic code => obtain ⟨_, _, h, _⟩ := hag; rw [hrun] at h; cases h
      | static => rw [hrun] at hag; cases hag
      | trap => rw [hrun] at hag; cases hag
      | oob => rw [hrun] at hag; cases hag
      | stop out w =>
        obtain ⟨_, _, h, _⟩ := hag
        rw [hrun] at h
        have hσ : σ' = w.accounts := by injection h with h; injection h with h; injection h with h
        exact hσ ▸ hP feed out w (Or.inr hm)
    | ok pr =>
      obtain ⟨out, w⟩ := pr
      obtain ⟨_, _, h, _⟩ := hag
      rw [hrun] at h
      have hσ : σ' = w.accounts := by injection h with h; injection h with h; injection h with h
      exact hσ ▸ hP feed out w (Or.inl hm)

end Fe.EVM
