import FeProofs.ERC20.ExportedCorrect
import FeProofs.ERC20.SonatinaCorrect

/-!
# FeERC20: the bytecode refines the hand-written model

The certificates of the exported contract (`SonatinaCorrect.lean`) carry over to the hand-written
model: each exported entry ends as the model's does (`runtime_endsAs`, `init_endsAs`), so the
bytecode's result, which agrees with the exported run, agrees with the model's (`agrees_endsAs`).
The runtime certificate is on calldata below `2 ^ 64` bytes (`CalldataFits`), as the exported
one is, where a certificate of the bytecode alone (`Refines`) is on calldata below `2 ^ 256`.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20

/-- A result that agrees with a run agrees with any run that it ends as: `Agrees.of_endsAs` the
    other way. -/
theorem agrees_endsAs {p : Profile} {evm : EvmResult}
    {a b : Option (Except (Exit World) (ByteArray × World))} (h : EndsAs a b)
    (ha : Agrees p evm a) : Agrees p evm b := by
  cases h with
  | stop_ok hacc hl _ | stop_stop hacc hl _ | ok_ok hacc hl _ | ok_stop hacc hl _ =>
    simpa only [Agrees, hacc, hl] using ha
  | exit f => exact ha
  | panic_revert code => exact ha
  | diverge => exact ha

/-- The runtime bytecode refines the hand-written model, on calldata below `2 ^ 64` bytes. -/
theorem feERC20RefinesModel : RefinesOn .P0 feERC20P1Bytecode Model.contract CalldataFits :=
  fun σ σ₀ g A I tail hcode htail hown hfits =>
    (Sonatina.feERC20RefinesExportedP1.toP0 σ σ₀ g A I tail hcode htail hown hfits).imp id
      fun ⟨feed, h⟩ => ⟨feed, agrees_endsAs (Exported.runtime_endsAs I (World.init σ A feed)
        (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment with one ABI-encoded `uint256` argument, the initial supply, refines the
    hand-written constructor. -/
theorem feERC20DeployRefinesModel :
    RefinesDeploy .P0 feERC20P1CreationBytecode feERC20P1Bytecode Model.contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hown hperm
  refine (Sonatina.feERC20DeployRefinesExportedP1.toP0 σ σ₀ g A I _ ⟨v, rfl⟩ hcode hown
    hperm).imp id fun ⟨feed, h⟩ => ⟨feed, ?_⟩
  simpa [Model.contract, ByteArray.append_empty] using agrees_endsAs (Exported.init_endsAs v _ I
    (World.init σ A feed) (by simp [World.init, UInt256.size])) h

end FeProofs.ERC20
