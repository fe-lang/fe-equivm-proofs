import FeProofs.ERC20.ExportedCorrect
import FeProofs.ERC20.ModelCorrect

/-!
# FeERC20: the bytecode refines the exported contract

`Exported.lean` is the whole contract as `fe-lean-export` prints it.  Each exported entry ends as
the hand-written model's does (`runtime_endsAs`, `init_endsAs` in `ExportedCorrect.lean`), so the
certificates for that model carry over.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20.Exported

/-! ## The certificate -/

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem feERC20RefinesExported : RefinesOn .P0 feERC20Bytecode contract CalldataFits := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hown hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feERC20RefinesModel σ σ₀ g A I ByteArray.empty
      (by rw [ByteArray.append_empty]; exact hcode) rfl hown hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A feed) (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment with one ABI-encoded `uint256` argument refines the exported deployment entry. -/
theorem feERC20DeployRefinesExported :
    RefinesDeploy .P0 feERC20CreationBytecode feERC20Bytecode contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hown hperm
  rcases feERC20DeployRefinesModel σ σ₀ g A I _ ⟨v, rfl⟩ hcode hown hperm with h | ⟨feed, h⟩
  · exact Or.inl h
  · replace h : Agrees .P0 (Ξ σ σ₀ g A I) ((Model.init (ctorTail v) >>= fun _ =>
        pure feERC20Bytecode).exec I (World.init σ A feed)) := by
      simpa [Model.contract, ByteArray.append_empty] using h
    exact Or.inr ⟨feed, Agrees.of_endsAs
      (init_endsAs v _ I (World.init σ A feed) (by simp [World.init, UInt256.size])) h⟩

end FeProofs.ERC20.Exported
