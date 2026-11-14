import FeProofs.ERC20.Conservation
import FeProofs.ERC20.RuntimeCorrect
import FeProofs.ERC20.SonatinaCorrect

/-!
# FeERC20: conservation, stated on the bytecode

Every successful call of the deployed bytecode keeps the balances of the holders equal to the
supply, and a successful deployment makes them so.  The statements mention the bytecode and the
EVM semantics; the models appear only in the proofs, which go through the exported contract: the
hand-written model conserves (`Conservation.lean`), each exported entry ends as the hand-written
one does (`runtime_endsAs`, `init_endsAs`), and the bytecode refines the exported contract
(`feERC20RefinesExported`, `feERC20DeployRefinesExported`).

The bytecode statements hold of any runtime and creation bytecode with `P0` certificates against
the exported contract (`call_keeps`, `deploy_keeps`).  `call_conserves` and `deploy_conserves`
are their instances at the pinned bytecode, `P1.call_conserves` and `P1.deploy_conserves` at the
bytecode of `P1/`, through its `P1` certificates (`feERC20RefinesExportedP1.toP0`).
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20

/-- Every run of the exported runtime entry that returns or stops, on a call that the holders
    `S` cover, from a world where their balances add up to the supply, ends in a world where
    they do. -/
theorem Exported.runtime_conserves {I : ExecutionEnv} {S : List UInt256} {w w' : World}
    {out : ByteArray} (hmem : w.memory.size + 1024 < UInt256.size) (hfits : CalldataFits I)
    (hS : CollisionFree S) (hcall : Covers S I) (hcons : Conserved I.codeOwner w.accounts S)
    (hrun : Succeeds (Exported.contract.runtime.exec I w) out w') :
    Conserved I.codeOwner w'.accounts S := by
  obtain ⟨w'', hrun', hacc⟩ := (Exported.runtime_endsAs I w hmem hfits).succeeds hrun
  exact hacc ▸ FeProofs.ERC20.runtime_conserves hS hcall hcons hrun'

/-- The exported deployment entry, returning the runtime `code`, makes the balances of the
    holders `S` add up to the supply, when the deployer is one of them and each starts with
    none. -/
theorem Exported.init_keeps {I : ExecutionEnv} {S : List UInt256} {w w' : World}
    {v : UInt256} {code out : ByteArray} (hmem : w.memory.size + 1024 < UInt256.size)
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner w.accounts a = ⟨0⟩)
    (hrun : Succeeds ((Exported.contract.init (ctorTail v) >>= fun tail =>
      pure (code ++ tail)).exec I w) out w') :
    Conserved I.codeOwner w'.accounts S := by
  obtain ⟨w'', hrun', hacc⟩ := (Exported.init_endsAs v code I w hmem).succeeds hrun
  rw [← hacc]
  rcases hrun' with hrun' | hrun' <;> simp only [M.exec_bind] at hrun' <;> split at hrun' <;>
    simp at hrun' <;> rename_i hinit
  · obtain ⟨-, rfl⟩ := hrun'
    exact FeProofs.ERC20.init_conserves hS hdeployer hzero hinit
  · subst hrun'
    exact absurd hinit (init_noStop _ I w _ _)

/-- `Exported.init_keeps` at the pinned runtime. -/
theorem Exported.init_conserves {I : ExecutionEnv} {S : List UInt256} {w w' : World}
    {v : UInt256} {out : ByteArray} (hmem : w.memory.size + 1024 < UInt256.size)
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner w.accounts a = ⟨0⟩)
    (hrun : Succeeds ((Exported.contract.init (ctorTail v) >>= fun tail =>
      pure (feERC20Bytecode ++ tail)).exec I w) out w') :
    Conserved I.codeOwner w'.accounts S :=
  Exported.init_keeps hmem hS hdeployer hzero hrun

section Certified

variable {runtime creation : ByteArray}

/-- On a runtime certified at `P0` against the exported contract, every call that succeeds keeps
    the sum of the balances of the holders `S` equal to the supply, as `call_conserves`
    states. -/
theorem call_keeps (hR : RefinesOn .P0 runtime Exported.contract CalldataFits)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256}
    (hcode : I.code = runtime) (hfits : CalldataFits I)
    (hS : CollisionFree S) (hcall : Covers S I) (hcons : Conserved I.codeOwner σ S)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  (hR σ σ₀ g A I ByteArray.empty (by rw [hcode, ByteArray.append_empty]) rfl hfits).accounts
    (P := (Conserved I.codeOwner · S))
    (fun _ _ _ hw => Exported.runtime_conserves (by simp [World.init, UInt256.size]) hfits hS
      hcall hcons hw) hrun

/-- A deployment of a creation bytecode certified at `P0` against the exported contract, with
    one argument word, that succeeds makes the sum of the balances of the holders `S` equal to
    the supply, as `deploy_conserves` states. -/
theorem deploy_keeps (hD : RefinesDeploy .P0 creation runtime Exported.contract
      (fun args => ∃ v : UInt256, args = ctorTail v))
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256} {v : UInt256}
    (hcode : I.code = creation ++ v.toByteArray) (hperm : I.perm = true)
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner σ a = ⟨0⟩)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  hD.accounts (P := (Conserved I.codeOwner · S)) ⟨v, rfl⟩
    (by rw [Exported.ctorTail_eq]; exact hcode) hperm
    (fun _ _ _ hw => Exported.init_keeps (by simp [World.init, UInt256.size]) hS hdeployer
      hzero hw) hrun

end Certified

/-- On the deployed bytecode, every call that succeeds keeps the sum of the balances of the
    holders `S` equal to the supply, when the holders' balance slots do not collide, the holders
    cover the call (`Covers`: it moves tokens between holders only and writes no allowance slot
    that is a balance slot or the supply slot), and its calldata is shorter than `2 ^ 64`
    bytes. -/
theorem call_conserves {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256}
    (hcode : I.code = feERC20Bytecode) (hfits : CalldataFits I)
    (hS : CollisionFree S) (hcall : Covers S I) (hcons : Conserved I.codeOwner σ S)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  call_keeps Exported.feERC20RefinesExported hcode hfits hS hcall hcons hrun

/-- A deployment of the creation bytecode with one argument word `v` that succeeds makes the
    sum of the balances of the holders `S` equal to the supply, when the holders' balance slots
    do not collide, the deployer is one of them, and each starts with none. -/
theorem deploy_conserves {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256} {v : UInt256}
    (hcode : I.code = feERC20CreationBytecode ++ v.toByteArray) (hperm : I.perm = true)
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner σ a = ⟨0⟩)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  deploy_keeps Exported.feERC20DeployRefinesExported hcode hperm hS hdeployer hzero hrun

/-- `call_conserves` for the bytecode of `P1/`. -/
theorem P1.call_conserves {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256}
    (hcode : I.code = feERC20P1Bytecode) (hfits : CalldataFits I)
    (hS : CollisionFree S) (hcall : Covers S I) (hcons : Conserved I.codeOwner σ S)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  call_keeps Sonatina.feERC20RefinesExportedP1.toP0 hcode hfits hS hcall hcons hrun

/-- `deploy_conserves` for the bytecode of `P1/`. -/
theorem P1.deploy_conserves {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {o : ByteArray} {S : List UInt256} {v : UInt256}
    (hcode : I.code = feERC20P1CreationBytecode ++ v.toByteArray) (hperm : I.perm = true)
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner σ a = ⟨0⟩)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I.codeOwner σ' S :=
  deploy_keeps Sonatina.feERC20DeployRefinesExportedP1.toP0 hcode hperm hS hdeployer hzero hrun

end FeProofs.ERC20
