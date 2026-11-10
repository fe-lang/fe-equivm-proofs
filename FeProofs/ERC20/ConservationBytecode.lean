import FeProofs.ERC20.Conservation
import FeProofs.ERC20.ModelCorrect

/-!
# FeERC20: conservation, stated on the bytecode

A successful `transfer` call to the deployed bytecode keeps the holders' balances equal to the
supply.  The statement mentions the bytecode and the EVM semantics; the model appears only in the
proof.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.ERC20

/-- A successful run of the `transfer` entry arm is a successful run of `transfer`. -/
theorem transferArm_ok {I : ExecutionEnv} {w w' : World} {cd out : ByteArray}
    (h : (Model.transferArm cd).exec I w = some (.ok (out, w'))) :
    ∃ r, (Model.transfer (word cd 4) (word cd 36)).exec I w = some (.ok (r, w')) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [Model.transferArm, exec_nonPayable, hwv] at h
  by_cases hhead : BadHead cd 2
  · simp [Model.transferArm, exec_nonPayable, hwv, hhead] at h
  by_cases haddr : NotAddress (word cd 4)
  · simp [Model.transferArm, exec_nonPayable, hwv, hhead, haddr] at h
  simp only [Model.transferArm, M.exec_bind, exec_nonPayable, hwv, if_true, hhead, haddr,
    if_false, M.exec_pure, M.exec_map] at h
  cases ht : (Model.transfer (word cd 4) (word cd 36)).exec I w with
  | none => simp [ht] at h
  | some res =>
    cases res with
    | error f => simp [ht] at h
    | ok p =>
      obtain ⟨r, w''⟩ := p
      simp [ht] at h
      exact ⟨r, by rw [h.2]⟩

/-- The `transfer` entry arm returns or fails; it never stops the run from inside. -/
theorem transferArm_noStop (cd : ByteArray) : (Model.transferArm cd).NoStop := by
  unfold Model.transferArm Model.transfer
  no_stop

/-- On the deployed bytecode: a `transfer` call that succeeds keeps the sum of the balances of
    the holders `S` equal to the supply, when the caller and the recipient are in `S`, the
    balance slots of `S` do not collide, and the contract's account exists. -/
theorem transfer_conserves_bytecode {σ σ₀ σ' : AccountMap} {A A' : Substate} {I : ExecutionEnv}
    {g g' : UInt256} {o : ByteArray} {acc : Account} {S : List UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 4))
    (hacc : σ.get? I.codeOwner = some acc) (hS : CollisionFree S)
    (hsender : UInt256.ofNat I.source.val ∈ S) (hdst : word I.calldata 4 ∈ S)
    (hcons : Conserved I σ S)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    Conserved I σ' S := by
  rcases transferArm_refines (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsize hsel with hoog | hag
  · rw [hrun] at hoog; cases hoog
  cases hm : (Model.transferArm I.calldata).exec I (World.init σ A) with
  | none => rw [hm] at hag; exact hag.elim
  | some res =>
    rw [hm] at hag
    cases res with
    | error f =>
      cases f with
      | revert data => obtain ⟨_, _, h, _⟩ := hag; rw [hrun] at h; cases h
      | panic code => obtain ⟨_, _, h, _⟩ := hag; rw [hrun] at h; cases h
      | static => rw [hrun] at hag; cases hag
      | stop out w' => exact absurd hm (transferArm_noStop _ _ _ _ _)
    | ok p =>
      obtain ⟨out, w'⟩ := p
      obtain ⟨g'', A'', h, _⟩ := hag
      rw [hrun] at h
      have hσ : σ' = w'.accounts := by injection h with h; injection h with h; injection h with h
      obtain ⟨r, ht⟩ := transferArm_ok hm
      rw [hσ]
      exact transfer_conserves (w := World.init σ A) hacc hS hsender hdst hcons ht

end FeProofs.ERC20
