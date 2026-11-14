import FeProofs.ERC20.Sonatina
import FeProofs.ERC20.ExportedStd
import Fe.Sonatina.Run

/-!
# FeERC20's machine IR, run
-/

namespace FeProofs.ERC20.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The selector as the machine IR computes it. -/
abbrev sel : Nat := (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224

theorem ir_short (h : I.calldata.size < 4) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  have h' : I.calldata.size % UInt256.size = I.calldata.size :=
    Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  simp only [UInt256.size] at h'
  repeat ir_step

set_option maxHeartbeats 4000000 in
/-- The dispatcher: on a selector of the table, the run goes on at the arm's entry block. -/
theorem ir_dispatch (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) {k b : Nat}
    (hk : (k, b) ∈ [(0x095ea7b3, 5), (0x18160ddd, 12), (0x23b872dd, 15), (0x70a08231, 33),
      (0xa9059cbb, 40), (0xdd62ed3e, 54)]) (hsel : sel I = k) :
    ∃ E p, (runBlocks m ic runtimeFunc ∅ none 0).exec I w =
      (runBlocks m ic runtimeFunc E p b).exec I w := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold sel at hsel
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, _, by ir_step; ir_step; ir_step; rfl⟩

set_option maxHeartbeats 4000000 in
/-- A selector of no arm: the machine IR reverts with no data. -/
theorem ir_noMatch (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (h : ∀ k ∈ [0x095ea7b3, 0x18160ddd, 0x23b872dd, 0x70a08231, 0xa9059cbb, 0xdd62ed3e],
      sel I ≠ k) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold sel at h1 h2 h3 h4 h5 h6
  have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3
  have := Ne.symm h4; have := Ne.symm h5; have := Ne.symm h6
  by_cases hl : (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 < 0x70a08231 <;>
    repeat ir_step

end FeProofs.ERC20.Sonatina
