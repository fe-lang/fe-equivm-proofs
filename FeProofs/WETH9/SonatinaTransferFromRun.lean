import FeProofs.WETH9.SonatinaTransferFrom

/-!
# FeWETH9's `%transfer_from` when it spends an allowance

The cases `SonatinaTransferFrom.lean` leaves: the caller spends another's tokens from an
allowance below the largest word.  Split from it for the time `ir_step` takes on each path.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The largest word, as the machine IR compares an allowance with it. -/
local notation "maxNat" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639935

set_option maxHeartbeats 4000000 in
/-- `%transfer_from src dst wad` from any world. -/
theorem transferFrom_run (hf : m.func? "transfer_from" = some transferFromFunc)
    (src dst wad : UInt256) : ∃ M,
    (runFunc m ic "transfer_from" [Val.int 256 src.toNat, Val.int 256 dst.toNat,
      Val.int 256 wad.toNat]).exec I w = tfOut I w src dst wad M := by
  by_cases hb : (slotWord I w.accounts (mapSlot src (UInt256.ofNat 3))).toNat < wad.toNat
  · exact transferFrom_run_noSpend ic I w hf src dst wad (.inl hb)
  by_cases hs : src.toNat = (callerWord I).toNat
  · exact transferFrom_run_noSpend ic I w hf src dst wad (.inr (.inl hs))
  by_cases hm : (slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot src (UInt256.ofNat 4)))).toNat = maxNat
  · exact transferFrom_run_noSpend ic I w hf src dst wad (.inr (.inr hm))
  have hs' : ¬ src.toNat = (I.source : Nat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [callerWord, Check.toNat_ofNat, UInt256.size] using hs
  rw [runFunc_entry hf rfl]
  simp only [Fe.Sonatina.bind, transferFromFunc.params_eq]
  by_cases ha : (slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot src (UInt256.ofNat 4)))).toNat < wad.toNat
  · refine ⟨.empty, ?_⟩
    simp [tfOut, hb, hs, hm, ha]
    repeat ir_step [pair_slot_gap, word_read_gap, hb, hs', hm, ha]
  by_cases hp : I.perm = true
  · refine Exists.intro ?M3 ?h3
    case h3 =>
      simp [tfOut, hb, hs, hm, ha, hp]
      repeat ir_step [pair_slot_gap, word_read_gap, hb, hs', hm, ha, hp]
      rfl
  · refine ⟨.empty, ?_⟩
    simp [tfOut, hb, hs, hm, ha, hp]
    repeat ir_step [pair_slot_gap, word_read_gap, hb, hs', hm, ha, hp]

/-- The memory `%transfer_from` leaves, chosen.  A definition of its own, so that `simp` does
    not rewrite inside the predicate the choice is of. -/
noncomputable def tfMem (hf : m.func? "transfer_from" = some transferFromFunc)
    (src dst wad : UInt256) : ByteArray :=
  (transferFrom_run ic I w hf src dst wad).choose

/-- `%transfer_from` as a rewrite for `ir_step` at its call sites. -/
theorem transferFrom_eq (hf : m.func? "transfer_from" = some transferFromFunc)
    (src dst wad : UInt256) :
    (runFunc m ic "transfer_from" [Val.int 256 src.toNat, Val.int 256 dst.toNat,
      Val.int 256 wad.toNat]).exec I w = tfOut I w src dst wad (tfMem ic I w hf src dst wad) :=
  (transferFrom_run ic I w hf src dst wad).choose_spec

end FeProofs.WETH9.Sonatina
