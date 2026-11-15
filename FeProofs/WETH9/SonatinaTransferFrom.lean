import FeProofs.WETH9.SonatinaRun

/-!
# FeWETH9's `%transfer_from`, run

`transfer` and `transferFrom` call it.  `tfOut` is what it ends with: `Panic(1)` on a short
balance, or on a short allowance when the caller spends another's tokens and the allowance is
not the largest word; otherwise the allowance falls by `wad` (when spent), the source's balance
falls by `wad` and the destination's grows by it, each read again after the store before it, and
the `Transfer` log follows.  The memory it leaves, its arena, is left as an `M`.
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

/-- What `%transfer_from src dst wad` ends with, its memory left as `M`. -/
def tfOut (src dst wad : UInt256) (M : ByteArray) :
    Option (Except (Exit World) (List Val × World)) :=
  let bal := slotWord I w.accounts (mapSlot src (UInt256.ofNat 3))
  let aslot := mapSlot (callerWord I) (mapSlot src (UInt256.ofNat 4))
  let al := slotWord I w.accounts aslot
  let spends := src.toNat ≠ (callerWord I).toNat ∧ al.toNat ≠ maxNat
  if bal.toNat < wad.toNat then some (.error (.revert (panicData 1)))
  else if spends ∧ al.toNat < wad.toNat then some (.error (.revert (panicData 1)))
  else if I.perm then
    let σ1 := if spends then storeWord I.codeOwner w.accounts aslot
      (UInt256.sub (slotWord I w.accounts aslot) wad) else w.accounts
    let σ2 := storeWord I.codeOwner σ1 (mapSlot src (UInt256.ofNat 3))
      (UInt256.sub (slotWord I σ1 (mapSlot src (UInt256.ofNat 3))) wad)
    let σ3 := storeWord I.codeOwner σ2 (mapSlot dst (UInt256.ofNat 3))
      (slotWord I σ2 (mapSlot dst (UInt256.ofNat 3)) + wad)
    some (.ok ([Val.int 256 1], { w with
      accounts := σ3
      logs := w.logs.push ⟨I.codeOwner, #[Exported.transferSig, src, dst], wad.toByteArray⟩
      memory := M }))
  else some (.error .static)

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
/-- `%transfer_from src dst wad` from any world, when it spends no allowance: the balance is
    short, the caller is the source, or the allowance is the largest word. -/
theorem transferFrom_run_noSpend (hf : m.func? "transfer_from" = some transferFromFunc)
    (src dst wad : UInt256)
    (hcase : (slotWord I w.accounts (mapSlot src (UInt256.ofNat 3))).toNat < wad.toNat ∨
      src.toNat = (callerWord I).toNat ∨
      (slotWord I w.accounts (mapSlot (callerWord I) (mapSlot src (UInt256.ofNat 4)))).toNat =
        maxNat) : ∃ M,
    (runFunc m ic "transfer_from" [Val.int 256 src.toNat, Val.int 256 dst.toNat,
      Val.int 256 wad.toNat]).exec I w = tfOut I w src dst wad M := by
  rw [runFunc_entry hf rfl]
  simp only [Fe.Sonatina.bind, transferFromFunc.params_eq]
  by_cases hb : (slotWord I w.accounts (mapSlot src (UInt256.ofNat 3))).toNat < wad.toNat
  · refine ⟨.empty, ?_⟩
    simp [tfOut, hb]
    repeat ir_step [pair_slot_gap, word_read_gap, hb]
  by_cases hs : src.toNat = (callerWord I).toNat
  · obtain rfl : src = callerWord I := Check.eq_of_toNat hs
    by_cases hp : I.perm = true
    · refine Exists.intro ?M1 ?h1
      case h1 =>
        simp [tfOut, hb, hp]
        repeat ir_step [pair_slot_gap, word_read_gap, hb, hp]
        rfl
    · refine ⟨.empty, ?_⟩
      simp [tfOut, hb, hp]
      repeat ir_step [pair_slot_gap, word_read_gap, hb, hp]
  have hs' : ¬ src.toNat = (I.source : Nat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [callerWord, Check.toNat_ofNat, UInt256.size] using hs
  have hm : (slotWord I w.accounts (mapSlot (callerWord I)
      (mapSlot src (UInt256.ofNat 4)))).toNat = maxNat := by omega
  · by_cases hp : I.perm = true
    · refine Exists.intro ?M2 ?h2
      case h2 =>
        simp [tfOut, hb, hs, hm, hp]
        repeat ir_step [pair_slot_gap, word_read_gap, hb, hs', hm, hp]
        rfl
    · refine ⟨.empty, ?_⟩
      simp [tfOut, hb, hs, hm, hp]
      repeat ir_step [pair_slot_gap, word_read_gap, hb, hs', hm, hp]
end FeProofs.WETH9.Sonatina
