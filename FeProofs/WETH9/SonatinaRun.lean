import FeProofs.WETH9.Sonatina
import FeProofs.WETH9.ExportedStd
import Fe.Sonatina.Run

/-!
# FeWETH9's machine IR, run

The callees of the runtime section's machine IR, one lemma each from any world, for `ir_step` to
use at every call site (`Fe/Sonatina/Run.lean`): `deposit_run` for `%deposit`, which `deposit()`
and the fallback call.

The machine IR keeps a map's key and root in its arena, at 160 and 192, which lie above the
memory a call starts with; `pair_slot_gap` hashes them to `mapSlot` whatever the memory's size.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The caller's address word, as `evm_caller` gives it. -/
abbrev callerWord : UInt256 := UInt256.ofNat I.source.val

/-- The machine IR's arena after it stores a map's key at 160 and its root at 192. -/
abbrev arenaKey (mem : ByteArray) (key root : UInt256) : ByteArray :=
  root.toByteArray.write 0 (key.toByteArray.write 0 mem 160 32) 192 32

/-- `%deposit`: the caller's balance, at `mapSlot caller 3`, grows by the call's value, and a
    `Deposit` log with the value as data follows.  Under a static call the store fails. -/
theorem deposit_run (hf : m.func? "deposit" = some depositFunc) :
    (runFunc m ic "deposit" []).exec I w =
      if I.perm then
        some (.ok ([], { w with
          accounts := storeWord I.codeOwner w.accounts (mapSlot (callerWord I) (UInt256.ofNat 3))
            (slotWord I w.accounts (mapSlot (callerWord I) (UInt256.ofNat 3)) + I.weiValue)
          logs := w.logs.push ⟨I.codeOwner, #[Exported.depositSig, callerWord I],
            I.weiValue.toByteArray⟩
          memory := I.weiValue.toByteArray.write 0 (arenaKey (arenaKey w.memory (callerWord I)
            (UInt256.ofNat 3)) (callerWord I) (UInt256.ofNat 3)) 160 32 }))
      else some (.error .static) := by
  rw [runFunc_entry hf rfl]
  simp [Fe.Sonatina.bind]
  by_cases hp : I.perm = true
  · ir_step [pair_slot_gap, word_read_gap, hp]
  · ir_step [pair_slot_gap, word_read_gap, hp]

end FeProofs.WETH9.Sonatina
