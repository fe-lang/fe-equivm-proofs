import FeProofs.Case44Bank.Sonatina
import Fe.Sonatina.Run

/-!
# Case44Bank's machine IR, run

The runtime's internal function `credit` from any world and arguments (`ir_credit`), the lemma
each of its two call sites rewrites with; the dispatcher to the arm's entry block; and the init
function's runs.  The machine IR's `credit` takes the key and the amount: the compiler folded
the map's root, slot 0, into it.
-/

namespace FeProofs.Case44Bank.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

theorem creditFunc_params : creditFunc.params = [(0, .int 256), (1, .int 256)] := rfl

/-- The machine IR's `credit` on the key `a` and the amount `b`, in any module whose `credit`
    it is: `Panic(0x11)` if the entry's word plus `b` overflows, otherwise it stores the sum at
    the entry, which fails under a static call, and returns nothing.  It hashes the key and the
    root at 0 and 32, twice. -/
theorem ir_credit (hm : m.func? "credit" = some creditFunc) (a b : UInt256) :
    (runFunc m ic "credit" [.int 256 a.toNat, .int 256 b.toNat]).exec I w =
      if UInt256.size ≤ (slotWord I w.accounts (mapSlot a ⟨0⟩)).toNat + b.toNat then
        some (.error (.revert (panicData 17)))
      else if I.perm then
        some (.ok ([], { w with
          accounts := storeWord I.codeOwner w.accounts (mapSlot a ⟨0⟩)
            (slotWord I w.accounts (mapSlot a ⟨0⟩) + b)
          memory := (UInt256.ofNat 0).toByteArray.write 0 (a.toByteArray.write 0
            ((UInt256.ofNat 0).toByteArray.write 0 (a.toByteArray.write 0 w.memory 0 32) 32 32)
              0 32) 32 32 }))
      else some (.error .static) := by
  rw [runFunc_entry hm rfl]
  simp [Fe.Sonatina.bind, Val.as, Ty.bits, toNat_mod, creditFunc_params]
  by_cases hover : UInt256.size ≤ (slotWord I w.accounts (mapSlot a ⟨0⟩)).toNat + b.toNat
  · have h' := hover
    simp only [UInt256.size] at h'
    rw [if_pos hover]
    repeat ir_step
  · have h' := hover
    simp only [UInt256.size] at h'
    rw [if_neg hover]
    by_cases hperm : I.perm = true
    · simp only [hperm, if_true]
      repeat ir_step
    · simp only [hperm]
      repeat ir_step

/-- The selector as the machine IR computes it. -/
abbrev sel : Nat := (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224

theorem ir_short (h : I.calldata.size < 4) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  have h' : I.calldata.size % UInt256.size = I.calldata.size :=
    Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  simp only [UInt256.size] at h'
  repeat ir_step

/-- The dispatcher: on the selector of `Credit`, the run goes on at the arm's entry block. -/
theorem ir_dispatch (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (hsel : sel I = 1) :
    ∃ E p, (runBlocks m ic runtimeFunc ∅ none 0).exec I w =
      (runBlocks m ic runtimeFunc E p 5).exec I w := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold sel at hsel
  exact ⟨_, _, by ir_step; ir_step; rfl⟩

/-- Another selector: the machine IR reverts with no data. -/
theorem ir_noMatch (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (h : sel I ≠ 1) :
    (runBlocks m ic runtimeFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold sel at h
  have := Ne.symm h
  repeat ir_step

/-! ## The constructor -/

/-- The constructor with call value: the machine IR reverts with no data. -/
theorem ir_init_value (hwv : I.weiValue ≠ ⟨0⟩) :
    (runBlocks m ic initFunc ∅ none 0).exec I w = some (.error (.revert ByteArray.empty)) := by
  have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
  repeat ir_step

/-- The constructor: the machine IR copies the 176 bytes of code at offset 19 to address 0 and
    returns them. -/
theorem ir_init (hs : ic.symbol "&Case44Bank_runtime" = some (19, 176))
    (hwv : I.weiValue = ⟨0⟩) :
    (runBlocks m ic initFunc ∅ none 0).exec I w = some (.error (.stop
      ((I.code.write 19 w.memory 0 176).readWithPadding 0 176)
      { w with memory := I.code.write 19 w.memory 0 176 })) := by
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  repeat ir_step

end FeProofs.Case44Bank.Sonatina
