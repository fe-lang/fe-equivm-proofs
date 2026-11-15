import FeProofs.WETH9.Sonatina
import FeProofs.WETH9.ExportedStd
import Fe.Sonatina.Run
import FeProofs.Common.SolString

/-!
# FeWETH9's machine IR, run

The callees of the runtime section's machine IR, one lemma each from any world, for `ir_step` to
use at every call site (`Fe/Sonatina/Run.lean`): `deposit_run` for `%deposit`, which `deposit()`
and the fallback call, `revertError_run` and `storedLen_run` for the callees of `%load`.

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

/-- `%revert_error c`: `Panic(c)`, its payload stored in the arena at 224. -/
theorem revertError_run (hf : m.func? "revert_error" = some revertErrorFunc) {c : Nat}
    (hc : c < 2 ^ 256) :
    (runFunc m ic "revert_error" [Val.int 256 c]).exec I w =
      some (.error (.revert (panicData c))) := by
  have hc' : c % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = c := Nat.mod_eq_of_lt hc
  rw [runFunc_entry hf rfl]
  simp [Fe.Sonatina.bind]
  ir_step [panic_read_gap, hc']

open Stele (solidityDecodeBytesLengthHeader) in
/-- `%stored_len head`: the length a string head encodes, as Stele decodes it, or
    `Panic(0x22)` when the length contradicts the short/long flag. -/
theorem storedLen_run (hf : m.func? "stored_len" = some storedLenFunc)
    (hr : m.func? "revert_error" = some revertErrorFunc) (head : UInt256) :
    (runFunc m ic "stored_len" [Val.int 256 head.toNat]).exec I w =
      match solidityDecodeBytesLengthHeader head with
      | .ok L => some (.ok ([Val.int 256 L], w))
      | _ => some (.error (.revert (panicData 0x22))) := by
  have hh := head.val.isLt
  change head.toNat < 2 ^ 256 at hh
  have e1 : head.toNat &&& 1 = head.toNat % 2 := Nat.and_one_is_mod _
  have e2 : head.toNat &&& 255 = head.toNat % 256 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  have e3 : ∀ x : Nat, x >>> 1 = x / 2 := fun x => by rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hm2 : head.toNat % 256 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 := Nat.mod_eq_of_lt (by omega)
  rw [runFunc_entry hf rfl]
  simp [Fe.Sonatina.bind]
  rcases decodeHeader_cases head with ⟨ho, hge, hok⟩ | ⟨he, hlt, hok⟩ | ⟨hbad, hrev⟩
  · rw [hok]
    have : ¬ head.toNat / 2 < 32 := by omega
    have hm : head.toNat / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat / 2 := Nat.mod_eq_of_lt (by omega)
    repeat ir_step [e1, e2, e3, ho, this, hm]
  · rw [hok]
    have hm : head.toNat % 256 / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 / 2 := Nat.mod_eq_of_lt (by omega)
    repeat ir_step [e1, e2, e3, he, hlt, hm, hm2]
  · rw [hrev]
    rcases hbad with ⟨ho, hlt⟩ | ⟨he, hge⟩
    · have hm : head.toNat / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      repeat ir_step [e1, e2, e3, ho, hlt, hm, revertError_run ic I _ hr (c := 34) (by decide)]
    · have hm : head.toNat % 256 / 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = head.toNat % 256 / 2 := Nat.mod_eq_of_lt (by omega)
      have : ¬ head.toNat % 256 / 2 < 32 := by omega
      repeat ir_step [e1, e2, e3, he, this, hm, hm2, revertError_run ic I _ hr (c := 34) (by decide)]

end FeProofs.WETH9.Sonatina
