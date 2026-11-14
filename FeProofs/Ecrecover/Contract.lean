import FeProofs.Ecrecover.Recover
import FeProofs.Ecrecover.Main
import FeProofs.Lib.ExportedCorrect

/-!
# Ecrecover: the contract

The exported runtime entry on a call of `recover(e, v, r, s)`, against
`Ethereum.Secp256k1.Spec.recover`.

- `decodeRecover_exec`: std's decoder gives the four words at offsets 4, 36, 68 and 100, or reverts
  with no data on calldata shorter than 132 bytes.
- `arm_spec`: the arm `recv0_arm0`, on any arguments, diverges or returns, with the world
  unchanged, the triple `Spec.recover` decides (`tripleOf`): `(true, x, y)` for the key `(x, y)`,
  `(false, 0, 0)` for none.  `lib.fe` checks `recovery_id > 1`, `r == 0`, `r >= N`, `s == 0`
  and `s >= N` before it calls `secp256k1::recover`, which requires them: they are the
  specification's own guard, so the statement needs no hypothesis.
- `FeProofs.Lib.returnTriple_exec`: std's `return_value` of the triple stops with its 96-byte ABI
  encoding (`encodeTriple`), changing memory only.
- `feEcrecoverContractCorrect`: on the calldata `calldata e v r s` of `Main.lean` (the selector,
  then the four words) and no call value, the runtime entry diverges or stops with the encoding
  of what `Spec.recover` decides, changing memory only.  `runtime_short`, `runtime_other` and
  `runtime_value`: shorter calldata, another selector, or call value revert with no data.
- `recover_main`: `Main.lean`'s `recover`, the stand-in for ECDSARECOVER that EVMLean runs,
  prints the key `x ‖ y` exactly when `Spec.recover` gives `(x, y)`, or does not terminate.

Divergence is left open: the model does not terminate only if the variable-time inversion does
not, whose termination is not proved; on the bytecode that is running out of gas.

## The precompile

`Spec.ecrecover d`, the ECRECOVER precompile, reads `v` from the call data and accepts only 27
and 28, passing `v - 27` as the recovery id; it returns the address of the key, the last 20 bytes
of the Keccak-256 hash of `x ‖ y`, left-padded, or nothing.  The contract takes the recovery id
itself (0 or 1, anything else giving `(false, 0, 0)`) and returns the key `(ok, x, y)`, not its
address.  So the contract on `(e, v - 27, r, s)` gives `ecrecover` on `(e, v, r, s)` for `v` in
`{27, 28}` after hashing `x ‖ y` and cutting the address; that step is not stated here.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open scoped FeProofs.Lib

namespace FeProofs.Ecrecover

open Exported

attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeRecover_exec (I : ExecutionEnv) (w : World) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    decode_runtime_args_Evm_Sol_Recover.exec I w =
      if I.calldata.size < 132 then some (.error (.revert ByteArray.empty))
      else some (.ok (⟨word I.calldata 4, word I.calldata 36, word I.calldata 68,
        word I.calldata 100⟩, w)) := by
  have hshort : I.calldata.size - 4 < 128 ↔ I.calldata.size < 132 := by omega
  have hhead : Recover_HEAD_SIZE = pure (UInt256.ofNat 128) := rfl
  have o36 : UInt256.ofNat 4 + UInt256.ofNat 32 = UInt256.ofNat 36 := rfl
  have o68 : UInt256.ofNat 36 + UInt256.ofNat 32 = UInt256.ofNat 68 := rfl
  have o100 : UInt256.ofNat 68 + UInt256.ofNat 32 = UInt256.ofNat 100 := rfl
  have t36 : (UInt256.ofNat 36).toNat = 36 := rfl
  have t68 : (UInt256.ofNat 68).toNat = 68 := rfl
  have t100 : (UInt256.ofNat 100).toNat = 100 := rfl
  have z36 : UInt256.ofNat 0 + UInt256.ofNat 36 = UInt256.ofNat 36 := rfl
  have z68 : UInt256.ofNat 0 + UInt256.ofNat 68 = UInt256.ofNat 68 := rfl
  have z100 : UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 := rfl
  have ne128 : UInt256.ofNat 128 ≠ UInt256.ofNat 0 := by decide
  simp [decode_runtime_args_Evm_Sol_Recover, decode_from_prechecked_head_Recover_Sol_CallData,
    Recover_decode_from_CallData, hhead, checkedAdd, checkedSub, toNat0, toNat32, toNat4,
    truncate_size _ hfits, o36, o68, o100, t36,
    t68, t100, z36, z68, z100, ne128, UInt256.size, at4,
    headCheck hlo hfits (by norm_num : 128 < 2 ^ 64), hshort]
  by_cases h : I.calldata.size < 132 <;> simp [h, word]

/-! ## The arm -/

/-- What the arm returns for what the specification decides: the key after `true`, or `false`
    and zeros. -/
def tripleOf : Option (Fp × Fp) → Bool × UInt256 × UInt256
  | none => (false, UInt256.ofNat 0, UInt256.ofNat 0)
  | some (x, y) => (true, UInt256.ofNat x.val, UInt256.ofNat y.val)

/-- **The arm `recover`**, on any arguments: it diverges, or returns, with the world unchanged,
    what `Spec.recover` decides.  The arm's own checks of the recovery id, `r` and `s` are the
    specification's guard. -/
theorem arm_spec (e v r s : UInt256) (env : Env) (w : World) :
    (recv0_arm0 e v r s).exec env w = none ∨
      (recv0_arm0 e v r s).exec env w =
        some (.ok (tripleOf (Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat), w)) := by
  have hn : (UInt256.ofNat Secp256k1.n).toNat = Secp256k1.n :=
    toNat_lit (show Secp256k1.n < 2 ^ 256 by decide)
  have t1 : (UInt256.ofNat 1).toNat = 1 := rfl
  have hspec : ¬ (0 < r.toNat ∧ r.toNat < Secp256k1.n ∧ 0 < s.toNat ∧ s.toNat < Secp256k1.n ∧
      v.toNat < 2) → Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat = none := fun hg => by
    rw [Secp256k1.Spec.recover, if_neg hg]
  have h0 : ∀ x : UInt256, x = UInt256.ofNat 0 ↔ x.toNat = 0 := fun x =>
    ⟨fun h => by rw [h]; rfl, fun h => u256_inj (by rw [h]; rfl)⟩
  by_cases hv : 1 < v.toNat
  · right
    rw [hspec (by omega)]
    simp [recv0_arm0, t1, hv, tripleOf]
  by_cases hr0 : r = UInt256.ofNat 0
  · right
    rw [hspec (by rw [(h0 r).mp hr0]; omega)]
    simp [recv0_arm0, t1, hv, hr0, tripleOf]
  by_cases hr : Secp256k1.n ≤ r.toNat
  · right
    rw [hspec (by omega)]
    simp [recv0_arm0, t1, hv, hr0, N_eq, hn, hr, tripleOf]
  by_cases hs0 : s = UInt256.ofNat 0
  · right
    rw [hspec (by rw [(h0 s).mp hs0]; omega)]
    simp [recv0_arm0, t1, hv, hr0, N_eq, hs0, tripleOf]
  by_cases hs : Secp256k1.n ≤ s.toNat
  · right
    rw [hspec (by omega)]
    simp [recv0_arm0, t1, hv, hr0, N_eq, hn, hs0, hs, tripleOf]
  have hr0' : 0 < r.toNat := Nat.pos_of_ne_zero fun h => hr0 ((h0 r).mpr h)
  have hs0' : 0 < s.toNat := Nat.pos_of_ne_zero fun h => hs0 ((h0 s).mpr h)
  rcases recover_spec e v r s (by omega) hr0' (by omega) hs0' (by omega) env w with h | h
  · left
    simp [recv0_arm0, t1, hv, hr0, N_eq, hn, hr, hs0, hs, h]
  · right
    simp [recv0_arm0, t1, hv, hr0, N_eq, hn, hr, hs0, hs, h]
    rcases Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat with _ | ⟨x, y⟩ <;>
      simp [keyOf, tripleOf, Option_PublicKey.Some_0]

/-! ## The calldata of `recover(e, v, r, s)` -/

/-- The word of `A ++ x ++ B` at the end of `A` is `x`. -/
theorem word_append (A B : ByteArray) (x : UInt256) :
    word (A ++ x.toByteArray ++ B) A.size = x := by
  have hx := toByteArray_size (v := x)
  have h : (A ++ x.toByteArray ++ B).readBytes A.size 32 = x.toByteArray := by
    apply ByteArray.ext
    apply Array.ext'
    rw [readBytes_at_toList_any _ _ (by simp [ByteArray.size_append, hx])]
    have hd : x.toByteArray.data.size = 32 := hx
    have hl : x.toByteArray.data.toList.length = 32 := by rw [Array.length_toList, hd]
    simp [ByteArray.data_append, Array.toList_append, hd]
  rw [word, h, uInt256OfByteArray_toByteArray]

/-- The selector of `recover(uint256,uint256,uint256,uint256)`. -/
def recoverSelector : ByteArray := ⟨#[0x2a, 0xa6, 0xd3, 0x51]⟩

/-- Its four bytes are those of the signature's Keccak-256 hash, which `calldata` computes. -/
theorem recoverSelector_eq :
    (KEC "recover(uint256,uint256,uint256,uint256)".toUTF8).extract 0 4 = recoverSelector := by
  decide +kernel

theorem calldata_eq (e v r s : UInt256) :
    calldata e.toNat v.toNat r.toNat s.toNat =
      recoverSelector ++ e.toByteArray ++ v.toByteArray ++ r.toByteArray ++ s.toByteArray := by
  simp only [calldata, List.foldl_cons, List.foldl_nil, u256_ofNat_toNat, recoverSelector_eq]

theorem calldata_facts (e v r s : UInt256) :
    let cd := calldata e.toNat v.toNat r.toNat s.toNat
    cd.size = 132 ∧ cd.extract 0 4 = recoverSelector ∧ word cd 4 = e ∧ word cd 36 = v ∧
      word cd 68 = r ∧ word cd 100 = s := by
  intro cd
  have hs := fun x : UInt256 => toByteArray_size (v := x)
  have hsel : recoverSelector.size = 4 := rfl
  have hcd : cd = _ := calldata_eq e v r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcd]; simp [ByteArray.size_append, hs, hsel]
  · rw [hcd, ByteArray.append_assoc, ByteArray.append_assoc, ByteArray.append_assoc]
    rw [ByteArray.extract_append_eq_left hsel]
  · have h : cd = recoverSelector ++ e.toByteArray ++ (v.toByteArray ++ r.toByteArray ++
        s.toByteArray) := by rw [hcd]; simp only [ByteArray.append_assoc]
    rw [h]; exact word_append _ _ e
  · have h : cd = (recoverSelector ++ e.toByteArray) ++ v.toByteArray ++ (r.toByteArray ++
        s.toByteArray) := by rw [hcd]; simp only [ByteArray.append_assoc]
    rw [h, show 36 = (recoverSelector ++ e.toByteArray).size by
      simp [ByteArray.size_append, hs, hsel]]
    exact word_append _ _ v
  · have h : cd = (recoverSelector ++ e.toByteArray ++ v.toByteArray) ++ r.toByteArray ++
        s.toByteArray := by rw [hcd]
    rw [h, show 68 = (recoverSelector ++ e.toByteArray ++ v.toByteArray).size by
      simp [ByteArray.size_append, hs, hsel]]
    exact word_append _ _ r
  · have h : cd = (recoverSelector ++ e.toByteArray ++ v.toByteArray ++ r.toByteArray) ++
        s.toByteArray ++ ByteArray.empty := by rw [hcd, ByteArray.append_empty]
    rw [h, show 100 = (recoverSelector ++ e.toByteArray ++ v.toByteArray ++ r.toByteArray).size by
      simp [ByteArray.size_append, hs, hsel]]
    exact word_append _ _ s

/-! ## The contract -/

/-- The 96-byte ABI encoding of `(bool, u256, u256)`. -/
def encodeTriple (t : Bool × UInt256 × UInt256) : ByteArray :=
  (Bool.toUInt256 t.1).toByteArray ++ t.2.1.toByteArray ++ t.2.2.toByteArray

theorem runtime_recover (e v r s : UInt256) (I : ExecutionEnv) (w : World)
    (hcd : I.calldata = calldata e.toNat v.toNat r.toNat s.toNat) :
    runtime.exec I w = recv0_arm0_entry.exec I w := by
  obtain ⟨hsz, hext, -⟩ := calldata_facts e v r s
  rw [← hcd] at hsz hext
  have hsel : selWord I.calldata = UInt256.ofNat 0x2aa6d351 :=
    selWord_hit (evmSelectorDecode (by omega) 0x2a 0xa6 0xd3 0x51 (UInt256.ofNat 0x2aa6d351)
      (by decide)) (by rw [hext]; rfl)
  have h132 : (UInt256.ofNat I.calldata.size).toNat = 132 := by rw [hsz]; rfl
  simp [runtime, h132, selector_exec, hsel]

/-- **The contract `Ecrecover` recovers what the specification does.**  On a call of
    `recover(e, v, r, s)` without value, the exported runtime entry does not terminate, or stops
    with the ABI encoding of `(true, x, y)` when `Spec.recover` gives the key `(x, y)` and of
    `(false, 0, 0)` when it gives none, changing memory only. -/
theorem feEcrecoverContractCorrect (e v r s : UInt256) (I : ExecutionEnv) (w : World)
    (hcd : I.calldata = calldata e.toNat v.toNat r.toNat s.toNat) (hv : I.weiValue = ⟨0⟩)
    (hmem : w.memory.size + 96 < UInt256.size) :
    (entry runtime).exec I w = none ∨
      ∃ memory, (entry runtime).exec I w = some (.error (.stop
        (encodeTriple (tripleOf (Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat)))
        { w with memory := memory })) := by
  obtain ⟨hsz, -, h4, h36, h68, h100⟩ := calldata_facts e v r s
  rw [← hcd] at hsz h4 h36 h68 h100
  have hdec := decodeRecover_exec I w (by omega) (by omega)
  rw [if_neg (by omega), h4, h36, h68, h100] at hdec
  rcases arm_spec e v r s I w with harm | harm
  · left
    simp [entry, runtime_recover e v r s I w hcd, recv0_arm0_entry, exec_nonPayable, hv, hdec,
      harm]
  · right
    obtain ⟨memory, hret⟩ := FeProofs.Lib.returnTriple_exec I w
      (tripleOf (Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat)) hmem
    refine ⟨memory, ?_⟩
    simp only [entry, M.exec_bind, runtime_recover e v r s I w hcd, recv0_arm0_entry,
      exec_nonPayable, hv, if_true, hdec, harm, hret, encodeTriple]

/-- Other calls revert with no data: calldata shorter than a selector, a selector other than
    `recover`'s, or call value sent. -/
theorem runtime_short (I : ExecutionEnv) (w : World) (h : I.calldata.size < 4) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  apply entry_exec
  simp [runtime, hn, h]

theorem runtime_other (I : ExecutionEnv) (w : World) (h4 : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < UInt256.size)
    (hsel : (recoverSelector == I.calldata.extract 0 4) = false) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := ulit_toNat' _ hfits
  have hw : selWord I.calldata ≠ UInt256.ofNat 0x2aa6d351 :=
    selWord_miss (evmSelectorDecode h4 0x2a 0xa6 0xd3 0x51 (UInt256.ofNat 0x2aa6d351) (by decide))
      hsel
  apply entry_exec
  simp [runtime, hn, Nat.not_lt.mpr h4, selector_exec, hw]

theorem runtime_value (e v r s : UInt256) (I : ExecutionEnv) (w : World)
    (hcd : I.calldata = calldata e.toNat v.toNat r.toNat s.toNat) (hv : I.weiValue ≠ ⟨0⟩) :
    (entry runtime).exec I w = some (.error (.revert ByteArray.empty)) := by
  apply entry_exec
  rw [runtime_recover e v r s I w hcd]
  rw [recv0_arm0_entry, M.exec_bind, exec_nonPayable, if_neg hv]

/-- **What `Main.lean` prints.**  The stand-in for ECDSARECOVER returns the key `x ‖ y` exactly
    when `Spec.recover` gives `(x, y)`, and none when it gives none, or the model does not
    terminate. -/
theorem recover_main (e v r s : UInt256) :
    FeProofs.Ecrecover.recover e.toNat v.toNat r.toNat s.toNat = .error "does not terminate" ∨
      FeProofs.Ecrecover.recover e.toNat v.toNat r.toNat s.toNat =
        .ok ((Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat).map fun k =>
          (UInt256.ofNat k.1.val).toByteArray ++ (UInt256.ofNat k.2.val).toByteArray) := by
  have hs := fun x : UInt256 => toByteArray_size (v := x)
  rcases feEcrecoverContractCorrect e v r s
      { (default : ExecutionEnv) with calldata := calldata e.toNat v.toNat r.toNat s.toNat }
      (World.init ∅ default) rfl rfl (by simp [World.init, UInt256.size]) with h | ⟨memory, h⟩
  · left
    simp only [FeProofs.Ecrecover.recover, h]
  · right
    simp only [FeProofs.Ecrecover.recover, h]
    rcases Secp256k1.Spec.recover e.toNat v.toNat r.toNat s.toNat with _ | ⟨x, y⟩
    · simp [tripleOf, encodeTriple, ByteArray.size_append, hs, Bool.toUInt256,
        ByteArray.append_assoc, ByteArray.extract_append_eq_left (hs _).symm,
        fromByteArrayBigEndian_toByteArray, toNat0]
    · simp [tripleOf, encodeTriple, ByteArray.size_append, hs, Bool.toUInt256,
        ByteArray.append_assoc, ByteArray.extract_append_eq_left (hs _).symm,
        ByteArray.extract_append_eq_right (hs _).symm, fromByteArrayBigEndian_toByteArray,
        show (UInt256.ofNat 1).toNat = 1 from rfl]

end FeProofs.Ecrecover
