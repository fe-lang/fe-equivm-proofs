import FeProofs.WETH9.SonatinaInitRun

/-!
# FeWETH9's constructor against the machine IR

The init section's root stores the free pointer 256, builds `"Wrapped Ether"` at 192 and
`"WETH"` at 256 (the length word, then the bytes' word), stores each with `%store`
(`store_run`), writes 18 into the low byte of slot 2 and returns the runtime code it copies from
its own code.  The exported constructor builds the same literals in fresh memory and stores them
with `SolString::store` (`Exported.storeStringLit_exec`); both end with the same storage, or the
same `Panic(0x22)` on a bad old head.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Reasoning.Theory
open Stele (solidityDecodeBytesLengthHeader solidityBytesDataBaseSlot solidityShortBytesWord)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

/-- The heads the machine IR stores for `"Wrapped Ether"` and `"WETH"`, from the words its root
    writes after their length words. -/
theorem irNameWord_eq : leadWord (UInt256.ofNat
    39553310892875263560936207548857176834471854732421237974622739861269930573824) 13 |||
      UInt256.ofNat 26 =
    solidityShortBytesWord ⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ := by
  decide +kernel

theorem irSymbolWord_eq : leadWord (UInt256.ofNat
    39473711962023174749424659199615060097653232135126263878786656434573155500032) 4 |||
      UInt256.ofNat 8 = solidityShortBytesWord ⟨#[87, 69, 84, 72]⟩ := by
  decide +kernel

/-- The machine IR's update of the low byte of slot 2 to 18, as the exported one writes it. -/
theorem decimalsWord_eq (x : UInt256) :
    UInt256.ofNat ((x.toNat &&&
      115792089237316195423570985008687907853269984665640564039457584007913129639680) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 ||| 18) =
      UInt256.lor (UInt256.ofNat 18) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) x) := by
  have hx := x.val.isLt
  change x.toNat < 2 ^ 256 at hx
  rw [Nat.mod_eq_of_lt (show _ < 115792089237316195423570985008687907853269984665640564039457584007913129639936 from
    lt_of_le_of_lt Nat.and_le_left hx)]
  apply Check.eq_of_toNat
  rw [u256_lor_toNat_exact, uland_toNat, lnot_toNat_gen, Check.toNat_ofNat, Check.toNat_ofNat,
    Check.toNat_ofNat]
  have h1 : (x.toNat &&& 115792089237316195423570985008687907853269984665640564039457584007913129639680
      ||| 18) < 2 ^ 256 :=
    Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left hx) (by norm_num)
  rw [Nat.mod_eq_of_lt (show _ < UInt256.size from h1)]
  simp only [UInt256.size]
  norm_num
  rw [Nat.lor_comm, Nat.land_comm]

variable (I : ExecutionEnv) (w : World)

/-- A section's run never returns, so what follows it does not run. -/
theorem init_bind_eq (args : ByteArray) (g : ByteArray → FeM ByteArray) :
    (((sidecar.model .machine).init args) >>= g).exec I w =
      ((sidecar.model .machine).init args).exec I w := by
  rw [Fe.M.exec_bind]
  cases h : ((sidecar.model .machine).init args).exec I w with
  | none => rfl
  | some x =>
    cases x with
    | error e => rfl
    | ok p => exact absurd h (Check.runSection_not_ok sidecar "init" .machine I w p.1 p.2)

/-- The machine IR's constructor: the prologue stores the free pointer 192 at address 64, then
    the init function runs from its entry block, with the symbols of the init section. -/
theorem ir_init_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    {args : ByteArray}
    (h : ∀ m ic, ic.symbol "&WETH9_runtime" = some (445, 1600) →
      m.func? "store" = some initStoreFunc → m.func? "stored_len" = some initStoredLenFunc →
      m.func? "revert_error" = some initRevertErrorFunc →
      EndsAs X (Check.endRun ((runBlocks m ic initFunc ∅ none 0).exec I
        { w with memory := (UInt256.ofNat 192).toByteArray.write 0 w.memory 64 32 }))) :
    EndsAs X (((sidecar.model .machine).init args).exec I w) := by
  rw [show (sidecar.model .machine).init args = sidecar.runSection "init" .machine from rfl,
    Check.runSection_eq (f := initFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simp [Fe.EVM.mstore, Check.toNat_ofNat, UInt256.size]
  exact h _ _ rfl rfl rfl rfl

/-- A word's write below `2 ^ 32` leaves memory at least that long. -/
theorem write_size_ge (v : UInt256) (M : ByteArray) {d : Nat} (hd : d < 2 ^ 32) :
    d + 32 ≤ (v.toByteArray.write 0 M d 32).size :=
  toByteArray_write_size_ge_off_add32 _ _ _ (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ hd))

/-- A word read below a word written at or past it, below `2 ^ 32`. -/
theorem read_below (v : UInt256) (M : ByteArray) {d r : Nat} (hd : d < 2 ^ 32) (hr : r + 32 ≤ d)
    (hM : r + 32 ≤ M.size) :
    (v.toByteArray.write 0 M d 32).readWithPadding r 32 = M.readWithPadding r 32 :=
  toByteArray_write_read_below_of_gap _ _ _ _ hM hr (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ hd))

/-- `%store` keeps the free pointer. -/
theorem storeMem_read64 (w : World) (slot head : UInt256) (h : 96 ≤ w.memory.size) :
    (storeMem w slot head).readWithPadding 64 32 = w.memory.readWithPadding 64 32 := by
  unfold storeMem
  split
  · exact read_below _ _ (by decide) (by decide) (by omega)
  · rfl

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The machine IR's constructor ends as the exported deployment entry does, on the creation
    code with no arguments, from the empty memory a call starts with and with write
    permission, as a creation has. -/
theorem init_endsAs (hw : w.memory = ByteArray.empty)
    (hcode : I.code = feWETH9CreationBytecode ++ ByteArray.empty) (hperm : I.perm = true) :
    EndsAs ((Exported.init_entry ByteArray.empty >>= fun tail =>
        pure (feWETH9Bytecode ++ tail)).exec I w)
      (((sidecar.model .machine).init ByteArray.empty >>= fun tail =>
        pure (ByteArray.empty ++ tail)).exec I w) := by
  obtain ⟨hrt, hcs⟩ := creation_runtime
  have hsize : I.code.size = 2045 := by rw [hcode, ByteArray.append_empty, hcs]
  have hret : ∀ M, (I.code.write 445 M 0 1600).readWithPadding 0 1600 = feWETH9Bytecode := by
    intro M
    rw [write0_read_back_from_gen _ _ _ _ (by decide) (by omega) (by decide), hcode,
      ByteArray.append_empty, ← hrt]
  clear hcode
  rw [init_bind_eq]
  apply ir_init_endsAs
  intro m ic hs1 hst hsl hre
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [Exported.init_entry, exec_nonPayable, hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  have h13 : UInt256.ofNat 13 = UInt256.ofNat (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray).size := rfl
  have h4 : UInt256.ofNat 4 = UInt256.ofNat (⟨#[87, 69, 84, 72]⟩ : ByteArray).size := rfl
  simp only [Exported.init_entry, Fe.M.exec_bind, exec_nonPayable, hwv, if_pos, Exported.init,
    Exported.nameField, Exported.symbolField, Exported.decimalsField, h13, h4]
  rw [Exported.stringLiteral_exec I w (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) (by decide) (by decide) (by rw [hw]; decide)]
  simp only []
  rw [Exported.storeStringLit_exec I _ (UInt256.ofNat 0) w.memory.size (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) (by decide) (by decide)
    Exported.nameWordLit_eq (Exported.literal_read _ _ (by decide)) (by rw [hw]; decide)
    (by simp [hw, zeros_size]; decide)]
  clear h13 h4
  have hst' := store_eq ic I hst hsl hre
  by_cases hb0 : strHeadBad (slotWord I w.accounts (UInt256.ofNat 0))
  · have hb0z : strHeadBad (slotWord I w.accounts ⟨0⟩) := hb0
    simp [hb0]
    ir_step
    ir_step_nat [hst' 0 (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) (by decide), word_read_gap,
      uInt256OfByteArray_toByteArray, irNameWord_eq, hb0, hb0z]
    exact .exit _
  have hb0z : ¬ strHeadBad (slotWord I w.accounts ⟨0⟩) := hb0
  simp [hb0, hperm, Exported.DynString_drop, FeProofs.Lib.dealloc_u8, FeProofs.Lib.cast_u8_u8]
  rw [Exported.stringLiteral_exec I _ (⟨#[87, 69, 84, 72]⟩ : ByteArray) (by decide) (by decide)
    (by simp [hw, zeros_size]; decide)]
  simp only []
  rw [Exported.storeStringLit_exec I _ (UInt256.ofNat 1) _ (⟨#[87, 69, 84, 72]⟩ : ByteArray) (by decide) (by decide)
    Exported.symbolWordLit_eq (Exported.literal_read _ _ (by decide))
    (by simp [hw, zeros_size]; decide) (by simp [hw, zeros_size]; decide)]
  by_cases hb1 : strHeadBad (slotWord I (strWriteMap I w.accounts (UInt256.ofNat 0) (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray))
    (UInt256.ofNat 1))
  · have hb1z : strHeadBad (slotWord I (strWriteMap I w.accounts ⟨0⟩ (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray)) (UInt256.ofNat 1)) := hb1
    simp [hb1]
    ir_step
    ir_step_nat [hst' 0 (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) (by decide), hst' 1 (⟨#[87, 69, 84, 72]⟩ : ByteArray) (by decide), word_read_gap,
      uInt256OfByteArray_toByteArray, irNameWord_eq, irSymbolWord_eq, hb0, hb0z, hb1, hb1z, hperm,
      storeMem_read64, read_below, write_size, List.length_nil]
    exact .exit _
  have hb1z : ¬ strHeadBad (slotWord I (strWriteMap I w.accounts ⟨0⟩ (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray)) (UInt256.ofNat 1)) := hb1
  simp [hb1, Exported.writeDecimalsLit_exec, exec_sstore, hperm]
  ir_step
  ir_step_nat [hst' 0 (⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩ : ByteArray) (by decide), hst' 1 (⟨#[87, 69, 84, 72]⟩ : ByteArray) (by decide), word_read_gap,
      uInt256OfByteArray_toByteArray, irNameWord_eq, irSymbolWord_eq, hb0, hb0z, hb1, hb1z, hperm,
      storeMem_read64, read_below, write_size, List.length_nil, decimalsWord_eq, hret]
  exact .ok_stop rfl rfl rfl

end FeProofs.WETH9.Sonatina
