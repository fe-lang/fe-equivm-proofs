import FeProofs.WETH9.SonatinaReturn

/-!
# FeWETH9's string getters against the machine IR

`name()` and `symbol()`: the machine IR calls `%load` on slot 0 or 1 (`load_run`) and returns
its copy with `%return_value__g7f54` (`returnValue_run`); the exported arm runs
`SolString::load` and `return_value` (`Exported.stringReturn_exec`).  Both return the offset
word and the copy, or fail with the same panic.  The arms read the free pointer, so the machine
IR's memory is the one the runtime's prologue leaves, and the exported world's memory is empty,
as at the start of a call.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina Reasoning.Theory
open Stele (solidityDecodeBytesLengthHeader)
open Exported (loaded)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable {m : Module} (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The memory the runtime's prologue leaves: the free pointer 224 at 64. -/
abbrev runtimeMem (M : ByteArray) : ByteArray := (UInt256.ofNat 224).toByteArray.write 0 M 64 32

theorem runtimeMem_fp (M : ByteArray) :
    uInt256OfByteArray ((runtimeMem M).readWithPadding 64 32) = UInt256.ofNat 224 := by
  rw [runtimeMem, word_read_gap _ _ (by decide), uInt256OfByteArray_toByteArray]

theorem runtimeMem_size : (runtimeMem ByteArray.empty).size ≤ 224 := by
  rw [runtimeMem, write_size _ _ (by decide)]; simp

set_option maxHeartbeats 8000000 in
/-- `name()`: the string at slot 0. -/
theorem arm_name (hl : m.func? "load" = some loadFunc)
    (hs : m.func? "stored_len" = some storedLenFunc)
    (hr : m.func? "revert_error" = some revertErrorFunc)
    (hrv : m.func? "return_value__g7f54" = some returnValueFunc)
    (hw : w.memory = ByteArray.empty) (hcd : I.calldata.size < 2 ^ 64) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_Name_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 5).exec I
        { w with memory := runtimeMem w.memory })) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [entry, Exported.recv_Name_entry, exec_nonPayable, hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  have hmr : w.reserved.memory.size + 2 ^ 66 < UInt256.size := by
    rw [World.reserved_size, hw]; decide
  rw [show (entry Exported.recv_Name_entry).exec I w = (entry (Exported.SolString_load
      (.storage (UInt256.ofNat 0)) >>= Exported.Evm_return_value_Sol_DynString)).exec I w by
    simp [entry, Exported.recv_Name_entry, exec_nonPayable, hwv, Exported.decodeName_exec,
      Exported.recv_Name, Exported.nameField]]
  obtain ⟨A', hA', hfp', hrun⟩ := load_run ic I w hl hs hr (UInt256.ofNat 0) (runtimeMem w.memory) 224
    (runtimeMem_fp _) (by rw [hw]; exact runtimeMem_size) (by decide) (by decide)
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl] at hrun
  rw [hw] at hrun ⊢
  cases hd : solidityDecodeBytesLengthHeader (slotWord I w.accounts (UInt256.ofNat 0)) with
  | ok L =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨0⟩) = .ok L := hd
    have hL : L < 2 ^ 255 := by
      rcases decodeHeader_cases (slotWord I w.accounts (UInt256.ofNat 0)) with
        ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd
      · have := u256_toNat_lt (slotWord I w.accounts (UInt256.ofNat 0)); omega
      · omega
    have hB : ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 0) L).size =
        32 + (L + 31) / 32 * 32 := by
      simp [loaded, strBytes_size]; omega
    by_cases h64 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    swap
    · have h64l : ¬ 32 + (L + 31) / 32 * 32 < 18446744073709551616 := h64
      rw [entry_exec (f := .panic 0x41) (by
        simp only [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd,
          show ¬ 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64 by omega, ite_false])]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64, h64l]
      exact .panic_revert 65
    have hSm : (32 + (L + 31) / 32 * 32) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        32 + (L + 31) / 32 * 32 := Nat.mod_eq_of_lt (by omega)
    have hext : (A' ++ ((UInt256.ofNat L).toByteArray ++
        loaded w.accounts I (UInt256.ofNat 0) L)).extract 224 (224 + (32 + (L + 31) / 32 * 32)) =
        (UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 0) L := by
      rw [extract_append_right_window _ _ _ _ (by omega), hA', Nat.sub_self,
        show 224 + (32 + (L + 31) / 32 * 32) - 224 =
          ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 0) L).size by
            rw [hB]; omega, byteArray_extract_self]
    have hfpM : uInt256OfByteArray ((A' ++ ((UInt256.ofNat L).toByteArray ++
        loaded w.accounts I (UInt256.ofNat 0) L)).readWithPadding 64 32) =
        UInt256.ofNat (A' ++ ((UInt256.ofNat L).toByteArray ++
          loaded w.accounts I (UInt256.ofNat 0) L)).size := by
      rw [read_prefix _ _ (by decide) (by rw [hA']; decide), hfp' L hd, ByteArray.size_append, hA', hB]
    have hrv' := returnValue_run ic I w hrv 224 (32 + (L + 31) / 32 * 32) _ hfpM
      (by rw [ByteArray.size_append, hA', hB]) (by omega)
      (by rw [ByteArray.size_append, hA', hB]; omega) h64 hcd
    have h64l : 32 + (L + 31) / 32 * 32 < 18446744073709551616 := h64
    simp only [ofNat_zero_eq] at hrv' hext
    by_cases h64' : 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64
    · have h64l' : 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 := h64'
      rw [entry_exec (by simp only [Exported.stringReturn_exec I w.reserved _ hmr,
        World.reserved_accounts, hd, h64', ite_true]; rfl)]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64l, hSm, hrv', h64', h64l', hext]
      exact .stop_stop rfl rfl rfl
    · have h64l' : ¬ 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 := h64'
      rw [entry_exec (f := .panic 0x41) (by
        simp only [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd,
          h64', ite_false])]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64l, hSm, hrv', h64', h64l']
      exact .panic_revert 65
  | revert =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨0⟩) = .revert := hd
    rw [entry_exec (f := .revert (panicData 0x22))
      (by rw [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd])]
    ir_step
    ir_step [hrun, loadOut, hd, hd']
    exact .exit _
  | error =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨0⟩) = .error := hd
    rw [entry_exec (f := .revert (panicData 0x22))
      (by rw [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd])]
    ir_step
    ir_step [hrun, loadOut, hd, hd']
    exact .exit _

set_option maxHeartbeats 8000000 in
/-- `symbol()`: the string at slot 1. -/
theorem arm_symbol (hl : m.func? "load" = some loadFunc)
    (hs : m.func? "stored_len" = some storedLenFunc)
    (hr : m.func? "revert_error" = some revertErrorFunc)
    (hrv : m.func? "return_value__g7f54" = some returnValueFunc)
    (hw : w.memory = ByteArray.empty) (hcd : I.calldata.size < 2 ^ 64) (E : Sonatina.Env)
    (p : Option Nat) :
    EndsAs ((entry Exported.recv_Symbol_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 49).exec I
        { w with memory := runtimeMem w.memory })) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [entry, Exported.recv_Symbol_entry, exec_nonPayable, hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  have hmr : w.reserved.memory.size + 2 ^ 66 < UInt256.size := by
    rw [World.reserved_size, hw]; decide
  rw [show (entry Exported.recv_Symbol_entry).exec I w = (entry (Exported.SolString_load
      (.storage (UInt256.ofNat 1)) >>= Exported.Evm_return_value_Sol_DynString)).exec I w by
    simp [entry, Exported.recv_Symbol_entry, exec_nonPayable, hwv, Exported.decodeSymbol_exec,
      Exported.recv_Symbol, Exported.symbolField]]
  obtain ⟨A', hA', hfp', hrun⟩ := load_run ic I w hl hs hr (UInt256.ofNat 1) (runtimeMem w.memory) 224
    (runtimeMem_fp _) (by rw [hw]; exact runtimeMem_size) (by decide) (by decide)
  simp only [show (UInt256.ofNat 1).toNat = 1 from rfl] at hrun
  rw [hw] at hrun ⊢
  cases hd : solidityDecodeBytesLengthHeader (slotWord I w.accounts (UInt256.ofNat 1)) with
  | ok L =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨1⟩) = .ok L := hd
    have hL : L < 2 ^ 255 := by
      rcases decodeHeader_cases (slotWord I w.accounts (UInt256.ofNat 1)) with
        ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd
      · have := u256_toNat_lt (slotWord I w.accounts (UInt256.ofNat 1)); omega
      · omega
    have hB : ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 1) L).size =
        32 + (L + 31) / 32 * 32 := by
      simp [loaded, strBytes_size]; omega
    by_cases h64 : 32 + (L + 31) / 32 * 32 < 2 ^ 64
    swap
    · have h64l : ¬ 32 + (L + 31) / 32 * 32 < 18446744073709551616 := h64
      rw [entry_exec (f := .panic 0x41) (by
        simp only [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd,
          show ¬ 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64 by omega, ite_false])]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64, h64l]
      exact .panic_revert 65
    have hSm : (32 + (L + 31) / 32 * 32) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        32 + (L + 31) / 32 * 32 := Nat.mod_eq_of_lt (by omega)
    have hext : (A' ++ ((UInt256.ofNat L).toByteArray ++
        loaded w.accounts I (UInt256.ofNat 1) L)).extract 224 (224 + (32 + (L + 31) / 32 * 32)) =
        (UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 1) L := by
      rw [extract_append_right_window _ _ _ _ (by omega), hA', Nat.sub_self,
        show 224 + (32 + (L + 31) / 32 * 32) - 224 =
          ((UInt256.ofNat L).toByteArray ++ loaded w.accounts I (UInt256.ofNat 1) L).size by
            rw [hB]; omega, byteArray_extract_self]
    have hfpM : uInt256OfByteArray ((A' ++ ((UInt256.ofNat L).toByteArray ++
        loaded w.accounts I (UInt256.ofNat 1) L)).readWithPadding 64 32) =
        UInt256.ofNat (A' ++ ((UInt256.ofNat L).toByteArray ++
          loaded w.accounts I (UInt256.ofNat 1) L)).size := by
      rw [read_prefix _ _ (by decide) (by rw [hA']; decide), hfp' L hd, ByteArray.size_append, hA', hB]
    have hrv' := returnValue_run ic I w hrv 224 (32 + (L + 31) / 32 * 32) _ hfpM
      (by rw [ByteArray.size_append, hA', hB]) (by omega)
      (by rw [ByteArray.size_append, hA', hB]; omega) h64 hcd
    have h64l : 32 + (L + 31) / 32 * 32 < 18446744073709551616 := h64
    by_cases h64' : 32 + (32 + (L + 31) / 32 * 32) < 2 ^ 64
    · have h64l' : 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 := h64'
      rw [entry_exec (by simp only [Exported.stringReturn_exec I w.reserved _ hmr,
        World.reserved_accounts, hd, h64', ite_true]; rfl)]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64l, hSm, hrv', h64', h64l', hext]
      exact .stop_stop rfl rfl rfl
    · have h64l' : ¬ 32 + (32 + (L + 31) / 32 * 32) < 18446744073709551616 := h64'
      rw [entry_exec (f := .panic 0x41) (by
        simp only [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd,
          h64', ite_false])]
      ir_step
      ir_step [hrun, loadOut, hd, hd', h64l, hSm, hrv', h64', h64l']
      exact .panic_revert 65
  | revert =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨1⟩) = .revert := hd
    rw [entry_exec (f := .revert (panicData 0x22))
      (by rw [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd])]
    ir_step
    ir_step [hrun, loadOut, hd, hd']
    exact .exit _
  | error =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I w.accounts ⟨1⟩) = .error := hd
    rw [entry_exec (f := .revert (panicData 0x22))
      (by rw [Exported.stringReturn_exec I w.reserved _ hmr, World.reserved_accounts, hd])]
    ir_step
    ir_step [hrun, loadOut, hd, hd']
    exact .exit _

end FeProofs.WETH9.Sonatina
