import FeProofs.WETH9.ExportedCorrect
import FeProofs.WETH9.ModelCorrect

/-!
# FeWETH9: the bytecode refines the exported contract

`Exported.lean` is the whole contract as `fe-lean-export` prints it: each arm's entry decodes the
message with std's `decode_runtime_args`, runs the arm and returns through std's `return_value`,
`runtime` dispatches on the selector or runs the fallback, and `init_entry` runs the constructor.
This file shows each entry ends as the hand-written model's does, on the empty memory a call
starts with, so the certificates for that model carry over.  The two differ in memory only:
exported code encodes events and return data in fresh buffers, hashes the key of each map entry
it reaches in another, and builds a string in memory before it returns it.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open FeProofs.Lib (returnBool_exec returnU256_exec returnU8_exec)

namespace FeProofs.WETH9.Exported

/-! ## The arms end alike up to memory -/

section Alike

variable (I : ExecutionEnv) (w : World)

theorem alike_approve (guy wad : UInt256) (hmem : w.memory.size + 160 < UInt256.size) :
    Alike 160 w ((recv0_arm1 guy wad).exec I w) ((Model.approve guy wad).exec I w) :=
  alike_withMemory (approve_exec I w guy wad hmem) (by rw [returned_size, keyedAll_size]; simp)

theorem alike_totalSupply : Alike 0 w (recv0_arm2.exec I w) (Model.totalSupply.exec I w) :=
  alike_of_eq (totalSupply_exec I w) fun a v h => by
    simp [Model.totalSupply, selfbalance] at h
    rw [← h.2]

theorem alike_transferFrom (src dst wad : UInt256) (hmem : w.memory.size + 864 < UInt256.size) :
    Alike 864 w ((recv0_arm3 src dst wad).exec I w) ((Model.transferFrom src dst wad).exec I w) :=
  by simpa [recv0_arm3] using transferFrom_alike I w src dst wad hmem

theorem alike_transfer (dst wad : UInt256) (hmem : w.memory.size + 864 < UInt256.size) :
    Alike 864 w ((recv0_arm8 dst wad).exec I w)
      ((caller >>= fun src => Model.transferFrom src dst wad).exec I w) := by
  simpa [recv0_arm8] using transferFrom_alike I w (sender I) dst wad hmem

theorem alike_decimals : Alike 0 w (recv0_arm5.exec I w) (Model.decimals.exec I w) :=
  alike_of_eq (decimals_exec I w) fun a v h => by
    simp [Model.decimals] at h
    rw [← h.2]

theorem alike_balanceOf (owner : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    Alike 64 w ((recv0_arm6 owner).exec I w) ((Model.balanceOf owner).exec I w) :=
  alike_withMemory (balanceOf_exec I w owner hmem) (by rw [keyedAll_size]; simp)

theorem alike_allowance (owner guy : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    Alike 128 w ((recv0_arm10 owner guy).exec I w) ((Model.allowance owner guy).exec I w) :=
  alike_withMemory (allowance_exec I w owner guy hmem) (by rw [keyedAll_size]; simp)

theorem alike_deposit (hmem : w.memory.size + 160 < UInt256.size) :
    Alike 160 w (deposit_Weth9Store_Evm_Evm.exec I w) (Model.deposit.exec I w) :=
  alike_withMemory (deposit_exec I w hmem) (by rw [returned_size, keyedAll_size]; simp)

end Alike

/-! ## The arms' entries

Each entry starts on the empty memory of a call. -/

section Entries

variable (I : ExecutionEnv) (w : World)

/-- An entry and an arm that both revert with no data end alike: a call with value of a
    non-payable arm, or calldata the arm's decoder rejects. -/
theorem revert_endsAs {m : FeM Empty} {arm : FeM ByteArray}
    (hm : m.exec I w = some (.error (.revert ByteArray.empty)))
    (harm : arm.exec I w = some (.error (.revert ByteArray.empty))) :
    EndsAs ((entry m).exec I w) (arm.exec I w) := by
  rw [entry_exec hm, harm]
  exact .exit _

theorem name_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv0_arm0_entry).exec I w) (Model.nameArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm0_entry, exec_nonPayable, hwv])
      (by simp [Model.nameArm, exec_nonPayable, hwv])
  have eg : (entry recv0_arm0_entry).exec I w =
      (entry (SolString_load (.storage Model.nameSlot) >>= Evm_return_value_Sol_DynString)).exec
        I w := by
    simp [entry, recv0_arm0_entry, exec_nonPayable, hwv, decodeName_exec, recv0_arm0, namePlace]
  have eh : Model.nameArm.exec I w = (Model.stringReturn Model.nameSlot).exec I w := by
    simp [Model.nameArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact stringReturn_endsAs I w _ hw

theorem symbol_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv0_arm7_entry).exec I w) (Model.symbolArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm7_entry, exec_nonPayable, hwv])
      (by simp [Model.symbolArm, exec_nonPayable, hwv])
  have eg : (entry recv0_arm7_entry).exec I w =
      (entry (SolString_load (.storage Model.symbolSlot) >>= Evm_return_value_Sol_DynString)).exec
        I w := by
    simp [entry, recv0_arm7_entry, exec_nonPayable, hwv, decodeSymbol_exec, recv0_arm7, symbolPlace]
  have eh : Model.symbolArm.exec I w = (Model.stringReturn Model.symbolSlot).exec I w := by
    simp [Model.symbolArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact stringReturn_endsAs I w _ hw

theorem approve_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm1_entry).exec I w) ((Model.approveArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm1_entry, exec_nonPayable, hwv])
      (by simp [Model.approveArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 68
  · exact revert_endsAs I w (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort])
      (by simp [Model.approveArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · exact revert_endsAs I w (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort, ha0])
      (by simp [Model.approveArm, exec_nonPayable, hwv, hgood, ha0])
  have eg : (entry recv0_arm1_entry).exec I w = (entry (recv0_arm1 (word I.calldata 4)
      (word I.calldata 36) >>= Evm_return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort,
      ha0]
  have eh : (Model.approveArm I.calldata).exec I w = (Model.approve (word I.calldata 4)
      (word I.calldata 36) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [Model.approveArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, by rw [encodeBool_eq]; exact returnBool_exec I w' r hm⟩)
    (alike_approve I w _ _ (by rw [hw]; decide)) (by rw [hw]; decide)

theorem totalSupply_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv0_arm2_entry).exec I w) (Model.totalSupplyArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm2_entry, exec_nonPayable, hwv])
      (by simp [Model.totalSupplyArm, exec_nonPayable, hwv])
  have eg : (entry recv0_arm2_entry).exec I w =
      (entry (recv0_arm2 >>= Evm_return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm2_entry, exec_nonPayable, hwv, decodeTotalSupply_exec]
  have eh : Model.totalSupplyArm.exec I w =
      (Model.totalSupply >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.totalSupplyArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (alike_totalSupply I w)
    (by rw [hw]; decide)

theorem transferFrom_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm3_entry).exec I w) ((Model.transferFromArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 3 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm3_entry, exec_nonPayable, hwv])
      (by simp [Model.transferFromArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 100
  · exact revert_endsAs I w (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits,
        hshort])
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 3 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · exact revert_endsAs I w (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits,
        hshort, ha0])
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0])
  by_cases ha1 : NotAddress (word I.calldata 36)
  · exact revert_endsAs I w (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits,
        hshort, ha0, ha1])
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1])
  have eg : (entry recv0_arm3_entry).exec I w = (entry (recv0_arm3 (word I.calldata 4)
      (word I.calldata 36) (word I.calldata 68) >>= Evm_return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm3_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits,
      hshort, ha0, ha1]
  have eh : (Model.transferFromArm I.calldata).exec I w = (Model.transferFrom (word I.calldata 4)
      (word I.calldata 36) (word I.calldata 68) >>= fun r => pure (Model.encodeBool r)).exec
        I w := by
    simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, by rw [encodeBool_eq]; exact returnBool_exec I w' r hm⟩)
    (alike_transferFrom I w _ _ _ (by rw [hw]; decide)) (by rw [hw]; decide)

theorem withdraw_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm4_entry).exec I w) ((Model.withdrawArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm4_entry, exec_nonPayable, hwv])
      (by simp [Model.withdrawArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 36
  · exact revert_endsAs I w (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeWithdraw_exec I w hlo hfits, hshort])
      (by simp [Model.withdrawArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  have eg : (entry recv0_arm4_entry).exec I w = (entry (recv0_arm4 (word I.calldata 4) >>=
      fun _ => returnData (UInt256.ofNat 0) (UInt256.ofNat 0))).exec I w := by
    simp [entry, recv0_arm4_entry, exec_nonPayable, hwv, decodeWithdraw_exec I w hlo hfits,
      hshort]
  have eh : (Model.withdrawArm I.calldata).exec I w = (Model.withdraw (word I.calldata 4) >>=
      fun _ => pure ByteArray.empty).exec I w := by
    simp [Model.withdrawArm, exec_nonPayable, hwv, hgood]
  rw [eg, eh]
  exact endsAs_alike (enc := fun _ => ByteArray.empty)
    (fun _ w' _ => ⟨w'.memory, returnNone_exec I w'⟩) (withdraw_alike I w _ hw)
    (by rw [hw]; decide)

theorem decimals_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv0_arm5_entry).exec I w) (Model.decimalsArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm5_entry, exec_nonPayable, hwv])
      (by simp [Model.decimalsArm, exec_nonPayable, hwv])
  have eg : (entry recv0_arm5_entry).exec I w =
      (entry (recv0_arm5 >>= Evm_return_value_Sol_u8)).exec I w := by
    simp [entry, recv0_arm5_entry, exec_nonPayable, hwv, decodeDecimals_exec]
  have eh : Model.decimalsArm.exec I w =
      (Model.decimals >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.decimalsArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU8_exec I w' r hm⟩) (alike_decimals I w)
    (by rw [hw]; decide)

theorem balanceOf_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm6_entry).exec I w) ((Model.balanceOfArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm6_entry, exec_nonPayable, hwv])
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 36
  · exact revert_endsAs I w (by
      simp [recv0_arm6_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort])
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · exact revert_endsAs I w (by
      simp [recv0_arm6_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort,
        ha0])
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv, hgood, ha0])
  have eg : (entry recv0_arm6_entry).exec I w =
      (entry (recv0_arm6 (word I.calldata 4) >>= Evm_return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm6_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits,
      hshort, ha0]
  have eh : (Model.balanceOfArm I.calldata).exec I w =
      (Model.balanceOf (word I.calldata 4) >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.balanceOfArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩)
    (alike_balanceOf I w _ (by rw [hw]; decide)) (by rw [hw]; decide)

theorem transfer_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm8_entry).exec I w) ((Model.transferArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm8_entry, exec_nonPayable, hwv])
      (by simp [Model.transferArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 68
  · exact revert_endsAs I w (by
      simp [recv0_arm8_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort])
      (by simp [Model.transferArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · exact revert_endsAs I w (by
      simp [recv0_arm8_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort,
        ha0])
      (by simp [Model.transferArm, exec_nonPayable, hwv, hgood, ha0])
  have eg : (entry recv0_arm8_entry).exec I w = (entry (recv0_arm8 (word I.calldata 4)
      (word I.calldata 36) >>= Evm_return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm8_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort,
      ha0]
  have eh : (Model.transferArm I.calldata).exec I w = ((caller >>= fun src =>
      Model.transferFrom src (word I.calldata 4) (word I.calldata 36)) >>=
        fun r => pure (Model.encodeBool r)).exec I w := by
    simp [Model.transferArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, by rw [encodeBool_eq]; exact returnBool_exec I w' r hm⟩)
    (alike_transfer I w _ _ (by rw [hw]; decide)) (by rw [hw]; decide)

theorem deposit_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv0_arm9_entry).exec I w) (Model.depositArm.exec I w) := by
  have eg : (entry recv0_arm9_entry).exec I w = (entry (deposit_Weth9Store_Evm_Evm >>=
      fun _ => returnData (UInt256.ofNat 0) (UInt256.ofNat 0))).exec I w := by
    simp [entry, recv0_arm9_entry, decodeDeposit_exec, recv0_arm9]
  have eh : Model.depositArm.exec I w =
      (Model.deposit >>= fun _ => pure ByteArray.empty).exec I w := by
    simp [Model.depositArm]
  rw [eg, eh]
  exact endsAs_alike (enc := fun _ => ByteArray.empty)
    (fun _ w' _ => ⟨w'.memory, returnNone_exec I w'⟩) (alike_deposit I w (by rw [hw]; decide))
    (by rw [hw]; decide)

theorem fallback_endsAs (hw : w.memory = ByteArray.empty) :
    EndsAs ((entry recv1_arm0_entry).exec I w) (Model.depositArm.exec I w) := by
  have eg : (entry recv1_arm0_entry).exec I w = (entry (deposit_Weth9Store_Evm_Evm >>=
      fun _ => returnData (UInt256.ofNat 0) (UInt256.ofNat 0))).exec I w := by
    simp [entry, recv1_arm0_entry, recv1_arm0]
  have eh : Model.depositArm.exec I w =
      (Model.deposit >>= fun _ => pure ByteArray.empty).exec I w := by
    simp [Model.depositArm]
  rw [eg, eh]
  exact endsAs_alike (enc := fun _ => ByteArray.empty)
    (fun _ w' _ => ⟨w'.memory, returnNone_exec I w'⟩) (alike_deposit I w (by rw [hw]; decide))
    (by rw [hw]; decide)

theorem allowance_endsAs (hw : w.memory = ByteArray.empty) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm10_entry).exec I w) ((Model.allowanceArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact revert_endsAs I w (by simp [recv0_arm10_entry, exec_nonPayable, hwv])
      (by simp [Model.allowanceArm, exec_nonPayable, hwv])
  by_cases hshort : I.calldata.size < 68
  · exact revert_endsAs I w (by
      simp [recv0_arm10_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort])
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hbad.mpr (by omega)])
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · exact revert_endsAs I w (by
      simp [recv0_arm10_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort,
        ha0])
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0])
  by_cases ha1 : NotAddress (word I.calldata 36)
  · exact revert_endsAs I w (by
      simp [recv0_arm10_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort,
        ha0, ha1])
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1])
  have eg : (entry recv0_arm10_entry).exec I w = (entry (recv0_arm10 (word I.calldata 4)
      (word I.calldata 36) >>= Evm_return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm10_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits,
      hshort, ha0, ha1]
  have eh : (Model.allowanceArm I.calldata).exec I w = (Model.allowance (word I.calldata 4)
      (word I.calldata 36) >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩)
    (alike_allowance I w _ _ (by rw [hw]; decide)) (by rw [hw]; decide)

end Entries

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written model's does, on calldata below `2 ^ 64`
    bytes and the empty memory a call starts with. -/
theorem runtime_endsAs (I : ExecutionEnv) (w : World) (hw : w.memory = ByteArray.empty)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (feWETH9SelBytes i)) →
      (feWETH9SelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    have eg : (entry runtime).exec I w = (entry recv1_arm0_entry).exec I w := by
      simp [entry, runtime, hn, hlt]
    have eh : Model.runtime.exec I w = Model.depositArm.exec I w := by
      simp [Model.runtime, hlt]
    rw [eg, eh]
    exact fallback_endsAs I w hw
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feWETH9SelBytes 0)
  · have hw' := selWord_hit (nameEvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = Model.nameArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = true from h0]
    rw [eg, eh]
    exact name_endsAs I w hw
  have n0 := miss 0 h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x06fdde03 :=
    selWord_miss (nameEvmSelector hsz) n0
  by_cases h1 : selIs I (feWETH9SelBytes 1)
  · have hw' := selWord_hit (approveEvmSelector hsz) h1
    have eg : (entry runtime).exec I w = (entry recv0_arm1_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.approveArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = true from h1]
    rw [eg, eh]
    exact approve_endsAs I w hw hsz hfits
  have n1 := miss 1 h1
  have w1 : selWord I.calldata ≠ UInt256.ofNat 0x095ea7b3 :=
    selWord_miss (approveEvmSelector hsz) n1
  by_cases h2 : selIs I (feWETH9SelBytes 2)
  · have hw' := selWord_hit (totalSupplyEvmSelector hsz) h2
    have eg : (entry runtime).exec I w = (entry recv0_arm2_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = Model.totalSupplyArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = true from h2]
    rw [eg, eh]
    exact totalSupply_endsAs I w hw
  have n2 := miss 2 h2
  have w2 : selWord I.calldata ≠ UInt256.ofNat 0x18160ddd :=
    selWord_miss (totalSupplyEvmSelector hsz) n2
  by_cases h3 : selIs I (feWETH9SelBytes 3)
  · have hw' := selWord_hit (transferFromEvmSelector hsz) h3
    have eg : (entry runtime).exec I w = (entry recv0_arm3_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.transferFromArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = true from h3]
    rw [eg, eh]
    exact transferFrom_endsAs I w hw hsz hfits
  have n3 := miss 3 h3
  have w3 : selWord I.calldata ≠ UInt256.ofNat 0x23b872dd :=
    selWord_miss (transferFromEvmSelector hsz) n3
  by_cases h4 : selIs I (feWETH9SelBytes 4)
  · have hw' := selWord_hit (withdrawEvmSelector hsz) h4
    have eg : (entry runtime).exec I w = (entry recv0_arm4_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.withdrawArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = true from h4]
    rw [eg, eh]
    exact withdraw_endsAs I w hw hsz hfits
  have n4 := miss 4 h4
  have w4 : selWord I.calldata ≠ UInt256.ofNat 0x2e1a7d4d :=
    selWord_miss (withdrawEvmSelector hsz) n4
  by_cases h5 : selIs I (feWETH9SelBytes 5)
  · have hw' := selWord_hit (decimalsEvmSelector hsz) h5
    have eg : (entry runtime).exec I w = (entry recv0_arm5_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = Model.decimalsArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = true from h5]
    rw [eg, eh]
    exact decimals_endsAs I w hw
  have n5 := miss 5 h5
  have w5 : selWord I.calldata ≠ UInt256.ofNat 0x313ce567 :=
    selWord_miss (decimalsEvmSelector hsz) n5
  by_cases h6 : selIs I (feWETH9SelBytes 6)
  · have hw' := selWord_hit (balanceOfEvmSelector hsz) h6
    have eg : (entry runtime).exec I w = (entry recv0_arm6_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.balanceOfArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = true from h6]
    rw [eg, eh]
    exact balanceOf_endsAs I w hw hsz hfits
  have n6 := miss 6 h6
  have w6 : selWord I.calldata ≠ UInt256.ofNat 0x70a08231 :=
    selWord_miss (balanceOfEvmSelector hsz) n6
  by_cases h7 : selIs I (feWETH9SelBytes 7)
  · have hw' := selWord_hit (symbolEvmSelector hsz) h7
    have eg : (entry runtime).exec I w = (entry recv0_arm7_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = Model.symbolArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n6,
        show (Model.symbolSelector == I.calldata.extract 0 4) = true from h7]
    rw [eg, eh]
    exact symbol_endsAs I w hw
  have n7 := miss 7 h7
  have w7 : selWord I.calldata ≠ UInt256.ofNat 0x95d89b41 :=
    selWord_miss (symbolEvmSelector hsz) n7
  by_cases h8 : selIs I (feWETH9SelBytes 8)
  · have hw' := selWord_hit (transferEvmSelector hsz) h8
    have eg : (entry runtime).exec I w = (entry recv0_arm8_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.transferArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n6,
        show (Model.symbolSelector == I.calldata.extract 0 4) = false from n7,
        show (Model.transferSelector == I.calldata.extract 0 4) = true from h8]
    rw [eg, eh]
    exact transfer_endsAs I w hw hsz hfits
  have n8 := miss 8 h8
  have w8 : selWord I.calldata ≠ UInt256.ofNat 0xa9059cbb :=
    selWord_miss (transferEvmSelector hsz) n8
  by_cases h9 : selIs I (feWETH9SelBytes 9)
  · have hw' := selWord_hit (depositEvmSelector hsz) h9
    have eg : (entry runtime).exec I w = (entry recv0_arm9_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = Model.depositArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n6,
        show (Model.symbolSelector == I.calldata.extract 0 4) = false from n7,
        show (Model.transferSelector == I.calldata.extract 0 4) = false from n8,
        show (Model.depositSelector == I.calldata.extract 0 4) = true from h9]
    rw [eg, eh]
    exact deposit_endsAs I w hw
  have n9 := miss 9 h9
  have w9 : selWord I.calldata ≠ UInt256.ofNat 0xd0e30db0 :=
    selWord_miss (depositEvmSelector hsz) n9
  by_cases h10 : selIs I (feWETH9SelBytes 10)
  · have hw' := selWord_hit (allowanceEvmSelector hsz) h10
    have eg : (entry runtime).exec I w = (entry recv0_arm10_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw']
    have eh : Model.runtime.exec I w = (Model.allowanceArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n6,
        show (Model.symbolSelector == I.calldata.extract 0 4) = false from n7,
        show (Model.transferSelector == I.calldata.extract 0 4) = false from n8,
        show (Model.depositSelector == I.calldata.extract 0 4) = false from n9,
        show (Model.allowanceSelector == I.calldata.extract 0 4) = true from h10]
    rw [eg, eh]
    exact allowance_endsAs I w hw hsz hfits
  have n10 := miss 10 h10
  have w10 : selWord I.calldata ≠ UInt256.ofNat 0xdd62ed3e :=
    selWord_miss (allowanceEvmSelector hsz) n10
  have eg : (entry runtime).exec I w = (entry recv1_arm0_entry).exec I w := by
    simp [entry, runtime, hn, hn4, selector_exec, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  have eh : Model.runtime.exec I w = Model.depositArm.exec I w := by
    simp [Model.runtime, hn4,
      show (Model.nameSelector == I.calldata.extract 0 4) = false from n0,
      show (Model.approveSelector == I.calldata.extract 0 4) = false from n1,
      show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n2,
      show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n3,
      show (Model.withdrawSelector == I.calldata.extract 0 4) = false from n4,
      show (Model.decimalsSelector == I.calldata.extract 0 4) = false from n5,
      show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n6,
      show (Model.symbolSelector == I.calldata.extract 0 4) = false from n7,
      show (Model.transferSelector == I.calldata.extract 0 4) = false from n8,
      show (Model.depositSelector == I.calldata.extract 0 4) = false from n9,
      show (Model.allowanceSelector == I.calldata.extract 0 4) = false from n10]
  rw [eg, eh]
  exact fallback_endsAs I w hw

/-! ## The certificate -/

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem feWETH9RefinesExported : RefinesOn .P0 feWETH9Bytecode contract CalldataFits := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hown hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feWETH9RefinesModel σ σ₀ g A I ByteArray.empty
      (by rw [ByteArray.append_empty]; exact hcode) rfl hown hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs (runtime_endsAs I (World.init σ A feed) rfl hfits) h⟩

/-- Deployment with no argument bytes, for any initial storage, refines the exported deployment
    entry. -/
theorem feWETH9DeployRefinesExported :
    RefinesDeploy .P0 feWETH9CreationBytecode feWETH9Bytecode contract (· = ByteArray.empty) := by
  intro σ σ₀ g A I args hargs hcode hown hperm
  rcases feWETH9DeployRefinesModel σ σ₀ g A I args hargs hcode hown hperm with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (init_endsAs I (World.init σ A feed) args feWETH9Bytecode rfl hperm) h⟩

end FeProofs.WETH9.Exported
