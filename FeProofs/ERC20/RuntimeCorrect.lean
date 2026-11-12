import FeProofs.ERC20.ExportedCorrect

/-!
# FeERC20: the bytecode refines the exported contract

`Exported.lean` is the whole contract as `fe-lean-export` prints it: each arm's entry decodes the
message with std's `decode_runtime_args`, runs the arm and returns through std's `return_value`,
`runtime` dispatches on the selector, and `init_entry` decodes the constructor argument.  This
file shows each entry ends as the hand-written model's does, so the certificates for that model
carry over.  The two differ in memory only: exported code encodes events and return data in
fresh buffers, and hashes the key of each map entry it reaches in another.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM
open FeProofs.Lib (returnU256_exec withArg withArg_size)

namespace FeProofs.ERC20.Exported

/-! ## The arms end alike up to memory -/

section Alike

variable (I : ExecutionEnv) (w : World)

theorem alike_transfer (dst value : UInt256) (hmem : w.memory.size + 352 < UInt256.size) :
    Alike 352 w ((recv0_arm0 dst value).exec I w) ((Model.transfer dst value).exec I w) :=
  alike_withMemory (transfer_exec I w dst value hmem)
    (by rw [returned_size, keyedAll_size]; simp)

theorem alike_approve (spender value : UInt256) (hmem : w.memory.size + 160 < UInt256.size) :
    Alike 160 w ((recv0_arm1 spender value).exec I w) ((Model.approve spender value).exec I w) :=
  alike_withMemory (approve_exec I w spender value hmem)
    (by rw [returned_size, keyedAll_size]; simp)

theorem alike_transferFrom (src dst value : UInt256)
    (hmem : w.memory.size + 608 < UInt256.size) :
    Alike 608 w ((recv0_arm2 src dst value).exec I w)
      ((Model.transferFrom src dst value).exec I w) :=
  alike_withMemory (transferFrom_exec I w src dst value hmem)
    (by rw [returned_size, keyedAll_size]; simp)

theorem alike_balanceOf (owner : UInt256) (hmem : w.memory.size + 64 < UInt256.size) :
    Alike 64 w ((recv0_arm3 owner).exec I w) ((Model.balanceOf owner).exec I w) :=
  alike_withMemory (balanceOf_exec I w owner hmem) (by rw [keyedAll_size]; simp)

theorem alike_allowance (owner spender : UInt256) (hmem : w.memory.size + 128 < UInt256.size) :
    Alike 128 w ((recv0_arm4 owner spender).exec I w)
      ((Model.allowance owner spender).exec I w) :=
  alike_withMemory (allowance_exec I w owner spender hmem) (by rw [keyedAll_size]; simp)

theorem alike_totalSupply : Alike 0 w (recv0_arm5.exec I w) (Model.totalSupply.exec I w) :=
  alike_of_eq (totalSupply_exec I w)
    ((show KeepsMemory Model.totalSupply by unfold Model.totalSupply; keeps_memory) I w)

end Alike

/-! ## The arms' entries -/

section Entries

variable (I : ExecutionEnv) (w : World)

theorem transfer_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm0_entry).exec I w) ((Model.transferArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv])]
    simp [Model.transferArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort])]
    simp [Model.transferArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort, ha0])]
    simp [Model.transferArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm0_entry).exec I w =
      (entry (recv0_arm0 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm0_entry, exec_nonPayable, hwv, decodeTransfer_exec I w hlo hfits, hshort, ha0]
  have eh : (Model.transferArm I.calldata).exec I w =
      (Model.transfer (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [Model.transferArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩)
    (alike_transfer I w _ _ (by omega)) (by omega)

theorem approve_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm1_entry).exec I w) ((Model.approveArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv])]
    simp [Model.approveArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort])]
    simp [Model.approveArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort, ha0])]
    simp [Model.approveArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm1_entry).exec I w =
      (entry (recv0_arm1 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm1_entry, exec_nonPayable, hwv, decodeApprove_exec I w hlo hfits, hshort, ha0]
  have eh : (Model.approveArm I.calldata).exec I w =
      (Model.approve (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [Model.approveArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩)
    (alike_approve I w _ _ (by omega)) (by omega)

theorem transferFrom_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm2_entry).exec I w) ((Model.transferFromArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 3 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv])]
    simp [Model.transferFromArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 100
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort])]
    simp [Model.transferFromArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 3 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0])]
    simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  by_cases ha1 : NotAddress (word I.calldata 36)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0, ha1])]
    simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1]
    exact .exit _
  have eg : (entry recv0_arm2_entry).exec I w =
      (entry (recv0_arm2 (word I.calldata 4) (word I.calldata 36) (word I.calldata 68) >>= return_value_Sol_bool)).exec I w := by
    simp [entry, recv0_arm2_entry, exec_nonPayable, hwv, decodeTransferFrom_exec I w hlo hfits, hshort, ha0, ha1]
  have eh : (Model.transferFromArm I.calldata).exec I w =
      (Model.transferFrom (word I.calldata 4) (word I.calldata 36) (word I.calldata 68) >>= fun r => pure (Model.encodeBool r)).exec I w := by
    simp [Model.transferFromArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnBool_exec I w' r hm⟩)
    (alike_transferFrom I w _ _ _ (by omega)) (by omega)

theorem balanceOf_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm3_entry).exec I w) ((Model.balanceOfArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv])]
    simp [Model.balanceOfArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort])]
    simp [Model.balanceOfArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort, ha0])]
    simp [Model.balanceOfArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  have eg : (entry recv0_arm3_entry).exec I w =
      (entry (recv0_arm3 (word I.calldata 4) >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm3_entry, exec_nonPayable, hwv, decodeBalanceOf_exec I w hlo hfits, hshort, ha0]
  have eh : (Model.balanceOfArm I.calldata).exec I w =
      (Model.balanceOf (word I.calldata 4) >>= fun r => pure (r.toByteArray)).exec I w := by
    simp [Model.balanceOfArm, exec_nonPayable, hwv, hgood, ha0]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (alike_balanceOf I w _ (by omega))
    (by omega)

theorem allowance_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hlo : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry recv0_arm4_entry).exec I w) ((Model.allowanceArm I.calldata).exec I w) := by
  have hbad := badHead_iff I.calldata 2 hfits
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv])]
    simp [Model.allowanceArm, exec_nonPayable, hwv]
    exact .exit _
  by_cases hshort : I.calldata.size < 68
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort])]
    simp [Model.allowanceArm, exec_nonPayable, hwv, hbad.mpr (by omega)]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 2 := fun h => hshort (by have := hbad.mp h; omega)
  by_cases ha0 : NotAddress (word I.calldata 4)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0])]
    simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0]
    exact .exit _
  by_cases ha1 : NotAddress (word I.calldata 36)
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0, ha1])]
    simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1]
    exact .exit _
  have eg : (entry recv0_arm4_entry).exec I w =
      (entry (recv0_arm4 (word I.calldata 4) (word I.calldata 36) >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm4_entry, exec_nonPayable, hwv, decodeAllowance_exec I w hlo hfits, hshort, ha0, ha1]
  have eh : (Model.allowanceArm I.calldata).exec I w =
      (Model.allowance (word I.calldata 4) (word I.calldata 36) >>= fun r => pure (r.toByteArray)).exec I w := by
    simp [Model.allowanceArm, exec_nonPayable, hwv, hgood, ha0, ha1]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (alike_allowance I w _ _ (by omega))
    (by omega)

theorem totalSupply_endsAs (hmem : w.memory.size + 1024 < UInt256.size) :
    EndsAs ((entry recv0_arm5_entry).exec I w) (Model.totalSupplyArm.exec I w) := by
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [entry_exec (f := .revert ByteArray.empty) (by
      simp [recv0_arm5_entry, exec_nonPayable, hwv])]
    simp [Model.totalSupplyArm, exec_nonPayable, hwv]
    exact .exit _
  have eg : (entry recv0_arm5_entry).exec I w =
      (entry (recv0_arm5 >>= return_value_Sol_u256)).exec I w := by
    simp [entry, recv0_arm5_entry, exec_nonPayable, hwv, decodeTotalSupply_exec]
  have eh : Model.totalSupplyArm.exec I w = (Model.totalSupply >>= fun r => pure r.toByteArray).exec I w := by
    simp [Model.totalSupplyArm, exec_nonPayable, hwv]
  rw [eg, eh]
  exact endsAs_alike (fun r w' hm => ⟨_, returnU256_exec I w' r hm⟩) (alike_totalSupply I w)
    (by omega)

/-! ## The runtime entry -/

/-- The exported runtime entry ends as the hand-written model's does, on calldata below
    `2 ^ 64` bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 1024 < UInt256.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry runtime).exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (feERC20SelBytes i)) →
      (feERC20SelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [entry_exec (f := .revert ByteArray.empty) (by simp [runtime, hn, hlt])]
    simp [Model.runtime, hlt]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feERC20SelBytes 0)
  · have hw := selWord_hit (approveEvmSelector hsz) h0
    have eg : (entry runtime).exec I w = (entry recv0_arm1_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = (Model.approveArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = true from h0]
    rw [eg, eh]
    exact approve_endsAs I w hmem hsz hfits
  have n0 := miss 0 h0
  have w0 : selWord I.calldata ≠ UInt256.ofNat 0x095ea7b3 := selWord_miss (approveEvmSelector hsz) n0
  by_cases h1 : selIs I (feERC20SelBytes 1)
  · have hw := selWord_hit (totalSupplyEvmSelector hsz) h1
    have eg : (entry runtime).exec I w = (entry recv0_arm5_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = Model.totalSupplyArm.exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = true from h1]
    rw [eg, eh]
    exact totalSupply_endsAs I w hmem
  have n1 := miss 1 h1
  have w1 : selWord I.calldata ≠ UInt256.ofNat 0x18160ddd := selWord_miss (totalSupplyEvmSelector hsz) n1
  by_cases h2 : selIs I (feERC20SelBytes 2)
  · have hw := selWord_hit (transferFromEvmSelector hsz) h2
    have eg : (entry runtime).exec I w = (entry recv0_arm2_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = (Model.transferFromArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = true from h2]
    rw [eg, eh]
    exact transferFrom_endsAs I w hmem hsz hfits
  have n2 := miss 2 h2
  have w2 : selWord I.calldata ≠ UInt256.ofNat 0x23b872dd := selWord_miss (transferFromEvmSelector hsz) n2
  by_cases h3 : selIs I (feERC20SelBytes 3)
  · have hw := selWord_hit (balanceOfEvmSelector hsz) h3
    have eg : (entry runtime).exec I w = (entry recv0_arm3_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = (Model.balanceOfArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = true from h3]
    rw [eg, eh]
    exact balanceOf_endsAs I w hmem hsz hfits
  have n3 := miss 3 h3
  have w3 : selWord I.calldata ≠ UInt256.ofNat 0x70a08231 := selWord_miss (balanceOfEvmSelector hsz) n3
  by_cases h4 : selIs I (feERC20SelBytes 4)
  · have hw := selWord_hit (transferEvmSelector hsz) h4
    have eg : (entry runtime).exec I w = (entry recv0_arm0_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = (Model.transferArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.transferSelector == I.calldata.extract 0 4) = true from h4]
    rw [eg, eh]
    exact transfer_endsAs I w hmem hsz hfits
  have n4 := miss 4 h4
  have w4 : selWord I.calldata ≠ UInt256.ofNat 0xa9059cbb := selWord_miss (transferEvmSelector hsz) n4
  by_cases h5 : selIs I (feERC20SelBytes 5)
  · have hw := selWord_hit (allowanceEvmSelector hsz) h5
    have eg : (entry runtime).exec I w = (entry recv0_arm4_entry).exec I w := by
      simp +decide [entry, runtime, hn, hn4, selector_exec, hw]
    have eh : Model.runtime.exec I w = (Model.allowanceArm I.calldata).exec I w := by
      simp [Model.runtime, hn4,
        show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
        show (Model.transferSelector == I.calldata.extract 0 4) = false from n4,
        show (Model.allowanceSelector == I.calldata.extract 0 4) = true from h5]
    rw [eg, eh]
    exact allowance_endsAs I w hmem hsz hfits
  have n5 := miss 5 h5
  have w5 : selWord I.calldata ≠ UInt256.ofNat 0xdd62ed3e := selWord_miss (allowanceEvmSelector hsz) n5
  rw [entry_exec (f := .revert ByteArray.empty) (by
    simp [runtime, hn, hn4, selector_exec, w0, w1, w2, w3, w4, w5])]
  simp [Model.runtime, hn4,
    show (Model.approveSelector == I.calldata.extract 0 4) = false from n0,
    show (Model.totalSupplySelector == I.calldata.extract 0 4) = false from n1,
    show (Model.transferFromSelector == I.calldata.extract 0 4) = false from n2,
    show (Model.balanceOfSelector == I.calldata.extract 0 4) = false from n3,
    show (Model.transferSelector == I.calldata.extract 0 4) = false from n4,
    show (Model.allowanceSelector == I.calldata.extract 0 4) = false from n5]
  exact .exit _

end Entries

/-! ## Deployment -/

/-- The exported deployment entry ends as the hand-written model's does, on one argument word. -/
theorem init_endsAs (v : UInt256) (out : ByteArray) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size + 1024 < UInt256.size) :
    EndsAs ((init_entry (ctorTail v) >>= fun tail => pure (out ++ tail)).exec I w)
      ((Model.init (ctorTail v) >>= fun _ => pure out).exec I w) := by
  have hsz : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hword : word (ctorTail v) 0 = v := by
    show uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v
    rw [readBytes_all32 _ hsz, ctorTail, word_toBytesBE_toByteArray_eq_toByteArray,
      uInt256OfByteArray_toByteArray]
  rw [M.exec_bind, initEntry_exec I w v (by omega)]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [Model.init, exec_nonPayable, hwv]
    exact .exit _
  rw [if_pos hwv, M.exec_bind, init_exec I _ v (by simp only [withArg_size]; omega)]
  by_cases hperm : I.perm = true
  · simp [Model.init, exec_nonPayable, hwv, hsz, hword, Model.initBody, exec_sstore, exec_emit,
      hperm]
    exact .ok_ok rfl rfl
  · simp [Model.init, exec_nonPayable, hwv, hsz, hword, Model.initBody, exec_sstore, hperm]
    exact .exit _

/-! ## The certificate -/

/-- The contract as exported: the deployment entry and the runtime entry. -/
def contract : ContractModel := { init := init_entry, runtime := entry runtime }

/-- The runtime bytecode refines the exported contract, on calldata below `2 ^ 64` bytes. -/
theorem feERC20RefinesExported : RefinesOn .P0 feERC20Bytecode contract CalldataFits := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hfits
  have hsize : I.calldata.size < UInt256.size := by
    unfold CalldataFits at hfits
    unfold UInt256.size
    omega
  rcases feERC20RefinesModel σ σ₀ g A I ByteArray.empty
      (by rw [ByteArray.append_empty]; exact hcode) rfl hsize with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs
      (runtime_endsAs I (World.init σ A feed) (by simp [World.init, UInt256.size]) hfits) h⟩

/-- Deployment with one ABI-encoded `uint256` argument refines the exported deployment entry. -/
theorem feERC20DeployRefinesExported :
    RefinesDeploy .P0 feERC20CreationBytecode feERC20Bytecode contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  rcases feERC20DeployRefinesModel σ σ₀ g A I _ ⟨v, rfl⟩ hcode hperm with h | ⟨feed, h⟩
  · exact Or.inl h
  · replace h : Agrees .P0 (Ξ σ σ₀ g A I) ((Model.init (ctorTail v) >>= fun _ =>
        pure feERC20Bytecode).exec I (World.init σ A feed)) := by
      simpa [Model.contract, ByteArray.append_empty] using h
    exact Or.inr ⟨feed, Agrees.of_endsAs
      (init_endsAs v _ I (World.init σ A feed) (by simp [World.init, UInt256.size])) h⟩

end FeProofs.ERC20.Exported
