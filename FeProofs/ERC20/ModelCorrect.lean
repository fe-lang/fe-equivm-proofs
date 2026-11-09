import FeProofs.ERC20.Correct
import FeProofs.ERC20.Model
import Fe.EVM.Reach

/-!
# FeERC20: the runtime bytecode refines the model

One theorem per entry arm: on calldata with that arm's selector, the bytecode runs out of gas or
agrees with the arm's model.  The EVM half of each is the trace the Stele proofs establish,
restated as terminals that mention the bytecode only.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}

/-- What an arm must show: out of gas, or agreement with its model. -/
abbrev ArmAgrees (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (arm : FeM ByteArray) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g A I) (arm.exec I (World.init σ A))

theorem notAddress_of {w : UInt256} (h : ¬ w.toNat < EVM.addressModulus) : NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

theorem not_notAddress_of {w : UInt256} (h : w.toNat < EVM.addressModulus) : ¬ NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

theorem badHead_of {cd : ByteArray} {n : ℕ} (h : cd.size < 4 + 32 * n ∨ 2 ^ 255 + 4 ≤ cd.size) :
    BadHead cd n := h

theorem not_badHead_of {cd : ByteArray} {n : ℕ} (hlen : 4 + 32 * n ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) : ¬ BadHead cd n := by
  unfold BadHead; omega

/-! ## `totalSupply()` -/

theorem totalSupplyArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 1)) :
    ArmAgrees σ σ₀ g A I Model.totalSupplyArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 1) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTotalSupplyBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.totalSupplyArm, exec_nonPayable, hwv]) (by simp)
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.totalSupplyArm, Model.totalSupply, exec_nonPayable, hwv]; rfl) rfl

/-! ## `balanceOf(address)` -/

theorem balanceOfArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 3)) :
    ArmAgrees σ σ₀ g A I (Model.balanceOfArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 3) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachBalanceOfBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv, badHead_of (n := 1) hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 1) hlen hhi
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize,
      shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.balanceOfArm, exec_nonPayable, hwv, hhead,
        show NotAddress (word I.calldata 4) from notAddress_of hcanon]) (by simp)
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize, shiftRight160_eq_zero hcanon]
  rw [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.balanceOfArm, Model.balanceOf, exec_nonPayable, hwv, hhead,
      show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hcanon]; rfl) rfl

/-! ## `allowance(address,address)` -/

theorem allowanceArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 5)) :
    ArmAgrees σ σ₀ g A I (Model.allowanceArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 5) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachAllowanceBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.allowanceArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, badHead_of (n := 2) hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 2) hlen hhi
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hhead,
        show NotAddress (word I.calldata 4) from notAddress_of hc0]) (by simp)
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hhead,
        show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hc0,
        show NotAddress (word I.calldata 36) from notAddress_of hc1]) (by simp)
  rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  rw [keccakWord_mapSlot, keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.allowanceArm, Model.allowance, exec_nonPayable, hwv, hhead,
      show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hc0,
      show ¬ NotAddress (word I.calldata 36) from not_notAddress_of hc1]; rfl) rfl

/-! ## `transfer(address,uint256)` -/

theorem transferArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 4)) :
    ArmAgrees σ σ₀ g A I (Model.transferArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 4) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTransferBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferArm, exec_nonPayable, hwv, badHead_of (n := 2) hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 2) hlen hhi
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferArm, exec_nonPayable, hwv, hhead,
        show NotAddress (word I.calldata 4) from notAddress_of hcanon]) (by simp)
  have haddr : ¬ NotAddress (word I.calldata 4) := not_notAddress_of hcanon
  have hbal : slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val)) = transferBal σ I := rfl
  have hval : word I.calldata 36 = calldataWord I.calldata 36 := rfl
  rd_run rd to 613 using [hwv, hc, shiftRight160_eq_zero hcanon]
  by_cases henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat
  swap
  · have hlt := Nat.lt_of_not_le henough
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .revert (assertData "ERC20: insufficient balance"))
      (by simp [Model.transferArm, Model.transfer, World.init, exec_nonPayable, hwv, hhead, haddr,
        hbal, hval, hlt]) (by simp)
  have hge := ult_zero henough
  have hnlt : ¬ (transferBal σ I).toNat < (calldataWord I.calldata 36).toNat := Nat.not_lt.mpr henough
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint hge]
    exact agrees_of_static hcode rd
      (by simp [Model.transferArm, Model.transfer, World.init, exec_nonPayable, exec_sstore,
        checkedSub, hwv, hhead, haddr, hbal, hval, hnlt, hpf])
  have hdeb : storeWord I.codeOwner σ (Model.balanceSlot (UInt256.ofNat I.source.val))
      (UInt256.sub (transferBal σ I) (calldataWord I.calldata 36)) = transferDebited σ I := rfl
  have htob : slotWord I (transferDebited σ I) (Model.balanceSlot (word I.calldata 4))
      = transferToBal σ I := rfl
  by_cases hfit : (transferToBal σ I).toNat + (calldataWord I.calldata 36).toNat < UInt256.size
  swap
  · have hover := Nat.le_of_not_lt hfit
    rd_run rd using [slot_hint hge, slot_hint (addCarry_ne_zero hover)]
    exact agrees_of_rev hcode rd (f := .panic 0x11)
      (by simp [Model.transferArm, Model.transfer, World.init, exec_nonPayable, exec_sstore,
        checkedSub, checkedAdd, hwv, hhead, haddr, hbal, hval, hnlt, hperm, hdeb, htob, hover])
      (by simp)
  rd_run rd using [slot_hint hge, slot_hint (addCarry_eq_zero hfit)]
  simp only [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd
    (w' := { accounts := storeWord I.codeOwner (transferDebited σ I)
               (Model.balanceSlot (word I.calldata 4))
               (transferToBal σ I + calldataWord I.calldata 36),
             logs := A.logSeries.push ⟨I.codeOwner,
               #[Model.transferTopic, UInt256.ofNat I.source.val, word I.calldata 4],
               (calldataWord I.calldata 36).toByteArray⟩ })
    (by simp [Model.transferArm, Model.transfer, Model.encodeBool, World.init, exec_nonPayable,
      exec_sstore, exec_emit, checkedSub, checkedAdd, hwv, hhead, haddr, hbal, hval, hnlt, hperm,
      hdeb, htob, Nat.not_le.mpr hfit]; rfl) rfl

end FeProofs.ERC20
