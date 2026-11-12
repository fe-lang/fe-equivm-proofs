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
  rd_run rd to 137 using [hwv, hc, shiftRight160_eq_zero hcanon]
  by_cases henough : (calldataWord I.calldata 36).toNat ≤ (transferBal σ I).toNat
  swap
  · have hlt := Nat.lt_of_not_le henough
    rd_run rd using [slot_hint (isZero_lt_eq_zero hlt)]
    exact agrees_of_rev hcode rd (f := .revert (assertData "ERC20: insufficient balance"))
      (by simp [Model.transferArm, Model.transfer, World.init, exec_nonPayable, hwv, hhead, haddr,
        hbal, hval, hlt]) (by simp)
  have hge := ult_zero henough
  have hnlt : ¬ (transferBal σ I).toNat < (calldataWord I.calldata 36).toNat := Nat.not_lt.mpr henough
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint (isZero_lt_ne_zero henough), slot_hint hge]
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
    rd_run rd using [slot_hint (isZero_lt_ne_zero henough), slot_hint hge,
      slot_hint (addCarry_ne_zero hover)]
    exact agrees_of_rev hcode rd (f := .panic 0x11)
      (by simp [Model.transferArm, Model.transfer, World.init, exec_nonPayable, exec_sstore,
        checkedSub, checkedAdd, hwv, hhead, haddr, hbal, hval, hnlt, hperm, hdeb, htob, hover])
      (by simp)
  rd_run rd using [slot_hint (isZero_lt_ne_zero henough), slot_hint hge,
    slot_hint (addCarry_eq_zero hfit)]
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

/-! ## `approve(address,uint256)` -/

theorem approveArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 0)) :
    ArmAgrees σ σ₀ g A I (Model.approveArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 0) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachApproveBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.approveArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.approveArm, exec_nonPayable, hwv, badHead_of (n := 2) hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 2) hlen hhi
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.approveArm, exec_nonPayable, hwv, hhead,
        show NotAddress (word I.calldata 4) from notAddress_of hcanon]) (by simp)
  have haddr : ¬ NotAddress (word I.calldata 4) := not_notAddress_of hcanon
  rd_run rd to 465 using [hwv, hc, shiftRight160_eq_zero hcanon]
  by_cases hperm : I.perm = true
  · rd_step rd
    rw [keccakWord_mapSlot, keccakWord_mapSlot, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
    exact agrees_of_ret hcode rd
      (w' := { accounts := storeWord I.codeOwner σ
                 (Model.allowanceSlot (UInt256.ofNat I.source.val) (word I.calldata 4))
                 (word I.calldata 36),
               logs := A.logSeries.push ⟨I.codeOwner,
                 #[Model.approvalTopic, UInt256.ofNat I.source.val, word I.calldata 4],
                 (word I.calldata 36).toByteArray⟩ })
      (by simp [Model.approveArm, Model.approve, Model.encodeBool, World.init, exec_nonPayable,
        exec_sstore, exec_emit, hwv, hhead, haddr, hperm]; rfl) rfl
  have hpf : I.perm = false := by simpa using hperm
  rd_step rd
  exact agrees_of_static hcode rd
    (by simp [Model.approveArm, Model.approve, World.init, exec_nonPayable, exec_sstore, hwv,
      hhead, haddr, hpf])

/-! ## `transferFrom(address,address,uint256)` -/

theorem transferFromArm_refines {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 2)) :
    ArmAgrees σ σ₀ g A I (Model.transferFromArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 2) rfl hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachTransferFromBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferFromArm, exec_nonPayable, hwv]) (by simp)
  by_cases hok : 100 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 100 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 3 hsz hsize hbad]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, badHead_of (n := 3) hbad]) (by simp)
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 3) hlen hhi
  have hc := solcCalldataStaticLenCheckOk (words := 3) hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hhead,
        show NotAddress (word I.calldata 4) from notAddress_of hc0]) (by simp)
  have ha0 : ¬ NotAddress (word I.calldata 4) := not_notAddress_of hc0
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hhead, ha0,
        show NotAddress (word I.calldata 36) from notAddress_of hc1]) (by simp)
  have ha1 : ¬ NotAddress (word I.calldata 36) := not_notAddress_of hc1
  have hval : word I.calldata 68 = calldataWord I.calldata 68 := rfl
  have hal : slotWord I σ (Model.allowanceSlot (word I.calldata 4) (UInt256.ofNat I.source.val))
      = transferFromAllowance σ I := rfl
  have hb0 : slotWord I σ (Model.balanceSlot (word I.calldata 4)) = transferFromBal σ I := rfl
  rd_run rd to 593 using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  by_cases hallow : (calldataWord I.calldata 68).toNat ≤ (transferFromAllowance σ I).toNat
  swap
  · have hlt := Nat.lt_of_not_le hallow
    rd_run rd using [slot_hint (isZero_lt_eq_zero hlt)]
    exact agrees_of_rev hcode rd (f := .revert (assertData "ERC20: insufficient allowance"))
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable, hwv,
        hhead, ha0, ha1, hval, hal, hlt]) (by simp)
  have hnal : ¬ (transferFromAllowance σ I).toNat < (calldataWord I.calldata 68).toNat :=
    Nat.not_lt.mpr hallow
  by_cases hbal : (calldataWord I.calldata 68).toNat ≤ (transferFromBal σ I).toNat
  swap
  · have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow),
      slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .revert (assertData "ERC20: insufficient balance"))
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable, hwv,
        hhead, ha0, ha1, hval, hal, hb0, hnal, hlt]) (by simp)
  have hnb : ¬ (transferFromBal σ I).toNat < (calldataWord I.calldata 68).toNat :=
    Nat.not_lt.mpr hbal
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (ult_zero hbal)]
    exact agrees_of_static hcode rd
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
        exec_sstore, checkedSub, hwv, hhead, ha0, ha1, hval, hal, hb0, hnal, hnb, hpf])
  have hsp : storeWord I.codeOwner σ
      (Model.allowanceSlot (word I.calldata 4) (UInt256.ofNat I.source.val))
      (UInt256.sub (transferFromAllowance σ I) (calldataWord I.calldata 68))
      = transferFromSpent σ I := rfl
  have hb1 : slotWord I (transferFromSpent σ I) (Model.balanceSlot (word I.calldata 4))
      = transferFromBal (transferFromSpent σ I) I := rfl
  by_cases hsub : (calldataWord I.calldata 68).toNat ≤
      (transferFromBal (transferFromSpent σ I) I).toNat
  swap
  · have hlt := Nat.lt_of_not_le hsub
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (ult_zero hbal),
      slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .panic 0x11)
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
        exec_sstore, checkedSub, hwv, hhead, ha0, ha1, hval, hal, hb0, hnal, hnb, hperm, hsp,
        hb1, hlt]) (by simp)
  have hnsub : ¬ (transferFromBal (transferFromSpent σ I) I).toNat
      < (calldataWord I.calldata 68).toNat := Nat.not_lt.mpr hsub
  have hdeb : storeWord I.codeOwner (transferFromSpent σ I)
      (Model.balanceSlot (word I.calldata 4))
      (UInt256.sub (transferFromBal (transferFromSpent σ I) I) (calldataWord I.calldata 68))
      = transferFromDebited σ I := rfl
  have htob : slotWord I (transferFromDebited σ I) (Model.balanceSlot (word I.calldata 36))
      = transferFromToBal σ I := rfl
  by_cases hfit : (transferFromToBal σ I).toNat + (calldataWord I.calldata 68).toNat < UInt256.size
  swap
  · have hover := Nat.le_of_not_lt hfit
    rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (ult_zero hbal),
      slot_hint (ult_zero hsub), slot_hint (addCarry_ne_zero hover)]
    exact agrees_of_rev hcode rd (f := .panic 0x11)
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
        exec_sstore, checkedSub, checkedAdd, hwv, hhead, ha0, ha1, hval, hal, hb0, hnal, hnb,
        hperm, hsp, hb1, hnsub, hdeb, htob, hover]) (by simp)
  rd_run rd using [slot_hint (isZero_lt_ne_zero hallow), slot_hint (ult_zero hbal),
    slot_hint (ult_zero hsub), slot_hint (addCarry_eq_zero hfit)]
  simp only [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd
    (w' := { accounts := storeWord I.codeOwner (transferFromDebited σ I)
               (Model.balanceSlot (word I.calldata 36))
               (transferFromToBal σ I + calldataWord I.calldata 68),
             logs := A.logSeries.push ⟨I.codeOwner,
               #[Model.transferTopic, word I.calldata 4, word I.calldata 36],
               (calldataWord I.calldata 68).toByteArray⟩ })
    (by simp [Model.transferFromArm, Model.transferFrom, Model.encodeBool, World.init,
      exec_nonPayable, exec_sstore, exec_emit, checkedSub, checkedAdd, hwv, hhead, ha0, ha1, hval,
      hal, hb0, hnal, hnb, hperm, hsp, hb1, hnsub, hdeb, htob, Nat.not_le.mpr hfit]; rfl) rfl

/-! ## The runtime entry -/

theorem feERC20RefinesModel : Refines .P0 feERC20Bytecode Model.contract := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hsize
  refine RefinesFor.closed ?_
  show ArmAgrees σ σ₀ g A I Model.runtime
  have sel : ∀ i, (¬ selIs I (feERC20SelBytes i)) →
      (feERC20SelBytes i == I.calldata.extract 0 4) = false := fun i h => by simpa [selIs] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feERC20X_short hcode (by omega))
      (f := .revert ByteArray.empty)
      (by simp [Model.runtime, show I.calldata.size < 4 by omega]) (by simp)
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feERC20SelBytes 0)
  · have e : Model.runtime.exec I (World.init σ A)
        = (Model.approveArm I.calldata).exec I (World.init σ A) := by
      simp [Model.runtime, hn4, show (Model.approveSelector == I.calldata.extract 0 4) = true from h0]
    rw [ArmAgrees, e]; exact approveArm_refines hcode hsize h0
  have n0 : (Model.approveSelector == I.calldata.extract 0 4) = false := sel 0 h0
  by_cases h1 : selIs I (feERC20SelBytes 1)
  · have e : Model.runtime.exec I (World.init σ A) = Model.totalSupplyArm.exec I (World.init σ A) := by
      simp [Model.runtime, hn4, n0,
        show (Model.totalSupplySelector == I.calldata.extract 0 4) = true from h1]
    rw [ArmAgrees, e]; exact totalSupplyArm_refines hcode hsize h1
  have n1 : (Model.totalSupplySelector == I.calldata.extract 0 4) = false := sel 1 h1
  by_cases h2 : selIs I (feERC20SelBytes 2)
  · have e : Model.runtime.exec I (World.init σ A)
        = (Model.transferFromArm I.calldata).exec I (World.init σ A) := by
      simp [Model.runtime, hn4, n0, n1,
        show (Model.transferFromSelector == I.calldata.extract 0 4) = true from h2]
    rw [ArmAgrees, e]; exact transferFromArm_refines hcode hsize h2
  have n2 : (Model.transferFromSelector == I.calldata.extract 0 4) = false := sel 2 h2
  by_cases h3 : selIs I (feERC20SelBytes 3)
  · have e : Model.runtime.exec I (World.init σ A)
        = (Model.balanceOfArm I.calldata).exec I (World.init σ A) := by
      simp [Model.runtime, hn4, n0, n1, n2,
        show (Model.balanceOfSelector == I.calldata.extract 0 4) = true from h3]
    rw [ArmAgrees, e]; exact balanceOfArm_refines hcode hsize h3
  have n3 : (Model.balanceOfSelector == I.calldata.extract 0 4) = false := sel 3 h3
  by_cases h4 : selIs I (feERC20SelBytes 4)
  · have e : Model.runtime.exec I (World.init σ A)
        = (Model.transferArm I.calldata).exec I (World.init σ A) := by
      simp [Model.runtime, hn4, n0, n1, n2, n3,
        show (Model.transferSelector == I.calldata.extract 0 4) = true from h4]
    rw [ArmAgrees, e]; exact transferArm_refines hcode hsize h4
  have n4 : (Model.transferSelector == I.calldata.extract 0 4) = false := sel 4 h4
  by_cases h5 : selIs I (feERC20SelBytes 5)
  · have e : Model.runtime.exec I (World.init σ A)
        = (Model.allowanceArm I.calldata).exec I (World.init σ A) := by
      simp [Model.runtime, hn4, n0, n1, n2, n3, n4,
        show (Model.allowanceSelector == I.calldata.extract 0 4) = true from h5]
    rw [ArmAgrees, e]; exact allowanceArm_refines hcode hsize h5
  have n5 : (Model.allowanceSelector == I.calldata.extract 0 4) = false := sel 5 h5
  exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode
    (feERC20X_noMatch hcode hsz hsize (feERC20NoSelectorMatches h0 h1 h2 h3 h4 h5))
    (f := .revert ByteArray.empty)
    (by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5]) (by simp)

/-! ## Deployment -/

/-- Deployment with one ABI-encoded `uint256` argument, the initial supply. -/
theorem feERC20DeployRefinesModel :
    RefinesDeploy .P0 feERC20CreationBytecode feERC20Bytecode Model.contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  refine RefinesDeploy.of_unit_closed (init := Model.init) (fun _ => rfl) ?_
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode (feERC20CtorRev hcode hwv)
      (f := .revert ByteArray.empty)
      (by simp [Model.init, exec_nonPayable, hwv]) (by simp)
  have hsz : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hword : word (ctorTail v) 0 = v := by
    show uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v
    rw [readBytes_all32 _ hsz, ctorTail, word_toBytesBE_toByteArray_eq_toByteArray,
      uInt256OfByteArray_toByteArray]
  have hslot : Model.balanceSlot (UInt256.ofNat I.source.val)
      = keccakWord (UInt256.ofNat 96) (UInt256.ofNat 64) (ctorKeyMem v I.source) :=
    (ctorKey_slot v I.source).symm
  exact agrees_of_ret (g := Sat256.ofUInt256 g) hcode (feERC20CtorRet v hcode hwv hperm)
    (w' := { accounts := storeWord I.codeOwner (storeWord I.codeOwner σ
               (Model.balanceSlot (UInt256.ofNat I.source.val)) v) Model.totalSupplySlot v,
             logs := A.logSeries.push ⟨I.codeOwner,
               #[Model.transferTopic, ⟨0⟩, UInt256.ofNat I.source.val], v.toByteArray⟩ })
    (by simp [Model.init, Model.initBody, World.init, exec_nonPayable,
      exec_sstore, exec_emit, hwv, hperm, hsz, hword])
    (by rw [hslot]; rfl)

end FeProofs.ERC20
