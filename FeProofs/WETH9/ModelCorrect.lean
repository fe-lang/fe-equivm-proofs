import FeProofs.WETH9.Correct
import FeProofs.WETH9.Model
import Fe.EVM.Reach

/-!
# FeWETH9: the runtime bytecode refines the model

One theorem per entry arm: on calldata with that arm's selector, the bytecode runs out of gas or
agrees with the arm's model, for some feed.  The EVM half of each is the trace the Stele proofs
establish, restated as terminals that mention the bytecode only.  `withdraw`'s value transfer is
EVMLean's `Θ` in both, through `call_feed`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}

/-- What an arm that makes no call must show: out of gas, or agreement with its model. -/
abbrev ArmAgrees (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (arm : FeM ByteArray) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g A I) (arm.exec I (World.init σ A))

/-- What an arm must show: out of gas, or agreement with its model under some feed. -/
abbrev ArmAgreesFeed (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (arm : FeM ByteArray) : Prop :=
  Ξ σ σ₀ g A I = .error .OutOfGass ∨
    ∃ feed, Agrees .P0 (Ξ σ σ₀ g A I) (arm.exec I (World.init σ A feed))

theorem ArmAgrees.feed {g : UInt256} {arm : FeM ByteArray} (h : ArmAgrees σ σ₀ g A I arm) :
    ArmAgreesFeed σ σ₀ g A I arm :=
  h.imp id fun h => ⟨[], h⟩

theorem notAddress_of {w : UInt256} (h : ¬ w.toNat < EVM.addressModulus) : NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

theorem not_notAddress_of {w : UInt256} (h : w.toNat < EVM.addressModulus) : ¬ NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

theorem badHead_of {cd : ByteArray} {n : ℕ} (h : cd.size < 4 + 32 * n ∨ 2 ^ 255 + 4 ≤ cd.size) :
    BadHead cd n := h

theorem not_badHead_of {cd : ByteArray} {n : ℕ} (hlen : 4 + 32 * n ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) : ¬ BadHead cd n := by
  unfold BadHead; omega

/-- `agrees_of_ret` for a model run that returns `o` and some world with the accounts `σ'`. -/
theorem agrees_of_ret' {g : Sat256} {code o : ByteArray} {σ' : AccountMap}
    {r : Option (Except (Exit World) (ByteArray × World))}
    (hcode : I.code = code) (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : ∃ w', r = some (.ok (o, w')) ∧ w'.accounts = σ') :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  obtain ⟨w', hm, hw⟩ := hm
  exact agrees_of_ret hcode h hm hw

/-- The maximum word, as the bytecode computes it. -/
theorem lnot_zero : UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by decide

/-! ## `totalSupply()` -/

theorem totalSupplyArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 2)) :
    ArmAgrees σ σ₀ g A I Model.totalSupplyArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 2) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachTotalSupplyBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.totalSupplyArm, exec_nonPayable, hwv]) (by simp)
  rd_run rd using [hwv]
  have rd := rd.selfbalance (by native_decide) (by simp)
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.totalSupplyArm, Model.totalSupply, selfbalance, exec_nonPayable, hwv]; rfl) rfl

/-! ## `balanceOf(address)` -/

theorem balanceOfArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 6)) :
    ArmAgrees σ σ₀ g A I (Model.balanceOfArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 6) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachBalanceOfBody (g := Sat256.ofUInt256 g) (σ := σ)
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
  u256_lits at rd
  rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.balanceOfArm, Model.balanceOf, exec_nonPayable, hwv, hhead,
      show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hcanon]; rfl) rfl

/-! ## `allowance(address,address)` -/

theorem allowanceArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 10)) :
    ArmAgrees σ σ₀ g A I (Model.allowanceArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 10) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachAllowanceBody (g := Sat256.ofUInt256 g) (σ := σ)
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
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0,
      shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.allowanceArm, exec_nonPayable, hwv, hhead,
        show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hc0,
        show NotAddress (word I.calldata 36) from notAddress_of hc1]) (by simp)
  rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  u256_lits at rd
  rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.allowanceArm, Model.allowance, exec_nonPayable, hwv, hhead,
      show ¬ NotAddress (word I.calldata 4) from not_notAddress_of hc0,
      show ¬ NotAddress (word I.calldata 36) from not_notAddress_of hc1]; rfl) rfl

/-! ## `decimals()` -/

theorem decimalsArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 5)) :
    ArmAgrees σ σ₀ g A I Model.decimalsArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 5) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachDecimalsBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.decimalsArm, exec_nonPayable, hwv]) (by simp)
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _), u256_land_comm] at rd
  exact agrees_of_ret hcode rd (w' := World.init σ A)
    (by simp [Model.decimalsArm, Model.decimals, exec_nonPayable, hwv]; rfl) rfl

/-! ## `approve(address,uint256)` -/

theorem approveArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 1)) :
    ArmAgrees σ σ₀ g A I (Model.approveArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 1) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachApproveBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
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
  rd_run rd to 689 using [hwv, hc, shiftRight160_eq_zero hcanon]
  by_cases hperm : I.perm = true
  · rd_step rd
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
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

/-! ## `transfer(address,uint256)` -/

theorem transferArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 8)) :
    ArmAgrees σ σ₀ g A I (Model.transferArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 8) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachTransferBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
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
  rd_run rd to 1285 using [hwv, hc, shiftRight160_eq_zero hcanon]
  have hb : slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val)) =
      solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source) ⟨3⟩) := rfl
  have hval : word I.calldata 36 = calldataWord I.calldata 36 := rfl
  by_cases hbal : (calldataWord I.calldata 36).toNat ≤
      (solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source) ⟨3⟩)).toNat
  swap
  · have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .panic 0x01)
      (by simp [Model.transferArm, Model.transferFrom, World.init, exec_nonPayable, hwv, hhead,
        haddr, hb, hval, hlt]) (by simp)
  have hnlt := Nat.not_lt.mpr hbal
  rd_run rd to 1455 using [slot_hint (ult_zero hbal), u256_eq_refl (addrWord I.source)]
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    exact agrees_of_static hcode (tfTailStatic hpf rd)
      (by simp [Model.transferArm, Model.transferFrom, World.init, exec_nonPayable, exec_sstore,
        hwv, hhead, haddr, hb, hval, hnlt, hpf])
  obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret' hcode rd
    (by simp [Model.transferArm, Model.transferFrom, Model.encodeBool, World.init,
      exec_nonPayable, exec_sstore, exec_emit, hwv, hhead, haddr, hb, hval, hnlt, hperm]; exact ⟨rfl, rfl⟩)

/-! ## `transferFrom(address,address,uint256)` -/

theorem transferFromArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 3)) :
    ArmAgrees σ σ₀ g A I (Model.transferFromArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 3) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachTransferFromBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
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
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0,
      shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.transferFromArm, exec_nonPayable, hwv, hhead, ha0,
        show NotAddress (word I.calldata 36) from notAddress_of hc1]) (by simp)
  have ha1 : ¬ NotAddress (word I.calldata 36) := not_notAddress_of hc1
  rd_run rd to 1285 using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  have hval : word I.calldata 68 = calldataWord I.calldata 68 := rfl
  have hb : slotWord I σ (Model.balanceSlot (word I.calldata 4)) =
      solcSlotWord σ I (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨3⟩) := rfl
  by_cases hbal : (calldataWord I.calldata 68).toNat ≤
      (solcSlotWord σ I (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨3⟩)).toNat
  swap
  · have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .panic 0x01)
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable, hwv,
        hhead, ha0, ha1, hval, hb, hlt]) (by simp)
  have hnlt := Nat.not_lt.mpr hbal
  rd_run rd to 1308 using [slot_hint (ult_zero hbal)]
  by_cases hself : calldataWord I.calldata 4 = addrWord I.source
  · -- `src` is the caller: no allowance
    rd_run rd to 1455 using [(show UInt256.eq (calldataWord I.calldata 4) (addrWord I.source) =
      ⟨1⟩ by rw [hself]; exact u256_eq_refl _)]
    have hs : UInt256.ofNat I.source.val = word I.calldata 4 := hself.symm
    by_cases hperm : I.perm = true
    swap
    · have hpf : I.perm = false := by simpa using hperm
      exact agrees_of_static hcode (tfTailStatic hpf rd)
        (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
          exec_sstore, hwv, hhead, ha0, ha1, hval, hb, hnlt, hs, hpf])
    obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
    rd_run rd
    u256_lits at rd
    rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
    exact agrees_of_ret' hcode rd
      (by simp [Model.transferFromArm, Model.transferFrom, Model.encodeBool, World.init,
        exec_nonPayable, exec_sstore, exec_emit, hwv, hhead, ha0, ha1, hval, hb, hnlt,
        hs, hperm]; exact ⟨rfl, rfl⟩)
  -- `src` is not the caller
  have hne : word I.calldata 4 ≠ UInt256.ofNat I.source.val := hself
  have ha : slotWord I σ (Model.allowanceSlot (word I.calldata 4)
        (UInt256.ofNat I.source.val)) =
      solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source)
        (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨4⟩)) := rfl
  rd_run rd to 1317 using [u256_eq_of_ne hself]
  by_cases hmaxw : solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source)
      (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨4⟩)) = UInt256.lnot ⟨0⟩
  · -- the maximum allowance is not spent
    rd_run rd to 1455 using [slot_hint (ne_of_eq_of_ne (show UInt256.eq (UInt256.lnot ⟨0⟩)
      (solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source)
        (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨4⟩))) = ⟨1⟩ by
          rw [hmaxw]; exact u256_eq_refl _) (by decide))]
    rw [lnot_zero] at hmaxw
    by_cases hperm : I.perm = true
    swap
    · have hpf : I.perm = false := by simpa using hperm
      exact agrees_of_static hcode (tfTailStatic hpf rd)
        (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
          exec_sstore, hwv, hhead, ha0, ha1, hval, hb, hnlt, hne, ha, hmaxw, hpf])
    obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
    rd_run rd
    u256_lits at rd
    rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
    exact agrees_of_ret' hcode rd
      (by simp [Model.transferFromArm, Model.transferFrom, Model.encodeBool, World.init,
        exec_nonPayable, exec_sstore, exec_emit, hwv, hhead, ha0, ha1, hval, hb, hnlt,
        hne, ha, hmaxw, hperm]; exact ⟨rfl, rfl⟩)
  have hmax : solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source)
      (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨4⟩)) ≠ UInt256.ofNat (UInt256.size - 1) := by
    rw [← lnot_zero]; exact hmaxw
  rd_run rd to 1351 using [slot_hint (u256_eq_of_ne (Ne.symm hmaxw))]
  by_cases hallow : (calldataWord I.calldata 68).toNat ≤
      (solcSlotWord σ I (FeProofs.mapSlot (addrWord I.source)
        (FeProofs.mapSlot (calldataWord I.calldata 4) ⟨4⟩))).toNat
  swap
  · -- short allowance
    have hlt := Nat.lt_of_not_le hallow
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact agrees_of_rev hcode rd (f := .panic 0x01)
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable, hwv,
        hhead, ha0, ha1, hval, hb, hnlt, hne, ha, hmax, hlt]) (by simp)
  have hnal := Nat.not_lt.mpr hallow
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the allowance `SSTORE` halts
    have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint (ult_zero hallow)]
    exact agrees_of_static hcode rd
      (by simp [Model.transferFromArm, Model.transferFrom, World.init, exec_nonPayable,
        exec_sstore, hwv, hhead, ha0, ha1, hval, hb, hnlt, hne, ha, hmax, hnal, hpf])
  rd_run rd to 1455 using [slot_hint (ult_zero hallow)]
  simp (disch := (first | rfl | decide | omega)) only [keccakWord_mapSlotAtWord] at rd
  obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  exact agrees_of_ret' hcode rd
    (by simp [Model.transferFromArm, Model.transferFrom, Model.encodeBool, World.init,
      exec_nonPayable, exec_sstore, exec_emit, hwv, hhead, ha0, ha1, hval, hb, hnlt,
      hne, ha, hmax, hnal, hperm]; exact ⟨rfl, rfl⟩)

/-! ## `deposit()` and the fallback -/

theorem depositArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 9)) :
    ArmAgrees σ σ₀ g A I Model.depositArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 9) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachDepositBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hperm : I.perm = true
  · rd_run rd
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide), byteArray_readWithPadding_zero] at rd
    exact agrees_of_ret' hcode rd
      (by simp [Model.depositArm, Model.deposit, World.init, callvalue, exec_sstore, exec_emit,
        hperm]; rw [u256_add_comm]; rfl)
  have hpf : I.perm = false := by simpa using hperm
  rd_run rd
  exact agrees_of_static hcode rd
    (by simp [Model.depositArm, Model.deposit, World.init, callvalue, exec_sstore, hpf])

/-- From the fallback entry (pc 771), reached with the selector word or nothing on the stack. -/
theorem fallbackFrom771_refines {g aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = feWETH9Bytecode) (hR : R.length ≤ 1)
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 771) R entryMem aw ByteArray.empty σ k C) :
    ArmAgrees σ σ₀ g A I Model.depositArm := by
  by_cases hperm : I.perm = true
  · rd_run rd using [hR]
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide), byteArray_readWithPadding_zero] at rd
    exact agrees_of_ret' hcode rd
      (by simp [Model.depositArm, Model.deposit, World.init, callvalue, exec_sstore, exec_emit,
        hperm]; rw [u256_add_comm]; rfl)
  have hpf : I.perm = false := by simpa using hperm
  rd_run rd using [hR]
  exact agrees_of_static hcode rd
    (by simp [Model.depositArm, Model.deposit, World.init, callvalue, exec_sstore, hpf])

/-- Calldata shorter than a selector, or matching none, runs the payable fallback. -/
theorem fallback_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hnm : 4 ≤ I.calldata.size →
      ∀ i, i < 11 → (feWETH9SelBytes i == I.calldata.extract 0 4) = false) :
    ArmAgrees σ σ₀ g A I Model.depositArm := by
  have rd := RD.initState (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · rd_run rd to 771 using [lt_four_ne_zero_of_lt (by omega)]
    exact fallbackFrom771_refines hcode (by simp) rd
  have hc := lt_four_eq_zero_of_ge hsz hsize
  have miss : ∀ (i : ℕ) (sel : UInt256), i < 11 →
      UInt256.eq sel (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)
        = (if (feWETH9SelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩) →
      UInt256.eq (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) sel =
          UInt256.ofNat 0 := by
    intro i sel hi e
    simp only [hnm hsz i hi, Bool.false_eq_true, if_false] at e
    rw [uInt256_eq_comm]
    exact e
  have n0 := miss 0 _ (by omega) (nameEvmSelector hsz)
  have n1 := miss 1 _ (by omega) (approveEvmSelector hsz)
  have n2 := miss 2 _ (by omega) (totalSupplyEvmSelector hsz)
  have n3 := miss 3 _ (by omega) (transferFromEvmSelector hsz)
  have n4 := miss 4 _ (by omega) (withdrawEvmSelector hsz)
  have n5 := miss 5 _ (by omega) (decimalsEvmSelector hsz)
  have n6 := miss 6 _ (by omega) (balanceOfEvmSelector hsz)
  have n7 := miss 7 _ (by omega) (symbolEvmSelector hsz)
  have n8 := miss 8 _ (by omega) (transferEvmSelector hsz)
  have n9 := miss 9 _ (by omega) (depositEvmSelector hsz)
  have n10 := miss 10 _ (by omega) (allowanceEvmSelector hsz)
  by_cases hp1 : UInt256.lt (UInt256.shiftRight (uInt256OfByteArray
      (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))
        (UInt256.ofNat 826074471) = UInt256.ofNat 0
  · by_cases hp2 : UInt256.lt (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))
          (UInt256.ofNat 2835717307) = UInt256.ofNat 0
    · rd_run rd to 771 using [hc, hp1, hp2, n8, n9, n10]
      exact fallbackFrom771_refines hcode (by simp) rd
    · rd_run rd to 771 using [hc, hp1, hp2, n5, n6, n7]
      exact fallbackFrom771_refines hcode (by simp) rd
  · by_cases hp3 : UInt256.lt (UInt256.shiftRight (uInt256OfByteArray
        (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))
          (UInt256.ofNat 404098525) = UInt256.ofNat 0
    · rd_run rd to 771 using [hc, hp1, hp3, n2, n3, n4]
      exact fallbackFrom771_refines hcode (by simp) rd
    · rd_run rd to 771 using [hc, hp1, hp3, n0, n1]
      exact fallbackFrom771_refines hcode (by simp) rd

/-! ## `withdraw(uint256)` -/

/-- From the transfer's `CALL` (pc 561), with the debit stored: the model's `call` makes the same
    message call for some feed entry, then both check `success`, log `Withdrawal` and return
    nothing. -/
theorem withdrawCall_refines {g gas aw : UInt256} {mem : ByteArray} {k C : ℕ}
    {inOff outOff : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hhead : ¬ BadHead I.calldata 1)
    (hnlt : ¬ (slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val))).toNat <
      (word I.calldata 4).toNat)
    (hgas : (if word I.calldata 4 = ⟨0⟩ then UInt256.ofNat 2300 else UInt256.ofNat 0) = gas)
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 561)
      [gas, UInt256.ofNat I.source.val, word I.calldata 4, inOff, ⟨0⟩, outOff, ⟨0⟩, gas,
        word I.calldata 4, UInt256.ofNat I.source.val]
      mem aw ByteArray.empty
      (storeWord I.codeOwner σ (Model.balanceSlot (UInt256.ofNat I.source.val))
        (slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val)) - word I.calldata 4))
      k C) :
    ArmAgreesFeed σ σ₀ g A I (Model.withdrawArm I.calldata) := by
  obtain ⟨s, z, o, σ', logs, aw', k', C', hcall, rd⟩ := call_feed rd (by native_decide)
    (Or.inl hperm) (by simp)
    (w := { accounts := storeWord I.codeOwner σ (Model.balanceSlot (UInt256.ofNat I.source.val))
              (slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val)) - word I.calldata 4)
            logs := A.logSeries })
    (argsPtr := ⟨0⟩) (argsLen := ⟨0⟩) (retPtr := ⟨0⟩) (retLen := ⟨0⟩) [] rfl
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero,
      byteArray_readWithPadding_zero])
  rw [← hgas] at hcall
  refine Or.imp id (fun h => ⟨[s], h⟩) ?_
  cases z <;> simp only [Bool.false_eq_true, ↓reduceIte] at rd
  · rd_run rd
    exact agrees_of_rev hcode rd (f := .panic 0x01)
      (by simp [Model.withdrawArm, Model.withdraw, World.init, exec_nonPayable, exec_sstore, hwv,
        hhead, hnlt, hperm, hcall]) (by simp)
  · rd_run rd
    u256_lits at rd
    rw [byteArray_readWithPadding_zero] at rd
    exact agrees_of_ret' hcode rd
      (by simp [Model.withdrawArm, Model.withdraw, World.init, exec_nonPayable, exec_sstore,
        exec_emit, hwv, hhead, hnlt, hperm, hcall, show UInt256.size ≠ 1 by decide])

theorem withdrawArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 4)) :
    ArmAgreesFeed σ σ₀ g A I (Model.withdrawArm I.calldata) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 4) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachWithdrawBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact ArmAgrees.feed (agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.withdrawArm, exec_nonPayable, hwv]) (by simp))
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact ArmAgrees.feed (agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.withdrawArm, exec_nonPayable, hwv, badHead_of (n := 1) hbad]) (by simp))
  obtain ⟨hlen, hhi⟩ := hok
  have hhead := not_badHead_of (n := 1) hlen hhi
  rd_run rd to 469 using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize]
  have hb : slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val)) = withdrawBal σ I := rfl
  have hval : word I.calldata 4 = withdrawWad I := rfl
  by_cases henough : (withdrawWad I).toNat ≤ (withdrawBal σ I).toNat
  swap
  · have hlt := Nat.lt_of_not_le henough
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact ArmAgrees.feed (agrees_of_rev hcode rd (f := .panic 0x01)
      (by simp [Model.withdrawArm, Model.withdraw, World.init, exec_nonPayable, hwv, hhead, hb,
        hval, hlt]) (by simp))
  have hnlt : ¬ (slotWord I σ (Model.balanceSlot (UInt256.ofNat I.source.val))).toNat <
      (word I.calldata 4).toNat := Nat.not_lt.mpr henough
  have hge := ult_zero henough
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint hge]
    exact ArmAgrees.feed (agrees_of_static hcode rd
      (by simp [Model.withdrawArm, Model.withdraw, World.init, exec_nonPayable, exec_sstore, hwv,
        hhead, hnlt, hpf]))
  rd_run rd to 495 using [slot_hint hge]
  by_cases hz : withdrawWad I = UInt256.ofNat 0 <;>
  · rd_run rd to 542 using [hz]
    u256_lits at rd
    rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
      keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide)] at rd
    rd_step rd
    exact withdrawCall_refines hcode hperm hwv hhead hnlt (by first
      | (rw [if_pos (show word I.calldata 4 = ⟨0⟩ from hval.trans hz)]; try rfl)
      | (rw [if_neg (show ¬ word I.calldata 4 = ⟨0⟩ from fun h => hz (hval.symm.trans h))]
         try rfl))
      rd

/-! ## `name()` and `symbol()` -/

open Strings in
/-- A string getter from the call of `SolString::load` (pc 860) on `slot`, with return address
    `ret`, from where it jumps to the return encoder (pc 1228, `hjump`): both return the string's
    ABI encoding, both panic when it takes `2 ^ 64` bytes or more, and both revert on a malformed
    head. -/
theorem stringReturn_refines {g : UInt256} {slot ret : UInt256} {R : List UInt256} {aw : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hret : (D_J feWETH9Bytecode 0).contains ret = true) (hR : R.length ≤ 990)
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 860) (slot :: ret :: R) entryMem aw rdata σ k C)
    (hjump : ∀ M aw k C n, RD feWETH9Bytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ret
        (UInt256.ofNat 224 :: UInt256.ofNat n :: R) M aw rdata σ k C →
      ∃ aw' k' C', RD feWETH9Bytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 1228)
        (UInt256.ofNat 224 :: UInt256.ofNat n :: R) M aw' rdata σ k' C') :
    ArmAgrees σ σ₀ g A I (Model.stringReturn slot) := by
  cases hd : solidityDecodeBytesLengthHeader (solcSlotWord σ I slot) with
  | ok L =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I σ slot) = .ok L := hd
    have hL := decodedLen_lt hd
    by_cases h32 : 32 + 32 * ((L + 31) / 32) < 2 ^ 64
    swap
    · exact agrees_of_rev hcode (loadString_tooLong hd (by omega) hR rd) (f := .panic 0x41)
        (by simp [Model.stringReturn, World.init, hd',
          show ¬ 64 + 32 * ((L + 31) / 32) < 18446744073709551616 by omega]) (by simp)
    obtain ⟨M, _, _, _, hMs, hM64, hMx, rd⟩ := loadString_ok hd h32 hret hR rd
    obtain ⟨_, _, _, rd⟩ := hjump _ _ _ _ _ rd
    by_cases hfit : 64 + 32 * ((L + 31) / 32) < 2 ^ 64
    swap
    · exact agrees_of_rev hcode (encodeReturn_tooLong (n := 32 + 32 * ((L + 31) / 32))
          (by omega) (by omega) (by omega) rd) (f := .panic 0x41)
        (by simp [Model.stringReturn, World.init, hd',
          show ¬ 64 + 32 * ((L + 31) / 32) < 18446744073709551616 from hfit]) (by simp)
    have rd := encodeReturn (n := 32 + 32 * ((L + 31) / 32)) (by rw [hMs]; omega)
      (by rw [hM64]; congr 1; omega) (by omega) (by omega) hsize (by omega) rd
    rw [show 224 + (32 + 32 * ((L + 31) / 32)) = 256 + 32 * ((L + 31) / 32) by omega, hMx] at rd
    exact agrees_of_ret hcode rd (w' := World.init σ A)
      (by simp [Model.stringReturn, World.init, hd',
        show 64 + 32 * ((L + 31) / 32) < 18446744073709551616 from hfit]) rfl
  | revert =>
    have hd' : solidityDecodeBytesLengthHeader (slotWord I σ slot) = .revert := hd
    exact agrees_of_rev hcode (loadString_revert hd hR rd) (f := .revert (panicData 0x22))
      (by simp [Model.stringReturn, World.init, hd']) (by simp)
  | error =>
    rcases decodeHeader_cases (solcSlotWord σ I slot) with
      ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd

theorem nameArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 0)) :
    ArmAgrees σ σ₀ g A I Model.nameArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 0) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachNameBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.nameArm, exec_nonPayable, hwv]) (by simp)
  rd_run rd to 860 using [hwv]
  have h := stringReturn_refines hcode hsize (by jump_dest) (by simp) rd
    fun _ _ _ _ _ rd => by rd_step rd; exact ⟨_, _, _, rd⟩
  simpa [ArmAgrees, Model.nameArm, exec_nonPayable, hwv] using h

theorem symbolArm_refines {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 7)) :
    ArmAgrees σ σ₀ g A I Model.symbolArm := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 7) rfl hsel
  obtain ⟨aw, k, C, rd⟩ := feWETH9ReachSymbolBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
    exact agrees_of_rev hcode rd (f := .revert ByteArray.empty)
      (by simp [Model.symbolArm, exec_nonPayable, hwv]) (by simp)
  rd_run rd to 860 using [hwv]
  have h := stringReturn_refines hcode hsize (by jump_dest) (by simp) rd
    fun _ _ _ _ _ rd => by rd_step rd; exact ⟨_, _, _, rd⟩
  simpa [ArmAgrees, Model.symbolArm, exec_nonPayable, hwv] using h

/-! ## The runtime entry -/

/-- The bytecode refines the model on every message call. -/
theorem feWETH9RefinesModel : Refines .P0 feWETH9Bytecode Model.contract := by
  refine RefinesOn.of_code rfl ?_
  intro σ σ₀ g A I hcode hsize
  refine RefinesFor.of_gas ?_
  show ArmAgreesFeed σ σ₀ g A I Model.runtime
  have sel : ∀ i, (¬ selIs I (feWETH9SelBytes i)) →
      (feWETH9SelBytes i == I.calldata.extract 0 4) = false := fun i h => by simpa [selIs] using h
  have route : ∀ {arm : FeM ByteArray},
      (∀ feed, Model.runtime.exec I (World.init σ A feed) = arm.exec I (World.init σ A feed)) →
      ArmAgreesFeed σ σ₀ g A I arm → ArmAgreesFeed σ σ₀ g A I Model.runtime := by
    intro arm e h
    simpa only [ArmAgreesFeed, e] using h
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact route (fun _ => by simp [Model.runtime, show I.calldata.size < 4 by omega])
      (fallback_refines hcode hsize (fun h => absurd h hsz)).feed
  have hn4 : ¬ I.calldata.size < 4 := Nat.not_lt.mpr hsz
  by_cases h0 : selIs I (feWETH9SelBytes 0)
  · exact route (fun _ => by simp [Model.runtime, hn4,
      show (Model.nameSelector == I.calldata.extract 0 4) = true from h0])
      (nameArm_refines hcode hsize h0).feed
  have n0 : (Model.nameSelector == I.calldata.extract 0 4) = false := sel 0 h0
  by_cases h1 : selIs I (feWETH9SelBytes 1)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0,
      show (Model.approveSelector == I.calldata.extract 0 4) = true from h1])
      (approveArm_refines hcode hsize h1).feed
  have n1 : (Model.approveSelector == I.calldata.extract 0 4) = false := sel 1 h1
  by_cases h2 : selIs I (feWETH9SelBytes 2)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1,
      show (Model.totalSupplySelector == I.calldata.extract 0 4) = true from h2])
      (totalSupplyArm_refines hcode hsize h2).feed
  have n2 : (Model.totalSupplySelector == I.calldata.extract 0 4) = false := sel 2 h2
  by_cases h3 : selIs I (feWETH9SelBytes 3)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2,
      show (Model.transferFromSelector == I.calldata.extract 0 4) = true from h3])
      (transferFromArm_refines hcode hsize h3).feed
  have n3 : (Model.transferFromSelector == I.calldata.extract 0 4) = false := sel 3 h3
  by_cases h4 : selIs I (feWETH9SelBytes 4)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3,
      show (Model.withdrawSelector == I.calldata.extract 0 4) = true from h4])
      (withdrawArm_refines hcode hsize h4)
  have n4 : (Model.withdrawSelector == I.calldata.extract 0 4) = false := sel 4 h4
  by_cases h5 : selIs I (feWETH9SelBytes 5)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4,
      show (Model.decimalsSelector == I.calldata.extract 0 4) = true from h5])
      (decimalsArm_refines hcode hsize h5).feed
  have n5 : (Model.decimalsSelector == I.calldata.extract 0 4) = false := sel 5 h5
  by_cases h6 : selIs I (feWETH9SelBytes 6)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5,
      show (Model.balanceOfSelector == I.calldata.extract 0 4) = true from h6])
      (balanceOfArm_refines hcode hsize h6).feed
  have n6 : (Model.balanceOfSelector == I.calldata.extract 0 4) = false := sel 6 h6
  by_cases h7 : selIs I (feWETH9SelBytes 7)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5, n6,
      show (Model.symbolSelector == I.calldata.extract 0 4) = true from h7])
      (symbolArm_refines hcode hsize h7).feed
  have n7 : (Model.symbolSelector == I.calldata.extract 0 4) = false := sel 7 h7
  by_cases h8 : selIs I (feWETH9SelBytes 8)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5, n6, n7,
      show (Model.transferSelector == I.calldata.extract 0 4) = true from h8])
      (transferArm_refines hcode hsize h8).feed
  have n8 : (Model.transferSelector == I.calldata.extract 0 4) = false := sel 8 h8
  by_cases h9 : selIs I (feWETH9SelBytes 9)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5, n6, n7, n8,
      show (Model.depositSelector == I.calldata.extract 0 4) = true from h9])
      (depositArm_refines hcode hsize h9).feed
  have n9 : (Model.depositSelector == I.calldata.extract 0 4) = false := sel 9 h9
  by_cases h10 : selIs I (feWETH9SelBytes 10)
  · exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9,
      show (Model.allowanceSelector == I.calldata.extract 0 4) = true from h10])
      (allowanceArm_refines hcode hsize h10).feed
  have n10 : (Model.allowanceSelector == I.calldata.extract 0 4) = false := sel 10 h10
  exact route (fun _ => by simp [Model.runtime, hn4, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10])
    (fallback_refines hcode hsize
      fun _ => feWETH9NoSelectorMatches h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).feed

/-! ## Deployment -/

open Ctor in
/-- Deployment, with no argument bytes and for any initial storage: both write the two strings
    and `decimals`, or both revert on a string head whose length contradicts its flag. -/
theorem feWETH9DeployRefinesModel :
    RefinesDeploy .P0 feWETH9CreationBytecode feWETH9Bytecode Model.contract
      (· = ByteArray.empty) := by
  refine RefinesDeploy.of_unit_closed (init := fun _ => Model.init) (fun _ => rfl) ?_
  rintro σ σ₀ g A I args rfl hcode hperm
  have hcode' : I.code = ctorCode := hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · exact agrees_of_rev (g := Sat256.ofUInt256 g) hcode' (feWETH9CtorRev hcode' hwv)
      (f := .revert ByteArray.empty) (by simp [Model.init, exec_nonPayable, hwv]) (by simp)
  obtain ⟨hbad0, hok0⟩ := feWETH9CtorEvm (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
    hcode' hwv hperm
  by_cases hb0 : strHeadBad (solcSlotWord σ I ⟨0⟩)
  · exact agrees_of_rev hcode' (hbad0 hb0) (f := .revert (panicData 0x22))
      (by simp [Model.init, Model.storeString, World.init, exec_nonPayable, hwv,
        show strHeadBad (slotWord I σ Model.nameSlot) from hb0]) (by simp)
  obtain ⟨hbad1, hok1⟩ := hok0 hb0
  have hn0 : ¬ strHeadBad (slotWord I σ Model.nameSlot) := hb0
  by_cases hb1 : strHeadBad (solcSlotWord (nameMap σ I) I ⟨1⟩)
  · exact agrees_of_rev hcode' (hbad1 hb1) (f := .revert (panicData 0x22))
      (by simp [Model.init, Model.storeString, World.init, exec_nonPayable, hwv, hperm, hn0,
        show strHeadBad (slotWord I (strWriteMap I σ Model.nameSlot Model.nameBytes)
          Model.symbolSlot) from hb1]) (by simp)
  have hn1 : ¬ strHeadBad (slotWord I (strWriteMap I σ Model.nameSlot Model.nameBytes)
    Model.symbolSlot) := hb1
  exact agrees_of_ret hcode' (hok1 hb1) (w' := { World.init σ A with accounts := ctorMap σ I })
    (by simp [Model.init, Model.storeString, World.init, exec_nonPayable, exec_sstore, hwv,
      hperm, hn0, hn1]; rfl) rfl

end FeProofs.WETH9

