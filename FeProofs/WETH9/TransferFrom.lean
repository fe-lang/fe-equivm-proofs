import FeProofs.WETH9.Dispatch
import FeProofs.WETH9.TransferFromBody

/-!
# FeWETH9 `transferFrom(address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 284; reach lemma `feWETH9ReachTransferFromBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- From the shared tail (pc 1450) with write permission: the debit, the credit, `LOG3`, and the
jump back to the arm with `true`. -/
theorem tfTail {σ σ₀ A I} {g : Sat256} {σ1 : AccountMap} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {sw dw w ret : UInt256} (hperm : I.perm = true)
    (hret : (D_J feWETH9Bytecode 0).contains ret = true)
    (rd : RD feWETH9Bytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 1450) [sw, dw, w, ret] mem aw
      ByteArray.empty σ1 k C) :
    ∃ mem' aw' k' C', RD feWETH9Bytecode I g (initState σ σ₀ g A I) ret [UInt256.ofNat 1] mem' aw'
      ByteArray.empty (tfMoveMap σ1 I sw dw w) k' C' := by
  obtain ⟨k', C', rd'⟩ := feWETH9Blocks.feWETH9_block_1450 (by simp) hperm hret rd
  simp (disch := (first | rfl | decide | omega)) only [keccakWord_mapSlotAtWord] at rd'
  rw [u256_add_comm w] at rd'
  exact ⟨_, _, _, _, rd'⟩

/-- From the shared tail in static mode: the debit's `SSTORE` halts. -/
theorem tfTailStatic {σ σ₀ A I} {g : Sat256} {σ1 : AccountMap} {mem : ByteArray} {aw : UInt256}
    {k C : ℕ} {sw dw w ret : UInt256} (hpf : I.perm = false)
    (rd : RD feWETH9Bytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 1450) [sw, dw, w, ret] mem aw
      ByteArray.empty σ1 k C) :
    RDstatic feWETH9Bytecode g (initState σ σ₀ g A I) := by
  rd_run rd
  exact rd

/-- The argument store `transferFrom(address,address,uint256)` decodes. -/
abbrev transferFromLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "src" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
    "dst" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert
    "wad" (.int (Int.ofNat (calldataWord I.calldata 68).toNat))

/-- `transferFrom(address,address,uint256)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem feWETH9TransferFromBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 3) rfl hsel
  have hd := feWETH9Dispatch_transferFrom hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachTransferFromBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 100 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 100 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 3 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (hbad.elim
      (decodeCalldata_address_address_uint256_none_short hsz)
      decodeCalldata_address_address_uint256_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcCalldataStaticLenCheckOk (words := 3) hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (decodeCalldata_address_address_uint256_none_noncanon0 hlen hhi hc0)
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (decodeCalldata_address_address_uint256_none_noncanon1 hlen hhi hc0 hc1)
  have hdec : config.externalABI.decodeCalldata? (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromLocals I) :=
    decodeCalldata_address_address_uint256_ok hlen hhi hc0 hc1
  rd_run rd to 1305 using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  have hsrcL : (transferFromLocals I).get? "src" =
      some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) := by store_get
  have hdstL : (transferFromLocals I).get? "dst" =
      some (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) := by store_get
  have hwadL : (transferFromLocals I).get? "wad" =
      some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)) := by store_get
  have hbo : (transferFromLocals I).get? "balanceOf" = none := by store_get
  have hal : (transferFromLocals I).get? "allowance" = none := by store_get
  have hB : loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (balSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) =
      solcSlotWord σ I (mapSlot (calldataWord I.calldata 4) ⟨3⟩) := by
    rw [loadAt_initState, balSlot, addrWord_ofNat hc0]
  by_cases hbal : (calldataWord I.calldata 68).toNat ≤
      (solcSlotWord σ I (mapSlot (calldataWord I.calldata 4) ⟨3⟩)).toNat
  swap
  · have hlt := Nat.lt_of_not_le hbal
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevertSel hcode rd hd hdec
      (tfBody_balance (hcv := hwv) (hbo := hbo) (hsrc := hsrcL) (hwad := hwadL) (by rw [hB]; exact hlt))
  rd_run rd to 1328 using [slot_hint (ult_zero hbal)]
  have hbalS : (calldataWord I.calldata 68).toNat ≤ (loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (balSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toNat := by
    rw [hB]; exact hbal
  have hacc (e : EVM.State) (he : e.executionEnv = I) :
      tfMoveMap e.accountMap I (calldataWord I.calldata 4) (calldataWord I.calldata 36)
        (calldataWord I.calldata 68) =
      (tfMove e (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (AccountAddress.ofNat (calldataWord I.calldata 36).toNat) (calldataWord I.calldata 68)).accountMap := by
    rw [tfMove_accountMap he, addrWord_ofNat hc0, addrWord_ofNat hc1]
  by_cases hself : calldataWord I.calldata 4 = addrWord I.source
  · -- `src` is the caller: no allowance
    have hs : AccountAddress.ofNat (calldataWord I.calldata 4).toNat = I.source :=
      (ofNat_eq_iff hc0).mpr hself
    rd_run rd to 1450 using [(show UInt256.eq (calldataWord I.calldata 4) (addrWord I.source) = ⟨1⟩ by
      rw [hself]; exact u256_eq_refl _)]
    by_cases hperm : I.perm = true
    swap
    · have hpf : I.perm = false := by simpa using hperm
      exact RDstatic.reEquivStaticHaltSel hcode (tfTailStatic hpf rd) hd hdec
        (tfBody_skipStatic (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hwad := hwadL)
          (hbal := hbalS) (Or.inl hs) hpf)
    obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
    rd_run rd
    u256_lits at rd
    rw [toByteArray_write_read_back_of_gap _ mem' 224 (small_gap mem' 224 (by decide))] at rd
    exact RDret.reEquivExecutionGenSel hcode rd hd hdec
      (tfBody_skipReturns (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hdst := hdstL)
        (hwad := hwadL) (hbal := hbalS) (Or.inl hs) hperm)
      (hacc (initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl)
      (returnEquiv_of_encode boolTrueReturnEncoding)
  -- `src` is not the caller
  have hne : AccountAddress.ofNat (calldataWord I.calldata 4).toNat ≠ I.source :=
    fun h => hself ((ofNat_eq_iff hc0).mp h)
  have hA : loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (allowSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.source) =
      solcSlotWord σ I (mapSlot (addrWord I.source) (mapSlot (calldataWord I.calldata 4) ⟨4⟩)) := by
    rw [loadAt_initState]
    show solcSlotWord σ I (allowSlot _ I.source) = _
    rw [allowSlot, addrWord_ofNat hc0]
  rd_run rd to 1337 using [u256_eq_of_ne hself]
  by_cases hmaxw : solcSlotWord σ I (mapSlot (addrWord I.source) (mapSlot (calldataWord I.calldata 4) ⟨4⟩)) =
      UInt256.lnot ⟨0⟩
  · -- the maximum allowance is not spent
    have hmax : (loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (allowSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.source)).toNat =
        2 ^ 256 - 1 := by rw [hA, hmaxw]; rfl
    rd_run rd to 1450 using [slot_hint (ne_of_eq_of_ne (show UInt256.eq (UInt256.lnot ⟨0⟩)
      (solcSlotWord σ I (mapSlot (addrWord I.source) (mapSlot (calldataWord I.calldata 4) ⟨4⟩))) = ⟨1⟩ by
        rw [hmaxw]; exact u256_eq_refl _) (by decide))]
    by_cases hperm : I.perm = true
    swap
    · have hpf : I.perm = false := by simpa using hperm
      exact RDstatic.reEquivStaticHaltSel hcode (tfTailStatic hpf rd) hd hdec
        (tfBody_skipStatic (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hwad := hwadL)
          (hbal := hbalS) (Or.inr hmax) hpf)
    obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
    rd_run rd
    u256_lits at rd
    rw [toByteArray_write_read_back_of_gap _ mem' 224 (small_gap mem' 224 (by decide))] at rd
    exact RDret.reEquivExecutionGenSel hcode rd hd hdec
      (tfBody_skipReturns (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hdst := hdstL)
        (hwad := hwadL) (hbal := hbalS) (Or.inr hmax) hperm)
      (hacc (initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl)
      (returnEquiv_of_encode boolTrueReturnEncoding)
  have hmax : (loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (allowSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.source)).toNat ≠
      2 ^ 256 - 1 := by
    rw [hA]; intro h; exact hmaxw (u256_inj (by rw [h]; rfl))
  rd_run rd to 1371 using [slot_hint (u256_eq_of_ne (Ne.symm hmaxw))]
  by_cases hallow : (calldataWord I.calldata 68).toNat ≤
      (solcSlotWord σ I (mapSlot (addrWord I.source) (mapSlot (calldataWord I.calldata 4) ⟨4⟩))).toNat
  swap
  · -- short allowance
    have hlt := Nat.lt_of_not_le hallow
    rd_run rd using [slot_hint (ne_of_eq_of_ne (ult_one hlt) (by decide))]
    exact RDrev.reEquivExecutionRevertSel hcode rd hd hdec
      (tfBody_allowance (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hwad := hwadL)
        (hbal := hbalS) hne hmax (by rw [hA]; exact hlt))
  have hallowS : (calldataWord I.calldata 68).toNat ≤ (loadAt (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (allowSlot (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.source)).toNat := by
    rw [hA]; exact hallow
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the allowance `SSTORE` halts
    have hpf : I.perm = false := by simpa using hperm
    rd_run rd using [slot_hint (ult_zero hallow)]
    exact RDstatic.reEquivStaticHaltSel hcode rd hd hdec
      (tfBody_spendStatic (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hwad := hwadL)
        (hbal := hbalS) hne hmax hallowS hpf)
  rd_run rd to 1450 using [slot_hint (ult_zero hallow)]
  simp (disch := (first | rfl | decide | omega)) only [keccakWord_mapSlotAtWord] at rd
  obtain ⟨mem', aw', k', C', rd⟩ := tfTail hperm (by native_decide) rd
  rd_run rd
  u256_lits at rd
  rw [toByteArray_write_read_back_of_gap _ mem' 224 (small_gap mem' 224 (by decide))] at rd
  refine RDret.reEquivExecutionGenSel hcode rd hd hdec
    (tfBody_spendReturns (hcv := hwv) (hbo := hbo) (hal := hal) (hsrc := hsrcL) (hdst := hdstL)
      (hwad := hwadL) (hbal := hbalS) hne hmax hallowS hperm) ?_
    (returnEquiv_of_encode boolTrueReturnEncoding)
  rw [← hacc _ (tfSpend_executionEnv _ _ _), tfSpend_accountMap rfl, allowSlot,
    addrWord_ofNat hc0]
  rfl


end FeProofs.WETH9
