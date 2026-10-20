import FeProofs.Deposit.Dispatch
import FeProofs.Common.Basic
import Reasoning.ABIViews
import Reasoning.WordArithmetic
import Reasoning.EVMWord

/-!
# FeDeposit `supportsInterface(bytes4)`

Arm entry pc 60: the call-value check, the head check at pc 67, Fe's canonical-`bytes4` check
`SHL(32, word) == 0` at pc 80, then `SHR(224, word)` compared with `0x01ffc9a7` (pc 91) and
`0x85640907` (pc 104); the boolean is stored at `0x100` and returned (pc 147).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- The argument word. -/
abbrev siWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

/-- The argument's 32 calldata bytes. -/
abbrev siArgBytes (I : ExecutionEnv) : List UInt8 := (I.calldata.toList.drop 4).take 32

/-- The decoded `bytes4`. -/
abbrev siBytes (I : ExecutionEnv) : List UInt8 := (siArgBytes I).take 4

abbrev siStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "interface_id" (.fixedBytes abiBytes4Width (siBytes I))

abbrev siResult (I : ExecutionEnv) : Bool :=
  (siBytes I == [0x01, 0xff, 0xc9, 0xa7]) || (siBytes I == [0x85, 0x64, 0x09, 0x07])

theorem siArgBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (siArgBytes I).length = 32 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [List.length_take, List.length_drop, htlen]
  omega

theorem siBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (siBytes I).length = 4 := by
  rw [List.length_take, siArgBytes_length hsz36]; rfl

-- GENERALIZES OpenZeppelinBench.AccessControl.supportsInterfaceWord_toNat — lift to
-- `Reasoning/ABIViews.lean` as the value of any calldata argument word.
theorem siWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (siWord I).toNat = fromBytesBigEndian (siArgBytes I) := by
  have hword : ABI.bytesToWord (siArgBytes I) = siWord I := by
    simpa [siWord, calldataWord] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [← hword]
  exact bytesToWord_toNat_of_len _ (siArgBytes_length hsz36)

theorem siWord_split {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (siWord I).toNat = fromBytesBigEndian (siBytes I) * 2 ^ 224 +
      fromBytesBigEndian ((siArgBytes I).drop 4) := by
  have htail : ((siArgBytes I).drop 4).length = 28 := by
    rw [List.length_drop, siArgBytes_length hsz36]
  rw [siWord_toNat hsz36]
  calc fromBytesBigEndian (siArgBytes I)
      = fromBytesBigEndian ((siArgBytes I).take 4 ++ (siArgBytes I).drop 4) := by
        rw [List.take_append_drop]
    _ = _ := by rw [fromBytesBigEndian_append, htail, show 8 * 28 = 224 by norm_num]

theorem siTail_lt {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fromBytesBigEndian ((siArgBytes I).drop 4) < 2 ^ 224 := by
  have hb := fromBytesBigEndian_bound ((siArgBytes I).drop 4)
  rw [List.length_drop, siArgBytes_length hsz36] at hb
  simpa using hb

/-- `SHR(224, word)` is the decoded `bytes4` read as a big-endian number. -/
theorem siHigh_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (UInt256.shiftRight (siWord I) (UInt256.ofNat 224)).toNat = fromBytesBigEndian (siBytes I) := by
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ (UInt256.ofNat 224).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val, show (UInt256.ofNat 224).val.val = 224 by decide, Nat.shiftRight_eq_div_pow]
  have h := siWord_split hsz36
  have ht := siTail_lt hsz36
  change (siWord I).toNat / 2 ^ 224 = _
  rw [h]
  omega

/-- `SHL(32, word)` is the word's low 224 bits, shifted to the top. -/
theorem siLow_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (UInt256.shiftLeft (siWord I) (UInt256.ofNat 32)).toNat =
      fromBytesBigEndian ((siArgBytes I).drop 4) * 2 ^ 32 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (UInt256.ofNat 32).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val, show (UInt256.ofNat 32).val.val = 32 by decide, Nat.shiftLeft_eq]
  change (siWord I).toNat * 2 ^ 32 % UInt256.size = _
  have h := siWord_split hsz36
  have ht := siTail_lt hsz36
  have hB : fromBytesBigEndian ((siArgBytes I).drop 4) * 2 ^ 32 < UInt256.size := by
    have h2 : fromBytesBigEndian ((siArgBytes I).drop 4) * 2 ^ 32 < 2 ^ 224 * 2 ^ 32 :=
      Nat.mul_lt_mul_of_pos_right ht (by positivity)
    simpa [UInt256.size, ← Nat.pow_add] using h2
  have e : (siWord I).toNat * 2 ^ 32 = fromBytesBigEndian (siBytes I) * UInt256.size +
      fromBytesBigEndian ((siArgBytes I).drop 4) * 2 ^ 32 := by
    rw [h]; simp only [UInt256.size]; ring
  rw [e, Nat.mul_comm _ UInt256.size, Nat.mul_add_mod, Nat.mod_eq_of_lt hB]

theorem siTail_zero_of_pad {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? (siArgBytes I) 4 28 = some ()) :
    fromBytesBigEndian ((siArgBytes I).drop 4) = 0 := by
  have htailLen : ((siArgBytes I).drop 4).length = 28 := by
    rw [List.length_drop, siArgBytes_length hsz36]
  have htailTake : ((siArgBytes I).drop 4).take 28 = (siArgBytes I).drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  apply (fromBytesBigEndian_zero_iff_all_zero _).mpr
  unfold zeroPadding? readBytes? at hpad
  rw [if_pos (by rw [htailTake, htailLen]), htailTake] at hpad
  by_cases hall : ((siArgBytes I).drop 4).all (· == 0) = true
  · exact hall
  · simp at hpad
    simpa using hpad

theorem siTail_ne_zero_of_pad {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? (siArgBytes I) 4 28 = none) :
    fromBytesBigEndian ((siArgBytes I).drop 4) ≠ 0 := by
  have htailLen : ((siArgBytes I).drop 4).length = 28 := by
    rw [List.length_drop, siArgBytes_length hsz36]
  have htailTake : ((siArgBytes I).drop 4).take 28 = (siArgBytes I).drop 4 :=
    List.take_of_length_le (by rw [htailLen])
  intro hz
  have hall := (fromBytesBigEndian_zero_iff_all_zero _).mp hz
  unfold zeroPadding? readBytes? at hpad
  rw [if_pos (by rw [htailTake, htailLen]), htailTake] at hpad
  simp at hpad
  rcases hpad with ⟨x, hxmem, hxne⟩
  have hallProp : ∀ x ∈ (siArgBytes I).drop 4, x = 0 := by simpa using hall
  exact hxne (hallProp x hxmem)

theorem siPad_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? (siArgBytes I) 4 28 = some ()) :
    UInt256.shiftLeft (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))
      (UInt256.ofNat 32) = UInt256.ofNat 0 := by
  apply u256_inj
  change (UInt256.shiftLeft (siWord I) (UInt256.ofNat 32)).toNat = 0
  rw [siLow_toNat hsz36, siTail_zero_of_pad hsz36 hpad]
  rfl

theorem siPad_bad {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? (siArgBytes I) 4 28 = none) :
    UInt256.shiftLeft (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))
      (UInt256.ofNat 32) ≠ UInt256.ofNat 0 := by
  intro h
  have h' := congrArg UInt256.toNat h
  change (UInt256.shiftLeft (siWord I) (UInt256.ofNat 32)).toNat = (UInt256.ofNat 0).toNat at h'
  rw [siLow_toNat hsz36, show (UInt256.ofNat 0).toNat = 0 from rfl] at h'
  exact siTail_ne_zero_of_pad hsz36 hpad (by simpa using h')

/-- `SHR(224, word) == sel` is the `bytes4` comparison. -/
theorem siSel_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) (bs : List UInt8)
    (hbs : bs.length = 4) (sel : ℕ) (hsel : fromBytesBigEndian bs = sel) (hsel256 : sel < UInt256.size) :
    (UInt256.eq (UInt256.shiftRight (siWord I) (UInt256.ofNat 224)) (UInt256.ofNat sel) ≠ ⟨0⟩) ↔
      siBytes I = bs := by
  have hsv := siHigh_toNat hsz36
  constructor
  · intro hne
    have heq : UInt256.shiftRight (siWord I) (UInt256.ofNat 224) = UInt256.ofNat sel := by
      by_contra hc
      exact hne (u256_eq_of_ne hc)
    have hn : fromBytesBigEndian (siBytes I) = fromBytesBigEndian bs := by
      rw [← hsv, heq, hsel, ulit_toNat' sel hsel256]
    exact fromBytesBigEndian_inj4 (siBytes_length hsz36) hbs hn
  · intro hb
    have heq : UInt256.shiftRight (siWord I) (UInt256.ofNat 224) = UInt256.ofNat sel :=
      u256_inj (by rw [hsv, hb, hsel, ulit_toNat' sel hsel256])
    rw [heq, uInt256_eq_self]
    decide

theorem siDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hpad : zeroPadding? (siArgBytes I) 4 28 = some ()) :
    config.externalABI.decodeCalldata? (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = some (siStore I) := by
  show decodeCalldata ["interface_id"] [abiBytes4] I.calldata = _
  exact decodeCalldata_bytes4_ok hsz36 hhi hpad

theorem siDecode_none {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (h : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size ∨
      (36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
        zeroPadding? (siArgBytes I) 4 28 = none)) :
    config.externalABI.decodeCalldata? (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interface_id"] [abiBytes4] I.calldata = _
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact decodeCalldata_bytes4_none_short hsz4 h
  · exact decodeCalldata_bytes4_none_huge h
  · exact decodeCalldata_bytes4_none_pad h1 h2 h3

theorem siFixedBytes4_beq (xs ys : List UInt8) :
    (Value.fixedBytes abiBytes4Width xs == Value.fixedBytes 3 ys) = (xs == ys) := by
  show (Value.fixedBytes abiBytes4Width xs == Value.fixedBytes abiBytes4Width ys) = _
  simp [BEq.beq, listUInt8_decide_eq_beq]

theorem siBodyReturns (evm : EVM.State) (I : ExecutionEnv) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (siStore I) supportsInterfaceTransition.body
      (.returned { contract := contract, locals := siStore I } evm (some [.bool (siResult I)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns ?_
  by_cases h1 : siBytes I == [0x01, 0xff, 0xc9, 0xa7]
  · simp [siStore, siResult, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      evalBinaryOp?, siFixedBytes4_beq, h1]
  · simp [siStore, siResult, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      evalBinaryOp?, siFixedBytes4_beq, h1]

theorem siReturn (b : Bool) (w : UInt256) (hw : w = if b then ⟨1⟩ else ⟨0⟩) :
    returnEquiv (UInt256.toByteArray w) (some [.bool b]) [.elem .bool] := by
  subst hw
  cases b
  · exact returnEquiv_of_encode boolFalseReturnEncoding
  · exact returnEquiv_of_encode boolTrueReturnEncoding

theorem siOut (w : UInt256) :
    ((w.toByteArray.write 0 ByteArray.empty (UInt256.ofNat 256).toNat 32).readWithPadding
      (UInt256.ofNat 256).toNat (UInt256.ofNat 32).toNat) = w.toByteArray :=
  toByteArray_write_read_back_of_gap w ByteArray.empty 256
    (by simp only [ByteArray.size_empty]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size)

/-- `supportsInterface(bytes4)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem feDepositSupportsInterfaceBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feDepositSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feDepositSelBytes 0) rfl hsel
  have hd := feDepositDispatch_supportsInterface hsel
  obtain ⟨k, C, rd⟩ := feDepositReachSupportsInterfaceBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := feDepositBlocks.feDeposit_block_60_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) hwv rd
    simp only [feDepositBlocks.feDeposit_block_60_fallthrough_stack] at rd1
    by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨hlen, hhi⟩ := hok
      have rd2 := feDepositBlocks.feDeposit_block_67_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack])
        (solcDecodeLenCheckOk_4_32 hlen hhi hsize) rd1
      cases hpad : zeroPadding? (siArgBytes I) 4 28 with
      | none =>
          have rd3 := feDepositBlocks.feDeposit_block_80_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (siPad_bad hlen hpad)
            (by jump_dest) rd2
          exact RDrev.reEquivDecodingFailed hcode (feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd3)
            hd (siDecode_none hsz (Or.inr (Or.inr ⟨hlen, hhi, hpad⟩)))
      | some u =>
          cases u
          have rd3 := feDepositBlocks.feDeposit_block_80_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (siPad_ok hlen hpad) rd2
          simp only [feDepositBlocks.feDeposit_block_80_fallthrough_stack] at rd3
          have hbody := siBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv)
          have hdec := siDecode_ok hlen hhi hpad
          by_cases h1 : siBytes I = [0x01, 0xff, 0xc9, 0xa7]
          · have rd4 := feDepositBlocks.feDeposit_block_91_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack])
              ((siSel_eq hlen _ rfl 33540519 (by decide) (by decide)).mpr h1) (by jump_dest) rd3
            have rd5 := feDepositBlocks.feDeposit_block_123 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd4
            have rd6 := feDepositBlocks.feDeposit_block_127_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by decide) rd5
            have rd7 := feDepositBlocks.feDeposit_block_132 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by jump_dest) rd6
            have rret := feDepositBlocks.feDeposit_block_147 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd7
            simp only [feDepositBlocks.feDeposit_block_132_memory] at rret
            rw [siOut] at rret
            exact rret.reEquivExecution hcode hd hdec hbody
              (siReturn _ _ (by simp [siResult, h1]; rfl))
          · have rd4 := feDepositBlocks.feDeposit_block_91_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack])
              (by
                by_contra hne
                exact h1 ((siSel_eq hlen _ rfl 33540519 (by decide) (by decide)).mp hne)) rd3
            by_cases h2 : siBytes I = [0x85, 0x64, 0x09, 0x07]
            · have rd5 := feDepositBlocks.feDeposit_block_104_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack])
                (by rw [uInt256_eq_comm]
                    exact (siSel_eq hlen _ rfl 2237925639 (by decide) (by decide)).mpr h2)
                (by jump_dest) rd4
              have rd6 := feDepositBlocks.feDeposit_block_117 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by jump_dest) rd5
              have rd7 := feDepositBlocks.feDeposit_block_127_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by decide) rd6
              have rd8 := feDepositBlocks.feDeposit_block_132 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by jump_dest) rd7
              have rret := feDepositBlocks.feDeposit_block_147 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd8
              simp only [feDepositBlocks.feDeposit_block_132_memory] at rret
              rw [siOut] at rret
              exact rret.reEquivExecution hcode hd hdec hbody
                (siReturn _ _ (by simp [siResult, h2]; rfl))
            · have rd5 := feDepositBlocks.feDeposit_block_104_fallthrough (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack])
                (by
                  rw [uInt256_eq_comm]
                  by_contra hne
                  exact h2 ((siSel_eq hlen _ rfl 2237925639 (by decide) (by decide)).mp hne)) rd4
              have rd6 := feDepositBlocks.feDeposit_block_113 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by jump_dest) rd5
              have rd7 := feDepositBlocks.feDeposit_block_127_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by decide)
                (by jump_dest) rd6
              have rd8 := feDepositBlocks.feDeposit_block_141 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd7
              have rret := feDepositBlocks.feDeposit_block_147 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd8
              simp only [feDepositBlocks.feDeposit_block_141_memory] at rret
              rw [siOut] at rret
              exact rret.reEquivExecution hcode hd hdec hbody
                (siReturn _ _ (by simp [siResult, h1, h2]))
    · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = ⟨1⟩ := by
        rcases hbad with h | h
        · exact solcDecodeLenCheckShort_4_32 hsz h hsize
        · exact solcDecodeLenCheckHuge_4_32 h hsize
      have rd2 := feDepositBlocks.feDeposit_block_67_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) (by rw [hslt]; decide)
        (by jump_dest) rd1
      exact RDrev.reEquivDecodingFailed hcode (feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd2)
        hd (siDecode_none hsz (by rcases hbad with h | h; exact Or.inl h; exact Or.inr (Or.inl h)))
  · have rd1 := feDepositBlocks.feDeposit_block_60_taken (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) hwv (by jump_dest) rd
    simp only [feDepositBlocks.feDeposit_block_60_taken_stack] at rd1
    exact RDrev.reEquivDispatchedRevert hcode (feDepositBlocks.feDeposit_block_2245 (by simp [feDepositBlocks.feDeposit_block_60_taken_stack, feDepositBlocks.feDeposit_block_60_fallthrough_stack, feDepositBlocks.feDeposit_block_80_taken_stack, feDepositBlocks.feDeposit_block_80_fallthrough_stack, feDepositBlocks.feDeposit_block_91_taken_stack, feDepositBlocks.feDeposit_block_91_fallthrough_stack, feDepositBlocks.feDeposit_block_104_taken_stack, feDepositBlocks.feDeposit_block_104_fallthrough_stack, feDepositBlocks.feDeposit_block_113_stack, feDepositBlocks.feDeposit_block_117_stack, feDepositBlocks.feDeposit_block_123_stack, feDepositBlocks.feDeposit_block_127_taken_stack, feDepositBlocks.feDeposit_block_127_fallthrough_stack]) rd1)
      hd fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end FeProofs.Deposit
