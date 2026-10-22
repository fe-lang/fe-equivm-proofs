import FeProofs.WETH9.StringLoad

/-!
# FeWETH9 string getters: the storage precondition and the refinement

`name()` and `symbol()` are `function f() external returns (string) { return f; }` for a string
field.  `stringGetter` proves the refinement for either, from the EVM state at the call of
`SolString::load` (pc 800): Stele reads the field with `solidityReadBytesValue?` (Solidity 0.8),
and the bytecode returns the ABI encoding of the same bytes, or both revert on a header whose
length contradicts its short/long flag.

## The storage precondition

For arbitrary storage a header word can claim a length up to `2^255 - 1` bytes.  Fe reverts with
`Panic(0x41)` when the allocation (`32 + 32 * ceil(len / 32)` bytes, checked by
`ptr::alloc_bytes` before any memory is touched) or the ABI encoding (`64 + 32 * ceil(len / 32)`
bytes, checked by the return encoder) exceeds `2^64 - 1` bytes, while Stele returns the string
whatever its length.  Even the larger case needs only about `2^109` gas of memory expansion, within
the gas the refinement quantifies over, so the refinement is false for a string whose ABI encoding
has `2^64` bytes or more (argued, not proved here).  `feWETH9StorageWF` excludes exactly that
case, and only for the calls that reach the encoder: `name()` and `symbol()` with zero call
value.  It is EquiVM's `weth9StorageWF` (`Benchmarks/WETH9/StringReturnBound.lean`) for Fe's
encoder.  WETH9's constructor stores `"Wrapped Ether"` and `"WETH"`, and no function writes
slots 0 and 1, so a deployed FeWETH9 satisfies it.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9.Strings

set_option maxRecDepth 2000000

end FeProofs.WETH9.Strings

namespace FeProofs.WETH9

open Strings

set_option maxRecDepth 2000000

/-! ## The storage precondition -/

/-- Storage well-formedness for FeWETH9: a zero-value `name()` (slot 0) or `symbol()` (slot 1)
call returns a string whose ABI encoding is shorter than `2^64` bytes.  Every other call is
unconstrained. -/
def feWETH9StorageWF : StorageWF := fun σ I =>
  (selIs I (feWETH9SelBytes 0) → I.weiValue = ⟨0⟩ →
    stringReturnFits (solcSlotWord σ I ⟨0⟩)) ∧
  (selIs I (feWETH9SelBytes 7) → I.weiValue = ⟨0⟩ →
    stringReturnFits (solcSlotWord σ I ⟨1⟩))

/-! ## The getter -/

/-- A `string` getter of the field `field` at `slot`, whose dispatcher arm (zero call value) has
called `SolString::load` (pc 800) with return address `ret`, from where it jumps to the return
encoder (pc 1236, `hjump`). -/
theorem stringGetter {σ σ₀ A I} {g : UInt256} {t : TransitionDecl} {field : Ident}
    {slot ret : UInt256} {R : List UInt256} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some ∅)
    (hbody : t.body = [.require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.storage { base := field, steps := [] }]])
    (hrt : t.returnType = [.string])
    (hty : storageTypeAt? contract.storage { base := field, steps := [] } = some .string)
    (hloc : config.storageBackend.locate? { base := field, steps := [] } = some (.anchor slot))
    (hwv : I.weiValue = ⟨0⟩) (hfits : stringReturnFits (solcSlotWord σ I slot))
    (hret : (D_J feWETH9Bytecode 0).contains ret = true) (hR : R.length ≤ 990)
    (rd : RD feWETH9Bytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 800) (slot :: ret :: R) ByteArray.empty aw rdata σ k C)
    (hjump : ∀ M aw k C n, RD feWETH9Bytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ret
        (UInt256.ofNat 224 :: UInt256.ofNat n :: R) M aw rdata σ k C →
      ∃ aw' k' C', RD feWETH9Bytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 1236)
        (UInt256.ofNat 224 :: UInt256.ofNat n :: R) M aw' rdata σ k' C') :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hwv' : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue = ⟨0⟩ := by
    simp only [initState]; exact hwv
  cases hd : solidityDecodeBytesLengthHeader (solcSlotWord σ I slot) with
  | ok L =>
    have hfit : 64 + 32 * ((L + 31) / 32) < 2 ^ 64 := hfits L hd
    obtain ⟨M, _, _, _, hMs, hM64, hMx, rd⟩ := loadString_ok hd hfit hret hR rd
    obtain ⟨_, _, _, rd⟩ := hjump _ _ _ _ _ rd
    have rd := encodeReturn (n := 32 + 32 * ((L + 31) / 32)) (by rw [hMs]; omega)
      (by rw [hM64]; congr 1; omega) (by omega) (by omega) hsize (by omega) rd
    rw [show 224 + (32 + 32 * ((L + 31) / 32)) = 256 + 32 * ((L + 31) / 32) by omega, hMx] at rd
    have hbody' := nonpayableReturnExprBodyReturns (imms := ∅) (locals := ∅) hwv'
      (stringField_eval_ok (g := Sat256.ofUInt256 g) (σ₀ := σ₀) (A := A) rfl hty hloc hd)
    rw [← hbody] at hbody'
    refine RDret.reEquivExecutionSel hcode rd hsd hdec hbody' ?_
    rw [hrt]
    refine returnEquiv_of_encode ?_
    rw [encodeReturnValue_eq_singleton, encodeString_eq, strBytes_size]
    rfl
  | revert =>
    have hbody' := nonpayableReturnExprBodyReverts (imms := ∅) (locals := ∅) hwv'
      (stringField_eval_revert (g := Sat256.ofUInt256 g) (σ₀ := σ₀) (A := A) rfl hty hloc hd)
    rw [← hbody] at hbody'
    exact RDrev.reEquivExecutionRevertSel hcode (loadString_revert hd hR rd) hsd hdec hbody'
  | error =>
    rcases decodeHeader_cases (solcSlotWord σ I slot) with
      ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h] at hd <;> cases hd

end FeProofs.WETH9
