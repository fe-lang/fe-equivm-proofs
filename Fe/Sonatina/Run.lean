import Fe.Sonatina.CheckCert
import Fe.EVM.Entry

/-!
# Running the machine IR of a contract

Lemmas for running a function of the machine IR on a call by `simp`, block by block: `ir_step`
unfolds `runBlocks` once and simplifies the block it is at, with the interpreter's definitions
and the model library's primitives.  A contract's run lemmas give it the function and the facts
of the call (`calldata_facts` for an arm's head check) and apply it once per block on the path.
-/

namespace Fe.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- `2 ^ 256`, as `simp` leaves it. -/
local notation "size256" =>
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- A word's value modulo `2 ^ 256`, as `simp` meets it once `UInt256.size` is a literal. -/
theorem toNat_mod (u : UInt256) : u.toNat % size256 = u.toNat :=
  Nat.mod_eq_of_lt u.val.isLt

/-- The selector word of calldata, as the IR computes it with `shr`. -/
theorem selWord_toNat (cd : ByteArray) :
    (selWord cd).toNat = (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 := by
  have h := Check.shr_word (x := 224) (y := (uInt256OfByteArray (cd.readBytes 0 32)).toNat)
    (by decide) (UInt256.val _).isLt
  rw [Reasoning.Theory.u256_ofNat_toNat] at h
  rw [selWord, show (⟨224⟩ : UInt256) = UInt256.ofNat 224 from rfl, h, if_neg (by decide)]
  exact Check.toNat_ofNat_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt256.val _).isLt)

/-- The selector word of calldata as the IR computes it, below `2 ^ 256`. -/
theorem sel_mod (cd : ByteArray) : (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 %
    size256 = (uInt256OfByteArray (cd.readBytes 0 32)).toNat >>> 224 :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt256.val _).isLt)

/-- The facts of a calldata size `n` that holds a selector, as `simp` meets them in an arm's
    head check `n - 4 <s k`. -/
theorem calldata_facts {n : Nat} (hsz : 4 ≤ n) (hfits : n < 2 ^ 64) :
    n % size256 = n ∧ (n : Int) % size256 = n ∧ wrap 256 ((n : Int) - 4) = n - 4 ∧
      (n - 4) % size256 = n - 4 ∧ signed 256 (n - 4) = (n : Int) - 4 ∧ ¬ n < 4 := by
  refine ⟨by omega, by omega, by simp only [wrap]; omega, by omega, ?_, by omega⟩
  simp only [signed]
  split <;> omega

/-- A value below `2 ^ (bits - 1)` is itself as a signed integer. -/
@[simp] theorem signed_of_lt {bits v : Nat} (h : v < 2 ^ (bits - 1)) : signed bits v = v := by
  simp [signed, h]

/-- A copy of `len` bytes from offset `so` of `src` is a copy of that window from its start: the
    shape `codecopy` and `calldatacopy` leave in memory, for the read-back lemmas of writes from
    offset 0. -/
theorem write_window (src base : ByteArray) (so d len : ℕ) (hlen : len ≠ 0)
    (hsrc : so + len ≤ src.size) :
    src.write so base d len = (src.extract so (so + len)).write 0 base d len := by
  have hs : (src.extract so (so + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg hlen, if_neg (by omega), if_neg (by omega), hs]
  have hz : (ByteArray.zeroes (min base.size (d + len) - (d + len))).data = #[] := by
    rw [show min base.size (d + len) - (d + len) = 0 by omega,
      Reasoning.Theory.zeroes_zero (n := 0) (by rfl)]; rfl
  have hd : src.data.size = src.size := rfl
  simp only [ByteArray.data_copySlice, ByteArray.data_append,
    show min len (src.size - so) = len by omega, show min len (len - 0) = len by omega, hz,
    Array.append_empty, hd, Nat.zero_add]
  rw [show min base.size (d + len) - (d + len) = 0 by omega, Nat.add_zero,
    show (src.extract so (so + len)).data.size - 0 = len from hs, Nat.min_self,
    show min len (src.size - so) = len by omega, ByteArray.data_extract, Array.extract_extract]
  simp

/-- Unfold `runBlocks` once and simplify the block the run is at, with the interpreter's
    definitions, the model library's primitives, the local hypotheses and the extra lemmas. -/
syntax "ir_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_step) => `(tactic| ir_step [])
  | `(tactic| ir_step [$ls,*]) => `(tactic| (rw [runBlocks.eq_1]; simp [Func.block?, enter,
      Fe.Sonatina.bind, runBody.eq_2, runBody.eq_1, runInst, EvmOp.run, evalPair, evalInt,
      evalOperand, evalWord, Fe.Sonatina.word, Val.as, Ty.bits, CmpOp.eval, BinOp.eval,
      Sonatina.bool, Check.toNat_ofNat, UInt256.size, Fe.EVM.calldatasize, Fe.EVM.calldataload,
      Fe.EVM.callvalue, Fe.EVM.codesize, Fe.EVM.codecopy, Fe.EVM.sload, Fe.EVM.sstore,
      Fe.EVM.mstore, Fe.EVM.mload, revertData, returnData,
      Reasoning.Theory.byteArray_readWithPadding_zero, toNat_mod, sel_mod,
      Reasoning.Theory.u256_ofNat_toNat, show UInt256.ofNat 0 = ⟨0⟩ from rfl,
      Std.TreeMap.getElem_insert, *, $ls,*]))

end Fe.Sonatina
