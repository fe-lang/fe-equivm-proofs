import FeProofs.CodeScalar.RuntimeBlocks_001
import FeProofs.CodeScalar.Selectors
import Reasoning.ABI
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.WordArithmetic
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.VyperCalls
import FeProofs.Common.Abi
import FeProofs.Common.Memory
import FeProofs.Common.Tactics
import FeProofs.Common.Basic

/-!
# FeCodeScalar runtime traces

The deployed code is the runtime bytecode followed by one word, the immutable field `value`.
Each trace is stated for the bytecode with data after it.  `get()` rejects call value, copies
the last 32 bytes of the running code to memory, and returns them.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls

namespace FeProofs.CodeScalar

set_option maxRecDepth 2000000

theorem feCodeScalarBytecode_size : feCodeScalarBytecode.size = 55 := by native_decide

theorem getEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨1833756220⟩ (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (feCodeScalarSelBytes 0 == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x6d 0x4c 0xe6 0x3c ⟨1833756220⟩ (by decide)

/-- The dispatcher reaches the `get()` arm at pc 26. -/
theorem feCodeScalarReachGet {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = feCodeScalarBytecode ++ tail) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feCodeScalarSelBytes 0)) :
    ∃ k C, RD (feCodeScalarBytecode ++ tail) I g (initState σ σ₀ g A I) (UInt256.ofNat 26)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty σ k C := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feCodeScalarSelBytes 0) rfl hsel
  have hword : solcSelectorWord I = ⟨1833756220⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x6d 0x4c 0xe6 0x3c ⟨1833756220⟩ (by native_decide)
      (by simpa [feCodeScalarSelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 to 26 using [lt_four_eq_zero_of_ge hsz hsize, selWord_eq hword]
  exact ⟨_, _, rd0⟩

/-- Memory after `CODECOPY(0, CODESIZE - 32, 32)`. -/
abbrev getMem (w : UInt256) : ByteArray :=
  (feCodeScalarBytecode ++ w.toByteArray).write
    ((UInt256.ofNat 31).lnot + UInt256.ofNat (feCodeScalarBytecode ++ w.toByteArray).size).toNat
    ByteArray.empty (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat

theorem code_size (w : UInt256) : (feCodeScalarBytecode ++ w.toByteArray).size = 87 := by
  rw [ByteArray.size_append, feCodeScalarBytecode_size, toByteArray_size]

/-- The copy is the word after the bytecode. -/
theorem getMem_eq (w : UInt256) :
    getMem w = ByteArray.empty ++ ByteArray.zeroes 0 ++ w.toByteArray := by
  unfold getMem
  rw [code_size, show ((UInt256.ofNat 31).lnot + UInt256.ofNat 87).toNat = 55 by decide,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    write_from_gap_eq (feCodeScalarBytecode ++ w.toByteArray) ByteArray.empty 55 0 32 (by decide)
      (by have := code_size w; omega) (Nat.le_refl 0)
      (Nat.lt_of_lt_of_le (by decide) USize.le_size),
    extract_append_right' _ _ 55 (55 + 32) feCodeScalarBytecode_size.symm
      (by rw [feCodeScalarBytecode_size, toByteArray_size])]
  rfl

theorem getMem_load (w : UInt256) : memLoad (⟨0⟩ : UInt256) (getMem w) = w := by
  have hpre : (ByteArray.empty ++ ByteArray.zeroes 0).size = 0 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]; rfl
  have hsz : (getMem w).size = 32 := by
    rw [getMem_eq, ByteArray.size_append, hpre, toByteArray_size]
  refine memLoad_of_read _ 0 w (by decide) (by omega) ?_
  rw [readWithPadding_eq_extract _ 0 (by omega), getMem_eq,
    extract_append_right' _ _ 0 (0 + 32) hpre.symm (by rw [hpre, toByteArray_size])]

/-- `get()` returns the word after the bytecode. -/
theorem feCodeScalarGetRet {σ σ₀ A I} {g : Sat256} (w : UInt256)
    (hcode : I.code = feCodeScalarBytecode ++ w.toByteArray)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feCodeScalarSelBytes 0)) (hwv : I.weiValue = ⟨0⟩) :
    RDret (feCodeScalarBytecode ++ w.toByteArray) g (initState σ σ₀ g A I) σ w.toByteArray := by
  obtain ⟨k, C, rd⟩ := feCodeScalarReachGet (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode hsize hsel
  rd_run rd using [hwv]
  rw [getMem_load] at rd
  u256_lits at rd
  rwa [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd

theorem feCodeScalarGetRev {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = feCodeScalarBytecode ++ tail) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feCodeScalarSelBytes 0)) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (feCodeScalarBytecode ++ tail) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := feCodeScalarReachGet (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode hsize hsel
  rd_run rd using [hwv, isZero_eq_zero_of_ne hwv]
  exact rd

/-- Calldata shorter than a selector. -/
theorem feCodeScalarX_short {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = feCodeScalarBytecode ++ tail) (hshort : I.calldata.size < 4) :
    RDrev (feCodeScalarBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  rd_run rd0 using [lt_four_ne_zero_of_lt hshort]
  exact rd0

/-- The selector is not `get()`. -/
theorem feCodeScalarX_noMatch {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = feCodeScalarBytecode ++ tail)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ¬ selIs I (feCodeScalarSelBytes 0)) :
    RDrev (feCodeScalarBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have hne : UInt256.eq (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)
      ⟨1833756220⟩ = ⟨0⟩ := by
    have e := getEvmSelector hsz
    simp only [show (feCodeScalarSelBytes 0 == I.calldata.extract 0 4) = false by
      simpa [selIs] using hnm, Bool.false_eq_true, ite_false] at e
    rw [uInt256_eq_comm] at e
    exact e
  rd_run rd0 using [lt_four_eq_zero_of_ge hsz hsize, hne]
  exact rd0

end FeProofs.CodeScalar
