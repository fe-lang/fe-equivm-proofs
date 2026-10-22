import FeProofs.WETH9.Dispatch
import FeProofs.Common.Basic

/-!
# FeWETH9 `decimals()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 506; reach lemma `feWETH9ReachDecimalsBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

abbrev uint8Int : ABI.IntType := .uint ⟨8, by decide⟩

/-- `decimals`: the low byte of slot 2, as a `uint8` field at offset 0. -/
theorem decimals_read {L : Store} {evm : EVM.State} (hL : L.get? "decimals" = none) :
    evalExpr? config { contract := contract, locals := L } evm (.storage { base := "decimals" }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (UInt256.ofNat 255)).toNat)) :=
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int uint8Int) (er := { base := "decimals", steps := [] })
    (loc := { slot := ⟨2⟩, offset := 0, size := 1, hbound := by decide, type := .int uint8Int })
    hL (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    rfl rfl rfl (storageLocLoad_uint_offset0 evm ⟨2⟩ 1 ⟨8, by decide⟩ (by decide) (by decide))

/-- `decimals()`: the theorem `Correct.lean` routes selector 5 to. -/
theorem feWETH9DecimalsBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 5) rfl hsel
  have hd := feWETH9Dispatch_decimals hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachDecimalsBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd using [hwv]
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := decimals_read (L := ∅) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (by simp)
  rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  rw [u256_land_comm] at rd
  change RDret _ _ _ σ ((UInt256.land (solcSlotWordAt ⟨2⟩ σ I) (UInt256.ofNat 255)).toByteArray) at rd
  have h8 : (UInt256.land (solcSlotWordAt ⟨2⟩ σ I) (UInt256.ofNat 255)).toNat < EVM.twoPow 8 := by
    rw [uland_toNat, show (UInt256.ofNat 255).toNat = 255 from rfl,
      show EVM.twoPow 8 = 256 from by decide]
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  exact RDret.reEquivExecutionSel hcode rd hd
    (show decodeCalldata [] [] I.calldata = some ∅ from decodeCalldata_empty_ok hsz)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint8ReturnEncoding _ h8))

end FeProofs.WETH9
