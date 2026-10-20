import FeProofs.Deposit.DepositDecode
import Reasoning.ABIViews

/-!
# FeDeposit: the decoded `deposit_data_root`

`uint256(deposit_data_root)` is the calldata word at `0x64`, the operand of the bytecode's
`CALLDATALOAD(0x64)` comparison.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs.Deposit

theorem dRootBytes_length (cd : ByteArray) (hn : 132 ≤ cd.size) : (dRootBytes cd).length = 32 := by
  simp only [dRootBytes, dArgs, List.length_take, List.length_drop, cd_toList_length]
  omega

theorem dRootBytes_value (cd : ByteArray) (hn : 132 ≤ cd.size) :
    fromBytesBigEndian (dRootBytes cd) = (calldataWord cd 100).toNat := by
  have hl := dRootBytes_length cd hn
  have hword : ABI.bytesToWord (dRootBytes cd) = calldataWord cd 100 := by
    have h' := decode_word_at_eq_any cd 100 (by omega)
    simpa [dRootBytes, dArgs, List.drop_drop, List.take_take] using h'
  rw [← hword]
  exact (bytesToWord_toNat_of_len _ hl).symm

/-- `uint256(deposit_data_root)` evaluates to `CALLDATALOAD(0x64)`. -/
theorem evalRootCast {cfg : Config} {stele : Frame} {evm : EVM.State} (cd : ByteArray)
    (hn : 132 ≤ cd.size)
    (hr : stele.locals.get? "deposit_data_root" = some (.fixedBytes ⟨31, by decide⟩ (dRootBytes cd))) :
    evalExpr? cfg stele evm
        (.cast (.var "deposit_data_root") (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (calldataWord cd 100).toNat)) := by
  have hv : fixedBytesToNat? (31 : Fin 32) (dRootBytes cd) = some (calldataWord cd 100).toNat := by
    simp only [fixedBytesToNat?, fixedBytesValid, dRootBytes_length cd hn, dRootBytes_value cd hn]
    rfl
  have hr' : stele.locals[("deposit_data_root" : Ident)]? =
      some (.fixedBytes ⟨31, by decide⟩ (dRootBytes cd)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hr
  simp [evalExpr?, hr', castValue?, hv, EvalResult.ofOption, EvalResult.bind, bind]

end FeProofs.Deposit
