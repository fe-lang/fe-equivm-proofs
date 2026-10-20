import FeProofs.Deposit.Common
import Reasoning.ExternalCall

/-!
# FeDeposit `get_deposit_root()` — Stele-side storage and loop facts

Reads of `deposit_count`, `branch[height]` and `zero_hashes[height]` as words of slots `32`,
`height` and `33 + height`, and the loop's condition, parity test, halving and increment as
word operations.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- The generated Solidity layout of the contract's storage. -/
def layout : StorageLayout := storageBackend.locate?

theorem config_storageBackend : config.storageBackend = solidityStorageBackend layout := rfl

abbrev uint256Elem : ElemType := .int (.uint ⟨256, by decide⟩)

theorem keyWord_ofNat {i : Nat} (hi : i < 32) :
    keyValueToWord (.int (Int.ofNat i)) = UInt256.ofNat i := by
  simp only [keyValueToWord, EVM.wordOfInt, EVM.word]
  rw [if_neg (by simp)]
  rfl

/-- `deposit_count` is the word of slot 32. -/
theorem evalDepositCount {L : Store} {evm : EVM.State} (hbase : L.get? "deposit_count" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "deposit_count", steps := [] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (UInt256.ofNat 32)).toNat)) := by
  rw [evalExpr_storage_scalar (t := uint256Elem) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps]; rfl) rfl config_storageBackend
    (loc := uint256Loc (UInt256.ofNat 32)) rfl, storageLocLoad_uint256]

/-- An in-bounds element of a `uint256[32]` array whose words start at slot `base`. -/
theorem evalArrayElem (name : Ident) (base : UInt256) {L : Store} {evm : EVM.State}
    {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i)))
    (hbase : L.get? name = none)
    (hty : storageTypeAt? contract.storage { base := name, steps := [] } =
      some (.array (.elem uint256Elem) 32))
    (htyElem : storageTypeAt? contract.storage { base := name, steps := [.aindex (.int (Int.ofNat i))] } =
      some (.elem uint256Elem))
    (hloc : layout { base := name, steps := [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (uint256Loc (base + UInt256.ofNat i)))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := name, steps := [.aindex idx] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (base + UInt256.ofNat i)).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := L } evm
      { base := name, steps := [.aindex idx] } =
      .ok { base := name, steps := [.aindex (.int (Int.ofNat i))] } := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
      arrayIndexInBounds?, hty, bind, EvalResult.bind, pure, EvalResult.ofOption, hi]
  rw [evalExpr_storage_scalar (t := uint256Elem) hbase her htyElem config_storageBackend hloc,
    storageLocLoad_uint256]

theorem evalBranch {L : Store} {evm : EVM.State} {i : Nat} (hi : i < 32)
    (hh : L.get? "height" = some (.int (Int.ofNat i))) (hbase : L.get? "branch" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "branch", steps := [.aindex (.var "height")] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (⟨0⟩ + UInt256.ofNat i)).toNat)) := by
  refine evalArrayElem "branch" ⟨0⟩ hi ?_ hbase rfl rfl ?_
  · rw [evalExpr?, hh]; rfl
  · show some (StorageAddr.leaf _) = _
    simp only [keyWord_ofNat hi, ulit_toNat' i (lt_of_lt_of_le hi (by decide)), Nat.div_one,
      Nat.mod_one, Nat.zero_mul]
    rfl

theorem evalZeroHash {L : Store} {evm : EVM.State} {i : Nat} (hi : i < 32)
    (hh : L.get? "height" = some (.int (Int.ofNat i))) (hbase : L.get? "zero_hashes" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "zero_hashes", steps := [.aindex (.var "height")] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (⟨33⟩ + UInt256.ofNat i)).toNat)) := by
  refine evalArrayElem "zero_hashes" ⟨33⟩ hi ?_ hbase rfl rfl ?_
  · rw [evalExpr?, hh]; rfl
  · show some (StorageAddr.leaf _) = _
    simp only [keyWord_ofNat hi, ulit_toNat' i (lt_of_lt_of_le hi (by decide)), Nat.div_one,
      Nat.mod_one, Nat.zero_mul]
    rfl

/-! ## Loop arithmetic -/

theorem evalLoopCond {L : Store} {evm : EVM.State} {i : Nat}
    (hh : L.get? "height" = some (.int (Int.ofNat i))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .lt (.var "height") (.intLit 32)) = .ok (.bool (decide (i < 32))) := by
  simp only [evalExpr?, hh, bind, EvalResult.bind, pure, EvalResult.ofOption, evalBinaryOp?]
  congr 2
  simp only [Int.ofNat_eq_natCast, decide_eq_decide]
  omega

theorem land_one_toNat (s : UInt256) : (UInt256.land s (UInt256.ofNat 1)).toNat = s.toNat % 2 := by
  rw [uland_toNat]
  change Nat.land s.toNat 1 = s.toNat % 2
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, nat_land_mask_eq_mod, pow_one]

theorem evalParity {L : Store} {evm : EVM.State} {s : UInt256}
    (hs : L.get? "size" = some (.int (Int.ofNat s.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .eq
        (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "size") (.intLit 1)) (.intLit 1)) =
      .ok (.bool (decide (s.toNat % 2 = 1))) := by
  have hand : evalBinaryOp? (.bitAnd (.uint ⟨256, by decide⟩)) (.int (Int.ofNat s.toNat)) (.int 1) =
      .ok (.int (Int.ofNat (s.toNat % 2))) := by
    simp only [evalBinaryOp?, evalIntBitwise]
    have hn : normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat s.toNat) = Int.ofNat s.toNat :=
      normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr s.val.isLt)
    have h1 : normalizeInt (.uint ⟨256, by decide⟩) 1 = 1 := by decide
    have hl : Nat.land s.toNat 1 = s.toNat % 2 := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, nat_land_mask_eq_mod, pow_one]
    simp only [IntType.bitWidth, hn, h1, Int.toNat_natCast, Int.toNat_one, Int.ofNat_eq_natCast] at *
    rw [show (Nat.land s.toNat 1 : Nat) = s.toNat % 2 from hl]
    congr 2
    exact normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _)
      (Int.ofNat_lt.mpr (lt_trans (Nat.mod_lt _ (by decide)) (by decide)))
  simp only [evalExpr?, hs, hand, bind, EvalResult.bind, pure, EvalResult.ofOption]
  simp only [evalBinaryOp?]
  congr 2
  by_cases hp : s.toNat % 2 = 1
  · rw [hp]; simp
  · have h0 : s.toNat % 2 = 0 := by omega
    rw [h0]; simp

theorem evalHalf {L : Store} {evm : EVM.State} {s : UInt256}
    (hs : L.get? "size" = some (.int (Int.ofNat s.toNat))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .div (.var "size") (.intLit 2)) =
      .ok (.int (Int.ofNat (UInt256.shiftRight s (UInt256.ofNat 1)).toNat)) := by
  have hshr : (UInt256.shiftRight s (UInt256.ofNat 1)).toNat = s.toNat / 2 := by
    unfold UInt256.shiftRight
    rw [if_neg (by decide)]
    change (s.toNat >>> 1) % UInt256.size = s.toNat / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) s.val.isLt)
  simp only [evalExpr?, hs, bind, EvalResult.bind, pure, EvalResult.ofOption, evalBinaryOp?]
  rw [hshr]
  simp only [show ¬ ((2 : Int) = 0) from by decide, if_false]
  rfl

theorem evalInc {L : Store} {evm : EVM.State} {i : Nat}
    (hh : L.get? "height" = some (.int (Int.ofNat i))) :
    evalExpr? config { contract := contract, locals := L } evm
        (.binary .add (.var "height") (.intLit 1)) = .ok (.int (Int.ofNat (i + 1))) := by
  simp only [evalExpr?, hh, bind, EvalResult.bind, pure, EvalResult.ofOption, evalBinaryOp?]
  rfl

theorem ofNat_succ_add (i : Nat) (hi : i + 1 < UInt256.size) :
    UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' 1 (by omega), ulit_toNat' i (by omega), ulit_toNat' (i + 1) hi,
    Nat.mod_eq_of_lt (by omega)]
  omega

end FeProofs.Deposit
