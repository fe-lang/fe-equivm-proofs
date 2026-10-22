import FeProofs.WETH9.Dispatch
import FeProofs.WETH9.MapStorage
import FeProofs.Common.Basic

/-!
# FeWETH9 `balanceOf(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 523; reach lemma `feWETH9ReachBalanceOfBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem feWETH9BalanceOfBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 6) rfl hsel
  have hd := feWETH9Dispatch_balanceOf
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachBalanceOfBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 1 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (hbad.elim (decodeCalldata_address_none_short hsz) decodeCalldata_address_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize,
      shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize, shiftRight160_eq_zero hcanon]
  u256_lits at rd
  rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := balanceOf_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (L := (∅ : Store).insert "owner"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
    (by simp) (evalVarF (store_get_self _ _ _))
  rw [keyValueToWord_address_of_canonical _ hcanon,
    storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  exact RDret.reEquivExecutionSel hcode rd hd (decodeCalldata_address_ok hlen hhi hcanon)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.WETH9
