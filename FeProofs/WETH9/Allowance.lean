import FeProofs.WETH9.Dispatch
import FeProofs.WETH9.MapStorage
import FeProofs.Common.Basic

/-!
# FeWETH9 `allowance(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 652; reach lemma `feWETH9ReachAllowanceBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- `allowance(address,address)`: the theorem `Correct.lean` routes selector 10 to. -/
theorem feWETH9AllowanceBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 10)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 10) rfl hsel
  have hd := feWETH9Dispatch_allowance hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachAllowanceBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd (hbad.elim
      (decodeCalldata_address_address_none_short hsz) decodeCalldata_address_address_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (decodeCalldata_address_address_none_noncanon0 hlen hhi hc0)
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact RDrev.reEquivDecodingFailedSel hcode rd hd
      (decodeCalldata_address_address_none_noncanon1 hlen hhi hc0 hc1)
  rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  u256_lits at rd
  rw [keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    keccakWord_mapSlotAt _ _ _ 160 192 rfl (by decide),
    toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := allowance_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (L := ((∅ : Store).insert "owner"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "guy"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)))
    (by simp) (evalVarF ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
    (evalVarF (store_get_self _ _ _))
  rw [keyValueToWord_address_of_canonical _ hc0, keyValueToWord_address_of_canonical _ hc1,
    storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  exact RDret.reEquivExecutionSel hcode rd hd (decodeCalldata_address_address_ok hlen hhi hc0 hc1)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.WETH9
