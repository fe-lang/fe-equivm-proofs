import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `allowance(address,address)`

Arm entry pc 743: call-value check, head-size check (pc 749), the canonical-address checks for
`owner` (pc 761) and `spender` (pc 771), then the nested map read
`SLOAD(keccak256(spender ‖ keccak256(owner ‖ 1)))` returned as one word (pc 781).  Every failed
check jumps to the revert block at pc 86.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- `allowance(address,address)`: the theorem `Correct.lean` routes selector 5 to. -/
theorem feERC20AllowanceBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 5) rfl hsel
  have hd := feERC20Dispatch_allowance
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachAllowanceBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad 2 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd (hbad.elim
      (decodeCalldata_address_address_none_short hsz) decodeCalldata_address_address_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  have hc := solcDecodeLenCheckOk_4_64 hlen hhi hsize
  by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_ne_zero (Nat.le_of_not_lt hc0)]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (decodeCalldata_address_address_none_noncanon0 hlen hhi hc0)
  by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_ne_zero (Nat.le_of_not_lt hc1)]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (decodeCalldata_address_address_none_noncanon1 hlen hhi hc0 hc1)
  rd_run rd using [hwv, hc, shiftRight160_eq_zero hc0, shiftRight160_eq_zero hc1]
  rw [keccakWord_mapSlot, keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := allowance_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (L := ((∅ : Store).insert "owner"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "spender"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)))
    hc0 hc1 (by simp) ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    (store_get_self _ _ _)
  rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  exact rd.reEquivExecution hcode hd (decodeCalldata_address_address_ok hlen hhi hc0 hc1)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.ERC20
