import FeProofs.ERC20.Dispatch
import FeProofs.ERC20.MapStorage
import FeProofs.Common.Basic

/-!
# FeERC20 `balanceOf(address)`

Arm entry pc 540: call-value check, head-size check (pc 546), the canonical-address check
`SHR(160, word) = 0` (pc 558), then `MSTORE(0, owner); MSTORE(32, 0); SLOAD(KECCAK256(0, 64))`
returned as one word (pc 568).  Every failed check jumps to the revert block at pc 86.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.ERC20

set_option maxRecDepth 2000000

/-- `balanceOf(address)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem feERC20BalanceOfBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feERC20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feERC20SelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feERC20SelBytes 3) rfl hsel
  have hd := feERC20Dispatch_balanceOf
    (not_selIs_of_selIs hsel (by decide)) (not_selIs_of_selIs hsel (by decide))
    (not_selIs_of_selIs hsel (by decide)) hsel
  obtain ⟨k, C, rd⟩ := feERC20ReachBalanceOfBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevert hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  by_cases hok : 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4
  swap
  · have hbad : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    rd_run rd using [hwv, solcDecodeLenCheckBad_4_32 hsz hsize hbad]
    exact RDrev.reEquivDecodingFailed hcode rd hd
      (hbad.elim (decodeCalldata_address_none_short hsz) decodeCalldata_address_none_huge)
  obtain ⟨hlen, hhi⟩ := hok
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize,
      shiftRight160_ne_zero (Nat.le_of_not_lt hcanon)]
    exact RDrev.reEquivDecodingFailed hcode rd hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
  rd_run rd using [hwv, solcDecodeLenCheckOk_4_32 hlen hhi hsize, shiftRight160_eq_zero hcanon]
  rw [keccakWord_mapSlot] at rd
  u256_lits at rd
  rw [toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)] at rd
  have hread := balanceOf_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (L := (∅ : Store).insert "owner"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) hcanon
    (by simp) (store_get_self _ _ _)
  rw [storageLoad_initState_ofUInt256_solcSlotWordAt] at hread
  exact rd.reEquivExecution hcode hd (decodeCalldata_address_ok hlen hhi hcanon)
    (nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) hread)
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end FeProofs.ERC20
