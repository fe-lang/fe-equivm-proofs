import FeProofs.Deposit.DepositPrefix
import FeProofs.Common.Basic

/-!
# FeDeposit `deposit`: from the dispatcher arm to pc 650

Combines the argument decoding (EVM and Stele), the length and value checks, and the Stele body
prefix.  Every rejected call is closed here (EVM revert against Stele decoding failure or a
reverting `require`); otherwise both sides stand at pc 650 / statement 9 with matching facts.
Stated under the calldata bound `size < 2^64` (see `DepositBridge`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

theorem ueq_ne_zero_iff (a b : UInt256) : UInt256.eq a b ≠ UInt256.ofNat 0 ↔ a = b := by
  constructor
  · intro h; by_contra hne; exact h (u256_eq_of_ne hne)
  · intro h; rw [h, uInt256_eq_self]; decide

theorem uisZero_ne_zero_iff (a : UInt256) : UInt256.isZero a ≠ UInt256.ofNat 0 ↔ a = UInt256.ofNat 0 := by
  constructor
  · exact u256_isZero_ne_zero_to_eq_zero
  · intro h; rw [h]; decide

theorem umod_gwei_toNat (a : UInt256) :
    (UInt256.mod a (UInt256.ofNat 1000000000)).toNat = a.toNat % 1000000000 := by
  unfold UInt256.mod; rw [if_neg (by decide)]; rfl

theorem lenEq_iff (I : ExecutionEnv) (i : Nat) (hi : 4 + 32 * i < UInt256.size)
    (hg : UInt256.gt (hWord I i) (UInt256.lnot (UInt256.ofNat 4)) = UInt256.ofNat 0) (n : Nat)
    (hn : n < UInt256.size) :
    UInt256.eq (UInt256.ofNat n) (rLen I (hPos I i)) ≠ UInt256.ofNat 0 ↔ dLen I.calldata i = n := by
  rw [ueq_ne_zero_iff, ← hLen_toNat I i hi hg]
  constructor
  · intro h; rw [← h, ulit_toNat' n hn]
  · intro h; apply u256_inj; rw [h, ulit_toNat' n hn]

/-- With the decoder accepted, the EVM checks are the Stele prefix conditions. -/
theorem cOk_iff (I : ExecutionEnv) (evm : EVM.State) (hee : evm.executionEnv = I) (hok : hOk I) :
    cOk I (rLen I (hPos I 0)) (rLen I (hPos I 1)) (rLen I (hPos I 2)) ↔ pOk I.calldata evm := by
  obtain ⟨_, hg0, _, hg1, _, hg2, _⟩ := hok
  have hv : pValue evm = I.weiValue.toNat := by simp [pValue, hee]
  unfold cOk pOk
  rw [lenEq_iff I 0 (by decide) hg0 48 (by decide), lenEq_iff I 1 (by decide) hg1 32 (by decide),
    lenEq_iff I 2 (by decide) hg2 96 (by decide), uisZero_ne_zero_iff, uisZero_ne_zero_iff,
    uisZero_ne_zero_iff, lt_zero_iff, gt_zero_iff, hv]
  have hmod : UInt256.mod I.weiValue (UInt256.ofNat 1000000000) = UInt256.ofNat 0 ↔
      I.weiValue.toNat % 1000000000 = 0 := by
    rw [← umod_gwei_toNat]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact u256_inj (by rw [h]; rfl)
  rw [hmod, udiv_toNat, ulit_toNat' 1000000000000000000 (by decide),
    ulit_toNat' 1000000000 (by decide),
    show (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192)).toNat =
      18446744073709551615 by decide]

/-- The EVM stack at pc 650. -/
abbrev fStack (I : ExecutionEnv) : List UInt256 :=
  [UInt256.div I.weiValue (UInt256.ofNat 1000000000), rAlloc I (hPos I 2), rAlloc I (hPos I 1),
   rFp ByteArray.empty, rFp (hMem2 I), rAlloc I (hPos I 0), rFp (hMem1 I)]

/-- `deposit` up to pc 650: either the call is already refined (every rejection), or both sides
    reach pc 650 / the ninth statement with the decoder, check and prefix facts. -/
theorem depositFront {σ σ₀ A I} {g : UInt256} (hcode : I.code = feDepositBytecode)
    (hsize : I.calldata.size < UInt256.size) (hsmall : I.calldata.size < 2 ^ 64)
    (hsel : selIs I (feDepositSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I ∨
    (hOk I ∧ dArgsOk I.calldata ∧ pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      dispatchMsg contract I.calldata = some depositTransition ∧
      ∃ aw k C, RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 650) (fStack I) (hMem3 I) aw ByteArray.empty σ k C) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feDepositSelBytes 1) rfl hsel
  have h0 : ¬ selIs I (feDepositSelBytes 0) := fun h =>
    absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd := feDepositDispatch_deposit h0 hsel
  obtain ⟨k, C, rd⟩ := feDepositReachDepositBody (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) hcode hsz hsize hsel
  have hee : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv = I := rfl
  by_cases hok : hOk I
  · obtain ⟨hargs, _, _, _⟩ := (hOk_iff I hsz hsmall).mp hok
    obtain ⟨aw, k', C', r242⟩ := depositHead_ok hok rd
    by_cases hc : cOk I (rLen I (hPos I 0)) (rLen I (hPos I 1)) (rLen I (hPos I 2))
    · obtain ⟨k'', C'', r650⟩ := depositChecks_ok hc r242
      exact Or.inr ⟨hok, hargs, (cOk_iff I _ hee hok).mp hc, hd, _, _, _, r650⟩
    · left
      exact RDrev.reEquivExecutionRevert hcode (depositChecks_rev hc r242) hd
        (depositDecode_ok hargs hsmall)
        (ExecFuncBody.execBlockRevert (depositPrefix_rev _ _ hargs
          (fun hp => hc ((cOk_iff I _ hee hok).mpr hp))))
  · left
    have rrev := depositHead_rev hok rd
    by_cases hargs : dArgsOk I.calldata
    · have hp : ¬ pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
        intro hp
        obtain ⟨l0, l1, l2, _⟩ := hp
        exact hok ((hOk_iff I hsz hsmall).mpr ⟨hargs, by omega, by omega, by omega⟩)
      exact RDrev.reEquivExecutionRevert hcode rrev hd (depositDecode_ok hargs hsmall)
        (ExecFuncBody.execBlockRevert (depositPrefix_rev _ _ hargs hp))
    · exact RDrev.reEquivDecodingFailed hcode rrev hd (depositDecode_none hargs hsmall)

end FeProofs.Deposit
