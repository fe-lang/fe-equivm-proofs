import FeProofs.Deposit.DepositBridge
import Reasoning.SteleBody

/-!
# FeDeposit `deposit` body prefix (Stele side)

The first eight statements of `deposit`: the three length `require`s, the two call-value
`require`s, `deposit_amount = msg.value / 1 gwei`, its `uint64` range `require`, and
`amount = uint64(deposit_amount)`.  Either one of the `require`s fails (the body reverts) or the
block continues with `deposit_amount` and `amount` bound.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs.Deposit

abbrev pFrame (L : Store) : Frame := { contract := contract, locals := L }

theorem pLenEval (evm : EVM.State) (L : Store) (x : Ident) (b : ByteArray)
    (hx : L.get? x = some (.bytes b)) (n : Int) :
    evalExpr? config (pFrame L) evm
        (.binary .eq (.arrayLength .localVar { base := x, steps := [] }) (.intLit n)) =
      .ok (.bool (Value.int (Int.ofNat b.size) == Value.int n)) := by
  have hx' : L[x]? = some (.bytes b) := by simpa [Std.HashMap.get?_eq_getElem?] using hx
  simp [evalExpr?, hx', readLocalPath?, evalBinaryOp?, EvalResult.bind, bind, pure]

abbrev pValue (evm : EVM.State) : Nat := evm.executionEnv.weiValue.toNat

theorem pGeEval (evm : EVM.State) (L : Store) :
    evalExpr? config (pFrame L) evm
        (.binary .ge (.env .callvalue) (.intLit 1000000000000000000)) =
      .ok (.bool (decide ((Int.ofNat (pValue evm)) ≥ 1000000000000000000))) := by
  simp [evalExpr?, envValue, evalBinaryOp?, EvalResult.bind, bind, pure]; rfl

theorem pModEval (evm : EVM.State) (L : Store) :
    evalExpr? config (pFrame L) evm
        (.binary .eq (.binary .mod (.env .callvalue) (.intLit 1000000000)) (.intLit 0)) =
      .ok (.bool (Value.int (Int.ofNat (pValue evm) % 1000000000) == Value.int 0)) := by
  simp [evalExpr?, envValue, evalBinaryOp?, EvalResult.bind, bind, pure]; rfl

theorem pDivEval (evm : EVM.State) (L : Store) :
    evalExpr? config (pFrame L) evm (.binary .div (.env .callvalue) (.intLit 1000000000)) =
      .ok (.int (Int.ofNat (pValue evm) / 1000000000)) := by
  simp [evalExpr?, envValue, evalBinaryOp?, EvalResult.bind, bind, pure]; rfl

theorem dPayload_size (cd : ByteArray) (o : Nat) (h : 4 + o + 32 + dWord cd o ≤ cd.size) :
    (dPayload cd o).size = dWord cd o := by
  show ((((dArgs cd).drop (o + 32)).take (dWord cd o)).toArray).size = _
  rw [List.size_toArray, List.length_take, List.length_drop, List.length_drop, cd_toList_length]
  omega

/-- The block's frame after `amount` is bound. -/
abbrev pLocals (cd : ByteArray) (evm : EVM.State) : Store :=
  ((dStore cd).insert "deposit_amount" (.int (Int.ofNat (pValue evm) / 1000000000))).insert
    "amount" (.int (Int.ofNat (pValue evm) / 1000000000))

/-- The prefix's conditions. -/
def pOk (cd : ByteArray) (evm : EVM.State) : Prop :=
  dLen cd 0 = 48 ∧ dLen cd 1 = 32 ∧ dLen cd 2 = 96 ∧ 1000000000000000000 ≤ pValue evm ∧
    pValue evm % 1000000000 = 0 ∧ pValue evm / 1000000000 ≤ 18446744073709551615

theorem dStore_pubkey (cd : ByteArray) :
    (dStore cd).get? "pubkey" = some (.bytes (dPayload cd (dWord cd 0))) := by
  unfold dStore
  store_get
theorem dStore_wc (cd : ByteArray) :
    (dStore cd).get? "withdrawal_credentials" = some (.bytes (dPayload cd (dWord cd 32))) := by
  unfold dStore
  store_get
theorem dStore_sig (cd : ByteArray) :
    (dStore cd).get? "signature" = some (.bytes (dPayload cd (dWord cd 64))) := by
  unfold dStore
  store_get

theorem depositPrefix_ok (evm : EVM.State) (cd : ByteArray) (hok : dArgsOk cd) (hp : pOk cd evm) :
    ABlock config evm (pFrame (dStore cd)) depositTransition.body (pFrame (pLocals cd evm))
      (depositTransition.body.drop 8) := by
  obtain ⟨_, hb0, hb1, hb2⟩ := hok
  obtain ⟨h0, h1, h2, hv1, hv2, hv3⟩ := hp
  have s0 := dPayload_size cd _ hb0.2
  have s1 := dPayload_size cd _ hb1.2
  have s2 := dPayload_size cd _ hb2.2
  refine (((((((ABlock.start.requireStep ?_).requireStep ?_).requireStep ?_).requireStep ?_).requireStep
    ?_).letStep ?_).requireStep ?_).letStep ?_
  · have e : (dPayload cd (dWord cd 0)).size = 48 := s0.trans h0
    rw [pLenEval _ _ _ _ (dStore_pubkey cd), e]; rfl
  · have e : (dPayload cd (dWord cd 32)).size = 32 := s1.trans h1
    rw [pLenEval _ _ _ _ (dStore_wc cd), e]; rfl
  · have e : (dPayload cd (dWord cd 64)).size = 96 := s2.trans h2
    rw [pLenEval _ _ _ _ (dStore_sig cd), e]; rfl
  · rw [pGeEval]; simp; omega
  · rw [pModEval]; simp; omega
  · exact pDivEval _ _
  · simp [evalExpr?, EvalResult.ofOption, evalBinaryOp?, EvalResult.bind, bind, pure]; omega
  · simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert_self, castValue?]
    rw [normalizeInt_uint_eq_self _ _ (by simp only [Int.ofNat_eq_coe]; omega) (by
      show Int.ofNat (pValue evm) / 1000000000 < Int.ofNat (EVM.twoPow 64)
      unfold EVM.twoPow; simp only [Int.ofNat_eq_coe]; push_cast; omega)]

/-- If a prefix condition fails, the body reverts at that `require`. -/
theorem depositPrefix_rev (evm : EVM.State) (cd : ByteArray) (hok : dArgsOk cd) (hbad : ¬ pOk cd evm) :
    ExecBlock config (pFrame (dStore cd)) evm depositTransition.body .reverted := by
  obtain ⟨_, hb0, hb1, hb2⟩ := hok
  have s0 := dPayload_size cd _ hb0.2
  have s1 := dPayload_size cd _ hb1.2
  have s2 := dPayload_size cd _ hb2.2
  unfold pOk at hbad
  have hne : ∀ (a : Nat) (b : Int), Int.ofNat a ≠ b →
      (Value.int (Int.ofNat a) == Value.int b) = false := by
    intro a b hab; simp only [Int.ofNat_eq_coe] at hab; simp [hab]
  have a0 : ABlock config evm (pFrame (dStore cd)) depositTransition.body (pFrame (dStore cd))
      depositTransition.body := ABlock.start
  by_cases h0 : dLen cd 0 = 48
  swap
  · have h0' : dWord cd (dWord cd 0) ≠ 48 := h0
    refine a0.requireRevert ?_
    rw [pLenEval _ _ _ _ (dStore_pubkey cd), s0,
      hne _ 48 (by simp only [Int.ofNat_eq_coe]; exact_mod_cast h0')]
  have a1 := a0.requireStep (by rw [pLenEval _ _ _ _ (dStore_pubkey cd), s0.trans h0]; rfl)
  by_cases h1 : dLen cd 1 = 32
  swap
  · have h1' : dWord cd (dWord cd 32) ≠ 32 := h1
    refine a1.requireRevert ?_
    rw [pLenEval _ _ _ _ (dStore_wc cd), s1,
      hne _ 32 (by simp only [Int.ofNat_eq_coe]; exact_mod_cast h1')]
  have a2 := a1.requireStep (by rw [pLenEval _ _ _ _ (dStore_wc cd), s1.trans h1]; rfl)
  by_cases h2 : dLen cd 2 = 96
  swap
  · have h2' : dWord cd (dWord cd 64) ≠ 96 := h2
    refine a2.requireRevert ?_
    rw [pLenEval _ _ _ _ (dStore_sig cd), s2,
      hne _ 96 (by simp only [Int.ofNat_eq_coe]; exact_mod_cast h2')]
  have a3 := a2.requireStep (by rw [pLenEval _ _ _ _ (dStore_sig cd), s2.trans h2]; rfl)
  by_cases hv1 : 1000000000000000000 ≤ pValue evm
  swap
  · refine a3.requireRevert ?_
    rw [pGeEval]; simp; omega
  have a4 := a3.requireStep (by rw [pGeEval]; simp; omega)
  by_cases hv2 : pValue evm % 1000000000 = 0
  swap
  · refine a4.requireRevert ?_
    rw [pModEval]; simp; omega
  have a5 := a4.requireStep (by rw [pModEval]; simp; omega)
  have a6 := a5.letStep (pDivEval _ _)
  have hv3 : ¬ pValue evm / 1000000000 ≤ 18446744073709551615 :=
    fun hv3 => hbad ⟨h0, h1, h2, hv1, hv2, hv3⟩
  refine a6.requireRevert ?_
  simp [evalExpr?, EvalResult.ofOption, evalBinaryOp?, EvalResult.bind, bind, pure]; omega

end FeProofs.Deposit
