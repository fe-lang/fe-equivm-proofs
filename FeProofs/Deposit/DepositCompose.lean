import FeProofs.Deposit.DepositFront

/-!
# FeDeposit `deposit`: composition from pc 650

`depositBody_of_rest` closes `feDepositDepositBody` from the front (`depositFront`) and one
obligation for the rest of the body: from the pc-650 state, the EVM run and the Stele block from
statement 9 (`body.drop 8`) end alike — both return (with equal account maps and empty output),
both revert, or both halt on a static-mode violation.  The hashing, event and tail segments
discharge that obligation.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

/-- The rest of `deposit` from pc 650 / statement 9 ends alike on both sides. -/
def RestOutcome (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : UInt256) : Prop :=
  (∃ σf frf evmf, RDret feDepositBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σf ByteArray.empty ∧
    ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8)
      (.returned frf evmf (some [])) ∧ σf = evmf.accountMap) ∨
  (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
    ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) .reverted) ∨
  (RDstatic feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
    ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) .staticViolation)

theorem emptyReturn : returnEquiv ByteArray.empty (some []) depositTransition.returnType :=
  returnEquiv.returned rfl (by
    show encodeReturnValues? [] [] = some ByteArray.empty
    native_decide)

/-- `deposit` refines its spec once the rest of the body is shown to end alike from pc 650. -/
theorem depositBody_of_rest {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 64) (hsel : selIs I (feDepositSelBytes 1))
    (hrest : hOk I → dArgsOk I.calldata →
      pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) →
      ∀ aw k C, RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 650) (fStack I) (hMem3 I) aw ByteArray.empty σ k C →
      RestOutcome σ σ₀ A I g) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  rcases depositFront (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsize hsmall hsel with
    hdone | ⟨hok, hargs, hp, hd, aw, k, C, r650⟩
  · exact hdone
  have hdec := depositDecode_ok hargs hsmall
  have hpre := depositPrefix_ok (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.calldata hargs hp
  rcases hrest hok hargs hp aw k C r650 with ⟨σf, frf, evmf, hret, hblk, hacc⟩ | ⟨hrev, hblk⟩ |
      ⟨hst, hblk⟩
  · exact RDret.reEquivExecutionGen hcode hret hd hdec
      (ExecFuncBody.execBlockRet (hpre.run hblk)) hacc emptyReturn
  · exact RDrev.reEquivExecutionRevert hcode hrev hd hdec (ExecFuncBody.execBlockRevert (hpre.run hblk))
  · exact RDstatic.reEquivStaticHalt hcode hst hd hdec (ExecFuncBody.execBlockStatic (hpre.run hblk))

/-- Matching outcomes of the EVM run from `initState` and of a Stele block described by `E`. -/
def OutAt (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : UInt256)
    (E : ExecResult → Prop) : Prop :=
  (∃ σf frf evmf, RDret feDepositBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σf ByteArray.empty ∧
    E (.returned frf evmf (some [])) ∧ σf = evmf.accountMap) ∨
  (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
    E .reverted) ∨
  (RDstatic feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
    E .staticViolation)

theorem RestOutcome_eq (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : UInt256) :
    RestOutcome σ σ₀ A I g = OutAt σ σ₀ A I g
      (ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8)) := rfl

/-- Transport an outcome back along a block prefix. -/
theorem OutAt.mono {σ σ₀ A I g} {E₁ E₀ : ExecResult → Prop} (hE : ∀ res, E₁ res → E₀ res)
    (h : OutAt σ σ₀ A I g E₁) : OutAt σ σ₀ A I g E₀ := by
  rcases h with ⟨σf, frf, evmf, hr, he, ha⟩ | ⟨hr, he⟩ | ⟨hr, he⟩
  · exact Or.inl ⟨σf, frf, evmf, hr, hE _ he, ha⟩
  · exact Or.inr (Or.inl ⟨hr, hE _ he⟩)
  · exact Or.inr (Or.inr ⟨hr, hE _ he⟩)

/-- A revert of the EVM run against a reverting block. -/
theorem OutAt.rev {σ σ₀ A I g} {E : ExecResult → Prop}
    (hr : RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (he : E .reverted) : OutAt σ σ₀ A I g E := Or.inr (Or.inl ⟨hr, he⟩)

/-- A static-mode halt of the EVM run against a block halting on a state change. -/
theorem OutAt.static {σ σ₀ A I g} {E : ExecResult → Prop}
    (hr : RDstatic feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (he : E .staticViolation) : OutAt σ σ₀ A I g E := Or.inr (Or.inr ⟨hr, he⟩)

/-- Chain three segments: each either ends (an `OutAt` of its own block) or reaches a state `X`
    of the next segment whose block runs back into its own. -/
theorem OutAt.chain3 {σ σ₀ A I g} {α β : Type} {E₀ : ExecResult → Prop}
    {P₁ : α → Prop} {E₁ : α → ExecResult → Prop} {P₂ : β → Prop} {E₂ : β → ExecResult → Prop}
    (seg₁ : OutAt σ σ₀ A I g E₀ ∨ ∃ x, P₁ x ∧ ∀ res, E₁ x res → E₀ res)
    (seg₂ : ∀ x, P₁ x → OutAt σ σ₀ A I g (E₁ x) ∨ ∃ y, P₂ y ∧ ∀ res, E₂ y res → E₁ x res)
    (seg₃ : ∀ y, P₂ y → OutAt σ σ₀ A I g (E₂ y)) : OutAt σ σ₀ A I g E₀ := by
  rcases seg₁ with h | ⟨x, hx, h₁⟩
  · exact h
  rcases seg₂ x hx with h | ⟨y, hy, h₂⟩
  · exact h.mono h₁
  · exact ((seg₃ y hy).mono h₂).mono h₁

end FeProofs.Deposit
