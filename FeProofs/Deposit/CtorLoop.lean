import FeProofs.Deposit.Le64
import FeProofs.Deposit.RootFacts
import FeProofs.Deposit.Sha256
import FeProofs.Deposit.CreationBlocks_001

/-!
# FeDeposit constructor loop

The initcode fills `zero_hashes[1..31]`: for `h < 31` it loads `zero_hashes[h]` (slot `33 + h`),
stores it at memory words 0 and 1, hashes `[0, 64)` with precompile 2 (reverting unless the call
succeeds and returns a word), and stores the first returned word in slot `34 + h`.  It keeps
`[33 + h, h]` on the stack and tests `h + 1 < 31` at the end of an iteration (pc 68), so after the
last one it stands past the loop at pc 69 (`CtorAt`).  The spec's `for` loop makes the same
storage reads, the same opaque `sha256_pair` calls and the same writes; `ctorLoop` simulates the
two loops together by induction on the remaining iterations, linking the EVM accounts to the
Stele state with `SourceState`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- The initcode as the creation summaries see it (no constructor arguments). -/
abbrev ctorCode : ByteArray := feDepositCreationBytecode ++ ByteArray.empty

/-! ## The hashed buffer -/

/-! ## `zero_hashes[i]`: slot `33 + i`

Adapted from the `get_deposit_root` read facts, with the write counterpart. -/

/-- The generated Solidity layout of the contract's storage. -/
def ctorLayout : StorageLayout := storageBackend.locate?

theorem ctor_storageBackend : config.storageBackend = solidityStorageBackend ctorLayout := rfl

theorem zeroHashRef_eval {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i))) :
    evalStorageRef config { contract := contract, locals := L } evm
        { base := "zero_hashes", steps := [.aindex idx] } =
      .ok { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } := by
  have hty : storageTypeAt? contract.storage { base := "zero_hashes", steps := [] } =
      some (.array (.elem (.int (.uint ⟨256, by decide⟩))) 32) := rfl
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
    arrayIndexInBounds?, hty, bind, EvalResult.bind, pure, EvalResult.ofOption, hi]

theorem zeroHash_type (i : Nat) :
    storageTypeAt? contract.storage { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

theorem zeroHash_loc {i : Nat} (hi : i < 32) :
    ctorLayout { base := "zero_hashes", steps := [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (uint256Loc (⟨33⟩ + UInt256.ofNat i))) := by
  show some (StorageAddr.leaf _) = _
  simp only [keyWord_ofNat, ulit_toNat' i (lt_of_lt_of_le hi (by decide)), Nat.div_one,
    Nat.mod_one, Nat.zero_mul]
  rfl

theorem zeroHash_read {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i)))
    (hbase : L.get? "zero_hashes" = none) :
    evalExpr? config { contract := contract, locals := L } evm
        (.storage { base := "zero_hashes", steps := [.aindex idx] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (⟨33⟩ + UInt256.ofNat i)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int (.uint ⟨256, by decide⟩)) hbase (zeroHashRef_eval hi hidx)
    (zeroHash_type i) ctor_storageBackend (zeroHash_loc hi), storageLocLoad_uint256]

theorem zeroHash_write {L : Store} {evm : EVM.State} {idx : Expr} {i : Nat} (hi : i < 32)
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx = .ok (.int (Int.ofNat i)))
    (hbase : L.get? "zero_hashes" = none) (v : UInt256) :
    assignStorageRef? config { contract := contract, locals := L } evm .storage
        { base := "zero_hashes", steps := [.aindex idx] } (.int (Int.ofNat v.toNat)) =
      .ok ({ contract := contract, locals := L },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (⟨33⟩ + UInt256.ofNat i) v) :=
  assignStorageRef_storage_scalar_value hbase (zeroHashRef_eval hi hidx) (zeroHash_type i)
    ctor_storageBackend (zeroHash_loc hi) (Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm _ v)

/-! ## Word facts for the loop -/

theorem succ_word {h : ℕ} (hlt : h < 31) :
    UInt256.ofNat 1 + UInt256.ofNat h = UInt256.ofNat (h + 1) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' 1 (by decide), ulit_toNat' h (lt_trans hlt (by decide)),
    ulit_toNat' (h + 1) (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega),
    Nat.mod_eq_of_lt (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)]
  omega

/-! ## The loop as Stele syntax -/

abbrev ctorInit : List Stmt :=
  [.letDecl "height" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

abbrev ctorCond : Expr := .binary .lt (.var "height") (.intLit 31)

abbrev ctorPost : List Stmt :=
  [.assign .localVar { base := "height", steps := [] } (.binary .add (.var "height") (.intLit 1))]

abbrev ctorLoopBody : List Stmt :=
  [ .letDecl "cur" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage { base := "zero_hashes", steps := [.aindex (.var "height")] }),
    .internalCall "sha256_pair" [.var "cur", .var "cur"] "next",
    .assign .storage
      { base := "zero_hashes", steps := [.aindex (.binary .add (.var "height") (.intLit 1))] }
      (.var "next") ]

theorem ctorBody_eq :
    contract.ctor.body =
      [.require (.binary .eq (.env .callvalue) (.intLit 0)),
       .for ctorInit ctorCond ctorPost ctorLoopBody] := rfl

theorem evalHeightLt {L : Store} {evm : EVM.State} {h : ℕ}
    (hh : L.get? "height" = some (.int (Int.ofNat h))) :
    evalExpr? config { contract := contract, locals := L } evm ctorCond =
      .ok (.bool (decide (Int.ofNat h < 31))) :=
  evalBin (by decide) (by decide) (evalVarF hh) (evalLit 31) (evalBinaryOp_lt_int_ok _ _)

/-! ## The simulation -/

/-- `zero_hashes[h]` as the loop reads it. -/
abbrev curWord (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) : UInt256 :=
  solcSlotWord σ I (⟨33⟩ + UInt256.ofNat h)

abbrev loopL1 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) : Store :=
  L.insert "cur" (.int (Int.ofNat (curWord σ I h).toNat))

abbrev loopL2 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) (out : ByteArray) : Store :=
  (loopL1 L σ I h).insert "next" (shaDigest out)

abbrev loopL3 (L : Store) (σ : AccountMap) (I : ExecutionEnv) (h : ℕ) (out : ByteArray) : Store :=
  (loopL2 L σ I h out).insert "height" (.int (Int.ofNat (h + 1)))

/-- The EVM at the start of Stele loop iteration `h`: in the loop body (pc 12) while `h < 31`,
    past the loop (pc 69) after the last iteration. -/
def CtorAt (s0 : State) (I : ExecutionEnv) (g : Sat256) (h : ℕ) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (σ : AccountMap) : Prop :=
  (h < 31 ∧ ∃ k C, RD ctorCode I g s0 (UInt256.ofNat 12)
    [UInt256.ofNat 33 + UInt256.ofNat h, UInt256.ofNat h] mem aw rdata σ k C) ∨
  (31 ≤ h ∧ ∃ k C x, RD ctorCode I g s0 (UInt256.ofNat 69) [UInt256.ofNat h, x] mem aw rdata σ k C)

theorem ctorLoop {I : ExecutionEnv} {g : Sat256} {s0 : State} (hperm : I.perm = true) :
    ∀ n h, h + n = 31 → ∀ {σh : AccountMap} {evmh : EVM.State} {mem rdata : ByteArray}
      {aw : UInt256} {L : Store},
      L.get? "height" = some (.int (Int.ofNat h)) → L.get? "zero_hashes" = none →
      CtorAt s0 I g h mem aw rdata σh →
      SourceState s0 I σh evmh →
      (RDrev ctorCode g s0 ∧
        ExecForLoop config { contract := contract, locals := L } evmh ctorCond ctorPost ctorLoopBody
          .reverted) ∨
      (∃ (σf : AccountMap) (evmf : EVM.State) (Lf : Store) (mem' rdata' : ByteArray)
          (aw' : UInt256) (k' C' : ℕ) (x : UInt256),
        SourceState s0 I σf evmf ∧
        RD ctorCode I g s0 (UInt256.ofNat 69) [UInt256.ofNat 31, x] mem' aw' rdata' σf k' C' ∧
        ExecForLoop config { contract := contract, locals := L } evmh ctorCond ctorPost ctorLoopBody
          (.ok { contract := contract, locals := Lf } evmf)) := by
  intro n
  induction n with
  | zero =>
    intro h hn σh evmh mem rdata aw L hh hz hat hs
    obtain rfl : h = 31 := by omega
    rcases hat with ⟨hlt, -⟩ | ⟨-, k, C, x, rd⟩
    · omega
    refine Or.inr ⟨σh, evmh, L, mem, rdata, aw, k, C, x, hs, rd, ExecForLoop.falseDone ?_⟩
    rw [evalHeightLt hh]
    rfl
  | succ m ih =>
    intro h hn σh evmh mem rdata aw L hh hz hat hs
    have hlt : h < 31 := by omega
    rcases hat with ⟨-, k, C, rd⟩ | ⟨hge, -⟩
    swap
    · omega
    have hcond : evalExpr? config { contract := contract, locals := L } evmh ctorCond =
        .ok (.bool true) := by
      have hlt' : Int.ofNat h < 31 := Int.ofNat_lt.mpr hlt
      rw [evalHeightLt hh, decide_eq_true hlt']
    rd_step rd
    obtain ⟨evm', σ', z, out, aw', k2, C2, hcall, hs', rd36, hob⟩ :=
      staticCallBridge rd hs (by native_decide) (by simp)
    u256_lits at hcall
    rw [pairWords_read _ _ _ 0 32 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hcall
    -- the Stele body up to the call
    have hcur := zeroHash_read (L := L) (evm := evmh) (i := h) (by omega) (evalVarF hh) hz
    rw [hs.storageRead] at hcur
    have hcurVar : evalExpr? config { contract := contract, locals := loopL1 L σh I h } evmh
        (.var "cur") =
        .ok (.int (Int.ofNat (σh.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD ((UInt256.ofNat 33) + UInt256.ofNat h) (⟨0⟩ : UInt256))).toNat)) :=
      evalVarF (store_get_self _ _ _)
    -- the EVM after the call: its checks, the store, and the loop test at the end of the iteration
    have hnext : (UInt256.ofNat 1 + UInt256.ofNat h).toNat = h + 1 := by
      rw [succ_word hlt, ulit_toNat' (h + 1) (lt_of_lt_of_le (by omega : h + 1 < 32) (by decide))]
    have key : (¬ (z = true ∧ 32 ≤ out.size) → RDrev ctorCode g s0) ∧
        (z = true → 32 ≤ out.size → ∃ memN awN, CtorAt s0 I g (h + 1) memN awN out
          (sstoreAccountMap I.codeOwner σ' (UInt256.ofNat 33 + UInt256.ofNat (h + 1))
            (calldataWord out 0))) := by
      by_cases hlast : h + 1 < 31
      · have hjump : UInt256.lt (UInt256.ofNat 1 + UInt256.ofNat h) (UInt256.ofNat 31) ≠
            UInt256.ofNat 0 := by
          rw [ult_one (by rw [hnext]; exact hlast)]; decide
        rd_checked rd36 z out as hrev hout to 12
        · exact ⟨fun _ => hrev, fun hz hl => absurd ⟨hz, hl⟩ hout⟩
        u256_lits at rd36
        rw [callOutput_load32 _ out hob hout
          (le_trans (by decide) (pairWords_size _ _ _ 0 32 rfl (by decide))), succ_word hlt] at rd36
        exact ⟨fun hbad => absurd ⟨rfl, hout⟩ hbad, fun _ _ => ⟨_, _, Or.inl ⟨hlast, _, _, rd36⟩⟩⟩
      · have hstay : UInt256.lt (UInt256.ofNat 1 + UInt256.ofNat h) (UInt256.ofNat 31) =
            UInt256.ofNat 0 :=
          ult_zero (by rw [hnext, ulit_toNat' 31 (by decide)]; omega)
        rd_checked rd36 z out as hrev hout to 69
        · exact ⟨fun _ => hrev, fun hz hl => absurd ⟨hz, hl⟩ hout⟩
        u256_lits at rd36
        rw [callOutput_load32 _ out hob hout
          (le_trans (by decide) (pairWords_size _ _ _ 0 32 rfl (by decide))), succ_word hlt] at rd36
        exact ⟨fun hbad => absurd ⟨rfl, hout⟩ hbad,
          fun _ _ => ⟨_, _, Or.inr ⟨by omega, _, _, _, rd36⟩⟩⟩
    by_cases hout : z = true ∧ 32 ≤ out.size
    swap
    · exact Or.inl ⟨key.1 hout, ExecForLoop.bodyRevert hcond (ExecBlock.consNormal (ExecStmt.letDecl hcur)
        (ExecBlock.consRevert (shaPairCall_revert rfl hcurVar hcurVar hcall hout)))⟩
    obtain ⟨rfl, hout⟩ := hout
    obtain ⟨memN, awN, hatN⟩ := key.2 rfl hout
    -- the Stele body after the call
    have hcall2 := shaPairCall_ok (caller := { contract := contract, locals := loopL1 L σh I h })
      rfl (ret := "next") hcurVar hcurVar hcall hout
    have hh2 : (loopL2 L σh I h out).get? "height" = some (.int (Int.ofNat h)) := by
      store_get; exact hh
    have hz2 : (loopL2 L σh I h out).get? "zero_hashes" = none := by
      store_get; exact hz
    have hassign := zeroHash_write (evm := evm') (i := h + 1) (by omega) (evalInc hh2) hz2
      (calldataWord out 0)
    rw [hs'.env] at hassign
    have hsN := hs'.storageWrite (⟨33⟩ + UInt256.ofNat (h + 1)) (calldataWord out 0)
    have hstore := ExecStmt.assign (hperm := Or.inr (by rw [hs'.env]; exact hperm))
      (evalVarF (store_get_self _ _ _)) hassign
    have hpost := ExecStmt.assign (cfg := config) (hperm := Or.inl rfl)
      (evalInc (evm := Stele.EVM.storageStore evm' I.codeOwner (⟨33⟩ + UInt256.ofNat (h + 1))
        (calldataWord out 0)) hh2) (assignLocalF (old := .int (Int.ofNat h)) hh2)
    have hh3 : (loopL3 L σh I h out).get? "height" = some (.int (Int.ofNat (h + 1))) :=
      store_get_self _ _ _
    have hz3 : (loopL3 L σh I h out).get? "zero_hashes" = none := by
      store_get; exact hz
    have hbody : ExecBlock config { contract := contract, locals := L } evmh ctorLoopBody
        (.ok { contract := contract, locals := loopL2 L σh I h out }
          (Stele.EVM.storageStore evm' I.codeOwner (⟨33⟩ + UInt256.ofNat (h + 1))
            (calldataWord out 0))) :=
      ExecBlock.consNormal (ExecStmt.letDecl hcur) <|
        ExecBlock.consNormal hcall2 <| ExecBlock.consNormal hstore ExecBlock.nil
    rcases ih (h + 1) (by omega) hh3 hz3 hatN hsN with
      ⟨hrev, hloop⟩ | ⟨σf, evmf, Lf, memF, rdataF, awF, kF, CF, x, hsf, rd69, hloop⟩
    · exact Or.inl ⟨hrev, ExecForLoop.iterate hcond hbody (ExecBlock.consNormal hpost ExecBlock.nil) hloop⟩
    · exact Or.inr ⟨σf, evmf, Lf, memF, rdataF, awF, kF, CF, x, hsf, rd69,
        ExecForLoop.iterate hcond hbody (ExecBlock.consNormal hpost ExecBlock.nil) hloop⟩

end FeProofs.Deposit
