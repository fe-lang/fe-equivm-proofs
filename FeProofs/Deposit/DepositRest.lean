import FeProofs.Deposit.DepositCompose
import FeProofs.Deposit.DepositHash
import FeProofs.Deposit.DepositEventStele
import FeProofs.Deposit.DepositLoop
import FeProofs.Deposit.DepositRoot
import FeProofs.Deposit.DepositMemory

/-!
# FeDeposit `deposit`: the rest of the body from pc 650

Chains the segments after the front: the three pubkey/signature hashing calls (statements 9–11,
pc 650 → 874, `Calls123`), the remaining hashing (`depositHash_874`, statements 12–17), the event
(`depositEventSegment`, statements 18–22) and the count update with the insertion loop
(`depositTail`), discharging `depositBody_of_rest`'s obligation.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-- The locals after the three hashing calls of statements 9–11. -/
abbrev rLocals11 (cd : ByteArray) (s0 : State) (o1 o2 o3 : ByteArray) : Store :=
  (((pLocals cd s0).insert "pubkey_root" (shaDigest o1)).insert "signature_left"
    (shaDigest o2)).insert "signature_right" (shaDigest o3)

/-- The deposit amount in gwei, as the bytecode computes it. -/
abbrev rGwei (I : ExecutionEnv) : UInt256 := UInt256.div I.weiValue (UInt256.ofNat 1000000000)

/-- The decoder's tail of the stack at pc 874. -/
abbrev rTail (I : ExecutionEnv) : List UInt256 :=
  [rAlloc I (hPos I 2), rAlloc I (hPos I 1), rFp ByteArray.empty, rFp (hMem2 I),
   rAlloc I (hPos I 0), rFp (hMem1 I)]

/-- Statements 9–11 from pc 650: the EVM reverts with the block, or reaches pc 874 with the three
    digests while the block has run into statement 12. -/
def Calls123 (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : UInt256) : Prop :=
  ∀ {aw : UInt256} {k C : Nat}, hOk I → dArgsOk I.calldata →
    pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) →
    RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 650) (fStack I) (hMem3 I) aw ByteArray.empty σ k C →
    (RDrev feDepositBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) .reverted) ∨
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o1 o2 o3 mem : ByteArray) (aw' : UInt256)
        (k' C' : Nat),
      RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (UInt256.ofNat 874)
        (calldataWord o2 0 :: UInt256.ofNat 640 :: UInt256.ofNat 608 :: u64ChunkWord (rGwei I) ::
          calldataWord o1 0 :: calldataWord (dPayload I.calldata (dWord I.calldata 32)) 0 :: rTail I)
        mem aw' o3 σ' k' C' ∧
      memLoad (UInt256.ofNat 608) mem = calldataWord o3 0 ∧
      memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 672 ∧ 672 ≤ mem.size ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      ∀ res, ExecBlock config
          (pFrame (rLocals11 I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3)) evm'
          (depositTransition.body.drop 11) res →
        ExecBlock config (pFrame (pLocals I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) (depositTransition.body.drop 8) res)

/-- The decoder's allocation size for an argument of (small) length `n`. -/
theorem rAlloc_small {I : ExecutionEnv} (hok : hOk I) (i n : Nat) (hi : i ≤ 2)
    (hl : dLen I.calldata i = n) (hn : n ≤ 4294967232) : (rAlloc I (hPos I i)).toNat < 4294967296 := by
  have h63 : (UInt256.ofNat 63).toNat = 63 := by decide
  have hnn : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by unfold UInt256.size; omega)
  rw [rAlloc, mLen_eq hok i hi n hl (by unfold UInt256.size; omega),
    show UInt256.lnot (UInt256.ofNat 31) = UInt256.lnot ⟨31⟩ from rfl, uland_toNat, lnot31_toNat,
    uadd_toNat, h63, hnn, Nat.mod_eq_of_lt (by unfold UInt256.size; omega), Nat.and_comm,
    nat_land_mask _ (by omega)]
  omega

theorem depositRest {σ σ₀ A I} {g : UInt256} (hcalls : Calls123 σ σ₀ A I g)
    (hok : hOk I) (hargs : dArgsOk I.calldata)
    (hp : pOk I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I)) {aw : UInt256} {k C : Nat}
    (rd : RD feDepositBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 650) (fStack I) (hMem3 I) aw ByteArray.empty σ k C) :
    RestOutcome σ σ₀ A I g := by
  rw [RestOutcome_eq]
  rcases hcalls hok hargs hp rd with ⟨hrev, hblk⟩ |
      ⟨σ1, evm1, o1, o2, o3, mem1, aw1, k1, C1, rd874, h608, h64, hsz, hs1, hk1⟩
  · exact OutAt.rev hrev hblk
  have hdiv : (rGwei I).toNat = I.weiValue.toNat / 1000000000 := udiv_toNat _ _
  have ham : (rLocals11 I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3).get?
      "amount" = some (.int (Int.ofNat (rGwei I).toNat)) := by
    rw [get_ins_ne (by decide), get_ins_ne (by decide), get_ins_ne (by decide), store_get_self, hdiv]
    show some (Value.int (Int.ofNat I.weiValue.toNat / 1000000000)) = _
    simp only [Option.some.injEq, Value.int.injEq, Int.ofNat_eq_natCast]
    omega
  have hwcsz : (dPayload I.calldata (dWord I.calldata 32)).size = 32 :=
    (dPayload_size _ _ hargs.2.2.1.2).trans hp.2.1
  rcases depositHash_874 (L := rLocals11 I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3)
      (by simp) rd874 hs1 h608 h64 hsz
      (by rw [get_ins_ne (by decide)]; exact store_get_self _ _ _)
      (store_get_self _ _ _)
      (by rw [get_ins_ne (by decide), get_ins_ne (by decide)]; exact store_get_self _ _ _)
      (by repeat rw [get_ins_ne (by decide)]
          exact store_get_self _ _ _)
      hwcsz ham with
    ⟨σ2, evm2, o4, o5, o6, o7, mem2, rdata2, aw2, k2, C2, rd1026, hnode, hs2, hk2⟩ | ⟨hrev, hblk⟩
  swap
  · exact OutAt.rev hrev (hk1 _ hblk)
  have hE : EventLocals (hL17 (rLocals11 I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3)
      o4 (dPayload I.calldata (dWord I.calldata 32)) (rGwei I) o5 o6 o7)
      (memLoad (UInt256.ofNat 672) mem2) (rGwei I)
      (.bytes (dPayload I.calldata (dWord I.calldata 0)))
      (.bytes (dPayload I.calldata (dWord I.calldata 32)))
      (.bytes (dPayload I.calldata (dWord I.calldata 64))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnode]; exact store_get_self _ _ _
    · repeat rw [get_ins_ne (by decide)]
      exact store_get_self _ _ _
    all_goals repeat rw [get_ins_ne (by decide)]
    all_goals first | exact store_get_self _ _ _ | exact store_get_empty _
  have hroot := evalRootCast (cfg := config) (evm := evm2)
    (stele := pFrame (hL17 (rLocals11 I.calldata (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3)
      o4 (dPayload I.calldata (dWord I.calldata 32)) (rGwei I) o5 o6 o7)) I.calldata hargs.1 (by
        show Std.HashMap.get? _ "deposit_data_root" = _
        repeat rw [get_ins_ne (by decide)]
        exact store_get_self _ _ _)
  rcases depositEventSegment (R := []) (by simp)
      (rAlloc_small hok 2 96 (by decide) hp.2.2.1 (by decide))
      (rAlloc_small hok 1 32 (by decide) hp.2.1 (by decide))
      (rAlloc_small hok 0 48 (by decide) hp.1 (by decide)) hE hroot hs2 rd1026 with
    ⟨hrev, hblk⟩ | ⟨hst, hblk⟩ | ⟨hperm, mem3, aw3, k3, C3, rd1592, hlt, hk3⟩
  · exact OutAt.rev hrev (hk1 _ (hk2 _ hblk))
  · exact OutAt.static hst (hk1 _ (hk2 _ hblk))
  have hd22 : depositTransition.body.drop 22 = depositTailStmts := depositTailStmts_eq
  rw [hd22] at hk3
  rcases depositTail (L := eventExitStore (hL17 (rLocals11 I.calldata
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) o1 o2 o3) o4
        (dPayload I.calldata (dWord I.calldata 32)) (rGwei I) o5 o6 o7) (rGwei I) (eventCount σ2 I))
      hperm (by simp) rd1592 hs2 rfl hlt
      (by rw [get_ins_ne (by decide), get_ins_ne (by decide)]; exact hE.node)
      (by rw [get_ins_ne (by decide), get_ins_ne (by decide)]; exact hE.branch)
      (by rw [get_ins_ne (by decide), get_ins_ne (by decide)]; exact hE.count) with
    ⟨σf, frf, evmf, hret, hblk, hacc⟩ | ⟨hrev, hblk⟩
  · exact Or.inl ⟨σf, frf, evmf, hret, hk1 _ (hk2 _ (hk3 _ hblk)), hacc.symm⟩
  · exact OutAt.rev hrev (hk1 _ (hk2 _ (hk3 _ hblk)))

/-- `deposit` refines its spec, given statements 9–11 from pc 650. -/
theorem depositBody_of_calls123 {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feDepositBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 64) (hsel : selIs I (feDepositSelBytes 1))
    (hcalls : Calls123 σ σ₀ A I g) :
    runtimeRefinementFor config contract σ σ₀ g A I :=
  depositBody_of_rest hcode hsize hsmall hsel
    fun hok hargs hp _ _ _ rd => depositRest hcalls hok hargs hp rd

end FeProofs.Deposit
