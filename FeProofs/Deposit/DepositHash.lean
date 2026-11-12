import FeProofs.Deposit.DepositHashStele
import FeProofs.Deposit.DepositLayout
import FeProofs.Deposit.DepositPrefix
import FeProofs.Deposit.CtorLoop

/-!
# FeDeposit `deposit()` hashing, calls 4–7 (pc 855 → 1025)

From the second signature hash on, every digest is a `sha256_pair` over a 64-byte scratch pair:
the signature pair at `0x140` (call 4: `left ‖ right`) and the merkleization pair at `0x180`
(calls 5–7).  Each call writes its digest over the pair's first word, which the next block reads.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## The segment -/

abbrev hL12 (L : Store) (o4 : ByteArray) : Store := L.insert "signature_root" (shaDigest o4)
abbrev hL13 (L : Store) (o4 wc : ByteArray) : Store :=
  (hL12 L o4).insert "credentials" (.int (Int.ofNat (calldataWord wc 0).toNat))
abbrev hL14 (L : Store) (o4 wc : ByteArray) (m : UInt256) : Store :=
  (hL13 L o4 wc).insert "amount_chunk" (.int (Int.ofNat (u64ChunkWord m).toNat))
abbrev hL15 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 : ByteArray) : Store :=
  (hL14 L o4 wc m).insert "left" (shaDigest o5)
abbrev hL16 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 o6 : ByteArray) : Store :=
  (hL15 L o4 wc m o5).insert "right" (shaDigest o6)
abbrev hL17 (L : Store) (o4 wc : ByteArray) (m : UInt256) (o5 o6 o7 : ByteArray) : Store :=
  (hL16 L o4 wc m o5 o6).insert "node" (shaDigest o7)

theorem depositBody_drop11 :
    depositTransition.body.drop 11 =
      .internalCall "sha256_pair" [.var "signature_left", .var "signature_right"] "signature_root" ::
      .letDecl "credentials" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.abiDecode (.elem (.int (.uint ⟨256, by decide⟩))) (.var "withdrawal_credentials")) ::
      .internalCall "u64_chunk" [.var "amount"] "amount_chunk" ::
      .internalCall "sha256_pair" [.var "pubkey_root", .var "credentials"] "left" ::
      .internalCall "sha256_pair" [.var "amount_chunk", .var "signature_root"] "right" ::
      .internalCall "sha256_pair" [.var "left", .var "right"] "node" ::
      depositTransition.body.drop 17 := rfl

/-- A returned word copied over the first word of a scratch pair reads back. -/
theorem pairOut_load (mem out : ByteArray) (a b : UInt256) (s t : ℕ) (ht : t = s + 32)
    (hs : s + 32 < 2 ^ 32) (hb : out.size < UInt256.size) (hsz : 32 ≤ out.size) :
    memLoad (UInt256.ofNat s)
      (callOutputMem (b.toByteArray.write 0 (a.toByteArray.write 0 mem s 32) t 32) out
        (UInt256.ofNat s) (UInt256.ofNat 32)) = calldataWord out 0 := by
  have hsn : (UInt256.ofNat s).toNat = s := ulit_toNat' s (by
    have : (2 : ℕ) ^ 32 ≤ UInt256.size := by decide
    omega)
  exact callOutput_loadAt _ out (UInt256.ofNat s) hb hsz (by
    rw [hsn]; have := pairWords_size mem a b s t ht hs; omega)

/-- **Calls 4–7.**  From the signature pair at `0x140` (holding `signature_right` at its first
    word, with `signature_left` on the stack) to the node at pc 1025: the EVM either reverts, or
    reaches pc 1025 with the node at `0x180` while the spec has run statements 11–16. -/
theorem depositHash_855 {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {evm : EVM.State} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {L : Store} {o1 o2 o3 wc : ByteArray} {m : UInt256} (hR : R.length ≤ 1000)
    (rd : RD feDepositBytecode I g s0 (UInt256.ofNat 855)
      (calldataWord o2 0 :: u64ChunkWord m :: calldataWord o1 0 :: calldataWord wc 0 :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hright : memLoad (UInt256.ofNat 320) mem = calldataWord o3 0)
    (hsl : L.get? "signature_left" = some (shaDigest o2))
    (hsr : L.get? "signature_right" = some (shaDigest o3))
    (hpk : L.get? "pubkey_root" = some (shaDigest o1))
    (hwc : L.get? "withdrawal_credentials" = some (.bytes wc)) (hwcsz : wc.size = 32)
    (ham : L.get? "amount" = some (.int (Int.ofNat m.toNat))) :
    (∃ (σ' : AccountMap) (evm' : EVM.State) (o4 o5 o6 o7 mem' rdata' : ByteArray) (aw' : UInt256)
        (k' C' : ℕ),
      RD feDepositBytecode I g s0 (UInt256.ofNat 1025) (u64ChunkWord m :: R)
        mem' aw' rdata' σ' k' C' ∧
      memLoad (UInt256.ofNat 384) mem' = calldataWord o7 0 ∧
      SourceState s0 I σ' evm' ∧
      ∀ res, ExecBlock config (pFrame (hL17 L o4 wc m o5 o6 o7)) evm' (depositTransition.body.drop 17) res →
        ExecBlock config (pFrame L) evm (depositTransition.body.drop 11) res) ∨
    (RDrev feDepositBytecode g s0 ∧
      ExecBlock config (pFrame L) evm (depositTransition.body.drop 11) .reverted) := by
  rw [depositBody_drop11]
  -- call 4: signature_root = sha256(signature_left ‖ signature_right) over the pair at 0x140
  have r880 := feDepositBlocks.feDeposit_block_855 (by simp; omega) rd
  simp only [feDepositBlocks.feDeposit_block_855_stack, feDepositBlocks.feDeposit_block_855_memory,
    hright] at r880
  u256_lits at r880
  obtain ⟨ev4, σ4, z4, o4, aw4, k4, C4, hc4, hs4, r881, hb4⟩ :=
    staticCallBridge r880 hs (by native_decide) (by simp; omega)
  u256_lits at hc4
  rw [pairWords_read _ _ _ 320 352 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hc4
  rd_checked r881 z4 o4 as hrev hout4 to 897
  · exact Or.inr ⟨hrev, ExecBlock.consRevert (shaPairCall_revert (caller := pFrame L) rfl (ret := "signature_root")
      (evalVarF hsl) (evalVarF hsr) hc4 hout4)⟩
  have hs11 := shaPairCall_ok (caller := pFrame L) rfl (ret := "signature_root") (evalVarF hsl)
    (evalVarF hsr) hc4 hout4
  have hs12 := ExecStmt.letDecl (cfg := config) (stele := pFrame (hL12 L o4)) (evm := ev4)
    (name := "credentials") (ty := some (.elem (.int (.uint ⟨256, by decide⟩))))
    (evalCredentials (by store_get; exact hwc) hwcsz)
  have hs13 := u64ChunkCall (caller := pFrame (hL13 L o4 wc)) (evm := ev4) rfl
    (by store_get; exact ham)
  -- call 5: left = sha256(pubkey_root ‖ credentials) over the merkleization pair at 0x180
  have r923 := feDepositBlocks.feDeposit_block_897 (by simp; omega) r881
  simp only [feDepositBlocks.feDeposit_block_897_stack, feDepositBlocks.feDeposit_block_897_memory,
    pairOut_load _ o4 _ _ 320 352 rfl (by decide) hb4 hout4] at r923
  u256_lits at r923
  obtain ⟨ev5, σ5, z5, o5, aw5, k5, C5, hc5, hs5, r924, hb5⟩ :=
    staticCallBridge r923 hs4 (by native_decide) (by simp; omega)
  u256_lits at hc5
  rw [pairWords_read _ _ _ 384 416 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hc5
  have hs14rev := fun (hbad : ¬ (z5 = true ∧ 32 ≤ o5.size)) =>
    shaPairCall_revert (caller := pFrame (hL14 L o4 wc m)) (evm := ev4) rfl (ret := "left")
      (ea := .var "pubkey_root") (eb := .var "credentials") (a := calldataWord o1 0) (b := calldataWord wc 0)
      (evalVarF (by store_get; exact hpk))
      (evalVarF (by store_get)) hc5 hbad
  rd_checked r924 z5 o5 as hrev hout5 to 940
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consRevert (hs14rev hout5)⟩
  have hs14 := shaPairCall_ok (caller := pFrame (hL14 L o4 wc m)) (evm := ev4) rfl (ret := "left")
    (ea := .var "pubkey_root") (eb := .var "credentials") (a := calldataWord o1 0) (b := calldataWord wc 0)
    (evalVarF (by store_get; exact hpk))
    (evalVarF (by store_get)) hc5 hout5
  -- call 6: right = sha256(amount_chunk ‖ signature_root)
  have r966 := feDepositBlocks.feDeposit_block_940 (by simp; omega) r924
  simp only [feDepositBlocks.feDeposit_block_940_stack, feDepositBlocks.feDeposit_block_940_memory,
    pairOut_load _ o5 _ _ 384 416 rfl (by decide) hb5 hout5] at r966
  u256_lits at r966
  obtain ⟨ev6, σ6, z6, o6, aw6, k6, C6, hc6, hs6, r967, hb6⟩ :=
    staticCallBridge r966 hs5 (by native_decide) (by simp; omega)
  u256_lits at hc6
  rw [pairWords_read _ _ _ 384 416 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hc6
  have hs15rev := fun (hbad : ¬ (z6 = true ∧ 32 ≤ o6.size)) =>
    shaPairCall_revert (caller := pFrame (hL15 L o4 wc m o5)) (evm := ev5) rfl (ret := "right")
      (ea := .var "amount_chunk") (eb := .var "signature_root") (a := u64ChunkWord m) (b := calldataWord o4 0)
      (evalVarF (by store_get))
      (evalVarF (by store_get)) hc6 hbad
  rd_checked r967 z6 o6 as hrev hout6 to 983
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consRevert (hs15rev hout6)⟩
  have hs15 := shaPairCall_ok (caller := pFrame (hL15 L o4 wc m o5)) (evm := ev5) rfl (ret := "right")
    (ea := .var "amount_chunk") (eb := .var "signature_root") (a := u64ChunkWord m) (b := calldataWord o4 0)
    (evalVarF (by store_get))
    (evalVarF (by store_get)) hc6 hout6
  -- call 7: node = sha256(left ‖ right)
  have r1008 := feDepositBlocks.feDeposit_block_983 (by simp; omega) r967
  simp only [feDepositBlocks.feDeposit_block_983_stack, feDepositBlocks.feDeposit_block_983_memory,
    pairOut_load _ o6 _ _ 384 416 rfl (by decide) hb6 hout6] at r1008
  u256_lits at r1008
  obtain ⟨ev7, σ7, z7, o7, aw7, k7, C7, hc7, hs7, r1009, hb7⟩ :=
    staticCallBridge r1008 hs6 (by native_decide) (by simp; omega)
  u256_lits at hc7
  rw [pairWords_read _ _ _ 384 416 64 rfl rfl (by decide), ← pairPayload_eq, ← precompile2_eq] at hc7
  have hs16rev := fun (hbad : ¬ (z7 = true ∧ 32 ≤ o7.size)) =>
    shaPairCall_revert (caller := pFrame (hL16 L o4 wc m o5 o6)) (evm := ev6) rfl (ret := "node")
      (ea := .var "left") (eb := .var "right") (a := calldataWord o5 0) (b := calldataWord o6 0)
      (evalVarF (by store_get))
      (evalVarF (store_get_self _ _ _)) hc7 hbad
  rd_checked r1009 z7 o7 as hrev hout7 to 1025
  · exact Or.inr ⟨hrev, ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consNormal hs15 <|
      ExecBlock.consRevert (hs16rev hout7)⟩
  have hs16 := shaPairCall_ok (caller := pFrame (hL16 L o4 wc m o5 o6)) (evm := ev6) rfl (ret := "node")
    (ea := .var "left") (eb := .var "right") (a := calldataWord o5 0) (b := calldataWord o6 0)
    (evalVarF (by store_get))
    (evalVarF (store_get_self _ _ _)) hc7 hout7
  exact Or.inl ⟨σ7, ev7, o4, o5, o6, o7, _, _, _, _, _, r1009,
    pairOut_load _ o7 _ _ 384 416 rfl (by decide) hb7 hout7, hs7, fun res h =>
    ExecBlock.consNormal hs11 <| ExecBlock.consNormal hs12 <| ExecBlock.consNormal hs13 <|
      ExecBlock.consNormal hs14 <| ExecBlock.consNormal hs15 <| ExecBlock.consNormal hs16 h⟩

end FeProofs.Deposit
