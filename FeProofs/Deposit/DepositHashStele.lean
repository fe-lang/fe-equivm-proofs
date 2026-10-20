import FeProofs.Deposit.Sha256
import FeProofs.Deposit.Le64

/-!
# FeDeposit `deposit()` hashing — Stele side

The deposit-data root is built from seven `sha256` calls over 64-byte payloads.  This file
evaluates the spec's payload expressions on the decoded `bytes` arguments, packages the raw
`sha256_64` internal call (the `sha256_pair` version is in `Sha256.lean`), and evaluates the
`u64_chunk(amount)` call as the byte-swapped word of `Le64.lean`.  Nothing here depends on the
bytecode's memory layout.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

set_option maxRecDepth 2000000

/-! ## Byte arrays -/

theorem replicate_toByteArray (n : ℕ) : (List.replicate n (0 : UInt8)).toByteArray = ByteArray.zeroes n := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.data_toByteArray, byteArray_zeroes_toList]

theorem packed_bytes_zeros (b : ByteArray) (n : ℕ) :
    (⟨(b.toList ++ List.replicate n 0).toArray⟩ : ByteArray) = b ++ ByteArray.zeroes n := by
  rw [mk_toArray_eq, list_toByteArray_append, byteArray_toList_toByteArray, replicate_toByteArray]

/-! ## Payload expressions of the deposit body -/

theorem evalFixedLit {cfg : Config} {stele : Frame} {evm : EVM.State} (n : Fin 32) (bs : List UInt8) :
    evalExpr? cfg stele evm (.fixedBytesLit n bs) = .ok (.fixedBytes n bs) := by
  rw [evalExpr?]; rfl

theorem evalSlice {cfg : Config} {stele : Frame} {evm : EVM.State} {x : Ident} {b : ByteArray}
    {s e : ℕ} (hx : stele.locals.get? x = some (.bytes b)) (hse : s ≤ e) (he : e ≤ b.size) :
    evalExpr? cfg stele evm (.bytesSlice (.var x) (.intLit (Int.ofNat s)) (.intLit (Int.ofNat e))) =
      .ok (.bytes (b.extract s e)) := by
  have hslice : sliceBytes? b (Int.ofNat s) (Int.ofNat e) = .ok (.bytes (b.extract s e)) := by
    simp only [sliceBytes?]
    rw [if_neg (by simp), if_neg (by simp; omega)]
    rfl
  rw [evalExpr?]
  simp only [evalVarF hx, evalLit, EvalResult.bind, bind, hslice]

/-- `abi.encodePacked(bytes(pubkey), bytes16(0))`. -/
theorem evalPubkeyPayload {cfg : Config} {stele : Frame} {evm : EVM.State} {pk : ByteArray}
    (hpk : stele.locals.get? "pubkey" = some (.bytes pk)) :
    evalExpr? cfg stele evm
      (.abiEncodePacked [(.bytes, .var "pubkey"),
        (.elem (.bytes 15), .fixedBytesLit 15 (List.replicate 16 0))]) =
      .ok (.bytes (pk ++ ByteArray.zeroes 16)) := by
  have henc : encodePackedValue? (.elem (.bytes 15)) (.fixedBytes 15 (List.replicate 16 0)) =
      some (List.replicate 16 0) := by decide
  have hpack := evalPackedArgs_cons (ty := .bytes) (evalVarF hpk) rfl
    (evalPackedArgs_single (evalFixedLit (cfg := cfg) (stele := stele) (evm := evm) 15
      (List.replicate 16 0)) henc)
  rw [evalExpr?]
  simp only [hpack, EvalResult.bind, bind, pure]
  rw [packed_bytes_zeros]

/-- `signature[0:64]`. -/
theorem evalSigLeftPayload {cfg : Config} {stele : Frame} {evm : EVM.State} {sig : ByteArray}
    (hsig : stele.locals.get? "signature" = some (.bytes sig)) (hsz : sig.size = 96) :
    evalExpr? cfg stele evm (.bytesSlice (.var "signature") (.intLit 0) (.intLit 64)) =
      .ok (.bytes (sig.extract 0 64)) :=
  evalSlice (s := 0) (e := 64) hsig (by decide) (by omega)

/-- `abi.encodePacked(bytes(signature[64:96]), bytes32(0))`. -/
theorem evalSigRightPayload {cfg : Config} {stele : Frame} {evm : EVM.State} {sig : ByteArray}
    (hsig : stele.locals.get? "signature" = some (.bytes sig)) (hsz : sig.size = 96) :
    evalExpr? cfg stele evm
      (.abiEncodePacked [(.bytes, .bytesSlice (.var "signature") (.intLit 64) (.intLit 96)),
        (.elem (.bytes 31), .fixedBytesLit 31 (List.replicate 32 0))]) =
      .ok (.bytes (sig.extract 64 96 ++ ByteArray.zeroes 32)) := by
  have henc : encodePackedValue? (.elem (.bytes 31)) (.fixedBytes 31 (List.replicate 32 0)) =
      some (List.replicate 32 0) := by decide
  have hpack : evalPackedArgs? cfg stele evm
      [(.bytes, .bytesSlice (.var "signature") (.intLit 64) (.intLit 96)),
        (.elem (.bytes 31), .fixedBytesLit 31 (List.replicate 32 0))] =
      .ok ((sig.extract 64 96).toList ++ List.replicate 32 0) := evalPackedArgs_cons (ty := .bytes)
    (evalSlice (cfg := cfg) (evm := evm) (s := 64) (e := 96) hsig (by decide) (by omega)) rfl
    (evalPackedArgs_single (evalFixedLit (cfg := cfg) (stele := stele) (evm := evm) 31
      (List.replicate 32 0)) henc)
  rw [evalExpr?]
  simp only [hpack, EvalResult.bind, bind, pure]
  rw [packed_bytes_zeros]

/-- `abi.decode(withdrawal_credentials, (uint256))` of a one-word `bytes`. -/
theorem evalCredentials {stele : Frame} {evm : EVM.State} {wc : ByteArray}
    (hwc : stele.locals.get? "withdrawal_credentials" = some (.bytes wc)) (hsz : wc.size = 32) :
    evalExpr? config stele evm
      (.abiDecode (.elem (.int (.uint ⟨256, by decide⟩))) (.var "withdrawal_credentials")) =
      .ok (.int (Int.ofNat (calldataWord wc 0).toNat)) := by
  have hdv : config.externalABI.decodeValue? (.elem (.int (.uint ⟨256, by decide⟩))) wc =
      some (.int (Int.ofNat (calldataWord wc 0).toNat)) := by
    have h := decodeReturnUint_extract (out := wc) (start := 0) (finish := 32) (by decide)
      (by omega) (by norm_num)
    rw [byteArray_extract_of_size wc 32 hsz] at h
    exact h
  rw [evalExpr?]
  simp only [evalVarF hwc, EvalResult.bind, bind, hdv, pure]

/-! ## The internal calls -/

/-- **`sha256_64(e)` over a successful call** binds the first returned word. -/
theorem sha64Call_ok {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {e : Expr} {ret : Ident} {payload out : ByteArray}
    (he : evalExpr? config caller evm e = .ok (.bytes payload))
    (hcall : callViaEVM evm (EVM.address precompile2) 0 payload (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecStmt config caller evm (.internalCall "sha256_64" [e] ret)
      (.ok { caller with locals := caller.locals.insert ret (shaDigest out) } evm') :=
  internalCallFunctionReturn (retVar := ret) (argVals := [.bytes payload])
    (evalExprs?_singleton he) (by rw [hc]; exact sha64Fn_lookup) rfl (sha64Body_ok hcall hout)

/-- **`sha256_64(e)` reverts** when the call fails or returns less than a word. -/
theorem sha64Call_revert {caller : Frame} (hc : caller.contract = contract) {evm evm' : EVM.State}
    {e : Expr} {ret : Ident} {payload out : ByteArray} {z : Bool}
    (he : evalExpr? config caller evm e = .ok (.bytes payload))
    (hcall : callViaEVM evm (EVM.address precompile2) 0 payload (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecStmt config caller evm (.internalCall "sha256_64" [e] ret) .reverted :=
  internalCallFunctionRevert (argVals := [.bytes payload]) (evalExprs?_singleton he)
    (by rw [hc]; exact sha64Fn_lookup) rfl (sha64Body_revert hcall hbad)

/-- **`u64_chunk(amount)`** binds the SSZ chunk of the amount word. -/
theorem u64ChunkCall {caller : Frame} (hc : caller.contract = contract) {evm : EVM.State}
    {m : UInt256} (ha : caller.locals.get? "amount" = some (.int (Int.ofNat m.toNat))) :
    ExecStmt config caller evm (.internalCall "u64_chunk" [.var "amount"] "amount_chunk")
      (.ok { caller with locals := (caller.locals.insert "amount_chunk"
        (.int (Int.ofNat (u64ChunkWord m).toNat))) } evm) := by
  obtain ⟨F, hbody⟩ := u64ChunkBody config caller evm m
  exact internalCallFunctionReturn (evalExprs?_singleton (evalVarF ha)) (by rw [hc]; rfl) rfl hbody

end FeProofs.Deposit
