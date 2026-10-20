import FeProofs.Deposit.Common
import Reasoning.SteleArithmetic

/-!
# FeDeposit: the SSZ `uint64` chunk and its eight-byte serialization

The spec's `u64_chunk` repeats Fe's three byte-swap passes with width-qualified `uint256` bit
operations, and the bytecode performs the same passes on words.  The value lemmas here pair each
Stele bit operation on in-range integers with the EVM word operation, so the two computations agree
operation by operation; no byte-swap identity is needed.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.Deposit

abbrev u256T : IntType := .uint ⟨256, by decide⟩
abbrev u64T : IntType := .uint ⟨64, by decide⟩

/-! ## Word operations as `Nat` operations -/

theorem ushlN_toNat (a : UInt256) (s : ℕ) (hs : s < 256) :
    (UInt256.shiftLeft a (UInt256.ofNat s)).toNat = a.toNat * 2 ^ s % 2 ^ 256 := by
  have hsv : (UInt256.ofNat s).toNat = s := ulit_toNat' s (by
    rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  unfold UInt256.shiftLeft
  rw [if_neg (by show ¬ (UInt256.ofNat s).toNat ≥ 256; omega)]
  show (Fin.shiftLeft a.val (UInt256.ofNat s).val).val = _
  unfold Fin.shiftLeft
  show (a.toNat <<< (UInt256.ofNat s).toNat) % UInt256.size = _
  rw [hsv, Nat.shiftLeft_eq]
  rfl

theorem ushrN_toNat (a : UInt256) (s : ℕ) (hs : s < 256) :
    (UInt256.shiftRight a (UInt256.ofNat s)).toNat = a.toNat / 2 ^ s := by
  have hsv : (UInt256.ofNat s).toNat = s := ulit_toNat' s (by
    rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have ha : a.toNat < UInt256.size := a.val.isLt
  unfold UInt256.shiftRight
  rw [if_neg (by show ¬ (UInt256.ofNat s).toNat ≥ 256; omega)]
  show (Fin.shiftRight a.val (UInt256.ofNat s).val).val = _
  unfold Fin.shiftRight
  show (a.toNat >>> (UInt256.ofNat s).toNat) % UInt256.size = _
  rw [hsv, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)

/-! ## Stele `uint256` bit operations on word values -/

theorem int_toNat_ofNat (n : ℕ) : (Int.ofNat n).toNat = n := rfl

theorem evalBitAnd_word (a b : UInt256) {x y : Int} (hx : x = Int.ofNat a.toNat)
    (hy : y = Int.ofNat b.toNat) :
    evalBinaryOp? (.bitAnd u256T) (.int x) (.int y) =
      .ok (.int (Int.ofNat (UInt256.land a b).toNat)) := by
  subst hx hy
  show EvalResult.ok (Value.int (normalizeInt u256T (Int.ofNat (Nat.land
    (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat a.toNat)).toNat
    (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat b.toNat)).toNat)))) = _
  have h := normalizeInt_uint256_word (UInt256.land a b)
  rw [uland_toNat] at h
  rw [normalizeInt_uint256_word a, normalizeInt_uint256_word b, int_toNat_ofNat, int_toNat_ofNat,
    show Nat.land a.toNat b.toNat = a.toNat &&& b.toNat from rfl, h, uland_toNat]

theorem evalBitOr_word (a b : UInt256) {x y : Int} (hx : x = Int.ofNat a.toNat)
    (hy : y = Int.ofNat b.toNat) :
    evalBinaryOp? (.bitOr u256T) (.int x) (.int y) =
      .ok (.int (Int.ofNat (UInt256.lor a b).toNat)) := by
  subst hx hy
  show EvalResult.ok (Value.int (normalizeInt u256T (Int.ofNat (Nat.lor
    (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat a.toNat)).toNat
    (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat b.toNat)).toNat)))) = _
  have h := normalizeInt_uint256_word (UInt256.lor a b)
  rw [u256_lor_toNat_exact] at h
  rw [normalizeInt_uint256_word a, normalizeInt_uint256_word b, int_toNat_ofNat, int_toNat_ofNat,
    show Nat.lor a.toNat b.toNat = a.toNat ||| b.toNat from rfl, h, u256_lor_toNat_exact]

theorem evalShl_word (a : UInt256) (s : ℕ) (hs : s < 256) {x : Int}
    (hx : x = Int.ofNat a.toNat) :
    evalBinaryOp? (.shl u256T) (.int x) (.int (Int.ofNat s)) =
      .ok (.int (Int.ofNat (UInt256.shiftLeft a (UInt256.ofNat s)).toNat)) := by
  subst hx
  have h1 : ¬ (Int.ofNat s < 0) := not_lt.mpr (Int.natCast_nonneg s)
  have h2 : ¬ (256 ≤ (Int.ofNat s).toNat) := by rw [int_toNat_ofNat]; omega
  show (if Int.ofNat s < 0 then EvalResult.error .typeError
    else if 256 ≤ (Int.ofNat s).toNat then EvalResult.ok (Value.int 0)
    else EvalResult.ok (Value.int (normalizeInt u256T
      (Int.ofNat a.toNat * Int.ofNat (EVM.twoPow (Int.ofNat s).toNat))))) = _
  rw [if_neg h1, if_neg h2, ushlN_toNat a s hs, int_toNat_ofNat]
  simp only [normalizeInt, EVM.twoPow]
  push_cast
  rfl

theorem evalShr_word (a : UInt256) (s : ℕ) (hs : s < 256) {x : Int}
    (hx : x = Int.ofNat a.toNat) :
    evalBinaryOp? (.shr u256T) (.int x) (.int (Int.ofNat s)) =
      .ok (.int (Int.ofNat (UInt256.shiftRight a (UInt256.ofNat s)).toNat)) := by
  subst hx
  have h1 : ¬ (Int.ofNat s < 0) := not_lt.mpr (Int.natCast_nonneg s)
  have h2 : ¬ (256 ≤ (Int.ofNat s).toNat) := by rw [int_toNat_ofNat]; omega
  show (if Int.ofNat s < 0 then EvalResult.error .typeError
    else
      if 256 ≤ (Int.ofNat s).toNat then
        EvalResult.ok (Value.int
          (if u256T.isSigned && normalizeInt u256T (Int.ofNat a.toNat) < 0 then -1 else 0))
      else EvalResult.ok (Value.int (normalizeInt u256T (Int.ofNat a.toNat) /
        Int.ofNat (EVM.twoPow (Int.ofNat s).toNat)))) = _
  rw [if_neg h1, if_neg h2, ushrN_toNat a s hs, int_toNat_ofNat, normalizeInt_uint256_word a]
  simp only [EVM.twoPow]
  push_cast
  rfl

/-! ## The `get_deposit_count` return buffer

The bytecode allocates the `bytes` value at `max(mload 0x40, 0x100) = 0x100`, writes its length
and data words there, writes the head offset `0x20` at `0xa0`, `MCOPY`s the 64-byte value to
`0xc0`, and returns `[0xa0, 0x100)`. -/

/-- Memory before the data word: free pointer `0x140` at `0x40`, length `8` at `0x100`. -/
abbrev countLenMem : ByteArray :=
  (UInt256.ofNat 8).toByteArray.write 0
    ((UInt256.ofNat 256 + UInt256.ofNat 64).toByteArray.write 0 ByteArray.empty
      (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 256).toNat 32

/-- `countLenMem` with the head offset `0x20` written at `0xa0`. -/
abbrev countHeadMem : ByteArray :=
  (UInt256.ofNat 32).toByteArray.write 0 countLenMem (UInt256.ofNat 160).toNat 32

theorem countLenMem_size : countLenMem.size = 288 := by native_decide

theorem countHeadMem_head : countHeadMem.extract 160 192 = (UInt256.ofNat 32).toByteArray := by
  native_decide

theorem countHeadMem_len : countHeadMem.extract 256 288 = (UInt256.ofNat 8).toByteArray := by
  native_decide

theorem countHeadMem_size : countHeadMem.size = 288 := by native_decide

theorem byteArray_extract_of_size (b : ByteArray) (n : ℕ) (h : b.size = n) : b.extract 0 n = b := by
  subst h; exact byteArray_extract_self b

theorem countHeadMem_split :
    countHeadMem = countLenMem.extract 0 160 ++ (UInt256.ofNat 32).toByteArray.extract 0 32 ++
      countLenMem.extract (160 + 32) 288 := by
  native_decide

theorem countDataMem_eq (b : UInt256) :
    (UInt256.ofNat 32).toByteArray.write 0
        (b.toByteArray.write 0 countLenMem (UInt256.ofNat 256 + UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 160).toNat 32 = countHeadMem ++ b.toByteArray := by
  have hb : b.toByteArray.size = 32 := toByteArray_size b
  have h32 : 32 ≤ (UInt256.ofNat 32).toByteArray.size := by rw [toByteArray_size]
  have e1 : b.toByteArray.write 0 countLenMem (UInt256.ofNat 256 + UInt256.ofNat 32).toNat 32 =
      countLenMem ++ b.toByteArray := by
    rw [show (UInt256.ofNat 256 + UInt256.ofNat 32).toNat = countLenMem.size by
        rw [countLenMem_size]; decide,
      write_at_end_eq _ _ 32 (by decide) (by omega), toByteArray_extract_all]
  have hs : (countLenMem ++ b.toByteArray).size = 320 := by
    rw [ByteArray.size_append, countLenMem_size, hb]
  rw [e1, show (UInt256.ofNat 160).toNat = 160 from rfl, write32_eq _ _ 160 h32 (by omega), hs,
    extract_append_left _ _ 0 160 (by rw [countLenMem_size]; omega),
    extract_append_span _ _ (160 + 32) 320 (by rw [countLenMem_size]; omega)
      (by rw [countLenMem_size]; omega),
    countLenMem_size, show 320 - 288 = 32 from rfl, countHeadMem_split]
  simp only [toByteArray_extract_all]
  apply ByteArray.ext
  simp only [ByteArray.data_append, Array.append_assoc]

theorem countReturn_eq (b : UInt256) :
    (((UInt256.ofNat 32).toByteArray.write 0
          (b.toByteArray.write 0 countLenMem (UInt256.ofNat 256 + UInt256.ofNat 32).toNat 32)
          (UInt256.ofNat 160).toNat 32).write (UInt256.ofNat 256).toNat
        ((UInt256.ofNat 32).toByteArray.write 0
          (b.toByteArray.write 0 countLenMem (UInt256.ofNat 256 + UInt256.ofNat 32).toNat 32)
          (UInt256.ofNat 160).toNat 32)
        (UInt256.ofNat 192).toNat (UInt256.ofNat 64).toNat).readWithPadding
      (UInt256.ofNat 160).toNat (UInt256.ofNat 96).toNat =
      (UInt256.ofNat 32).toByteArray ++ ((UInt256.ofNat 8).toByteArray ++ b.toByteArray) := by
  have hb : b.toByteArray.size = 32 := toByteArray_size b
  rw [countDataMem_eq]
  generalize hM : countHeadMem ++ b.toByteArray = M
  have hMs : M.size = 320 := by rw [← hM, ByteArray.size_append, countHeadMem_size, hb]
  have hBm : M.extract 256 (256 + 64) = (UInt256.ofNat 8).toByteArray ++ b.toByteArray := by
    rw [← hM, extract_append_span _ _ 256 (256 + 64) (by rw [countHeadMem_size]; omega)
        (by rw [countHeadMem_size]; omega), countHeadMem_size, countHeadMem_len,
      show 256 + 64 - 288 = 32 from rfl, toByteArray_extract_all]
  have hA : (M.extract 0 192).extract 160 192 = (UInt256.ofNat 32).toByteArray := by
    rw [extract_extract_BA, show 0 + 160 = 160 from rfl,
      show min (0 + 192) 192 = 192 from rfl, ← hM,
      extract_append_left _ _ 160 192 (by rw [countHeadMem_size]; omega), countHeadMem_head]
  have hAs : (M.extract 0 192).size = 192 := by rw [ByteArray.size_extract]; omega
  have hBs : (M.extract 256 (256 + 64)).size = 64 := by rw [ByteArray.size_extract]; omega
  rw [show (UInt256.ofNat 256).toNat = 256 from rfl, show (UInt256.ofNat 192).toNat = 192 from rfl,
    show (UInt256.ofNat 64).toNat = 64 from rfl, show (UInt256.ofNat 160).toNat = 160 from rfl,
    show (UInt256.ofNat 96).toNat = 96 from rfl,
    write_eq_gen_from _ _ 256 192 64 (by decide) (by omega) (by omega), hMs,
    show 192 + 64 = 256 from rfl, show (320 : ℕ) = 256 + 64 from rfl]
  rw [readWithPadding_eq_extract' _ 160 96 (by decide) (by decide) (by
      rw [ByteArray.size_append, ByteArray.size_append, hAs, hBs]; omega),
    extract_append_left _ _ 160 (160 + 96) (by rw [ByteArray.size_append, hAs, hBs]),
    extract_append_span _ _ 160 (160 + 96) (by rw [hAs]; omega) (by rw [hAs]; omega), hAs,
    show 160 + 96 - 192 = 64 from rfl, hA, byteArray_extract_of_size _ 64 hBs, hBm]

/-! ## Word forms of the byte-swap passes, in the spec's operand order -/

def swap8 (m : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (UInt256.land m (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8))
    (UInt256.land (UInt256.shiftRight m (UInt256.ofNat 8)) (UInt256.ofNat 71777214294589695))

def swap16 (v : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (UInt256.land v (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))
    (UInt256.land (UInt256.shiftRight v (UInt256.ofNat 16)) (UInt256.ofNat 281470681808895))

def chunkOf (v : UInt256) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.lor (UInt256.shiftLeft v (UInt256.ofNat 32)) (UInt256.shiftRight v (UInt256.ofNat 32)))
    (UInt256.ofNat 192)

/-- The SSZ chunk of the `uint64` held in the low bits of `m`. -/
def u64ChunkWord (m : UInt256) : UInt256 := chunkOf (swap16 (swap8 m))

/-- The value `le64` packs: the chunk's top eight bytes. -/
def le64Value (m : UInt256) : ℕ := (UInt256.shiftRight (u64ChunkWord m) (UInt256.ofNat 192)).toNat

/-- `le64`'s bytes: the eight big-endian bytes of `le64Value`. -/
def le64Bytes (m : UInt256) : List UInt8 := (EVM.word (le64Value m)).toBytesBE.drop 24

/-- The bytecode's operand order for the three passes is the spec's, commuted. -/
theorem evmChunk_eq (m : UInt256) :
    UInt256.shiftLeft (UInt256.lor
      (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895)
        (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 71777214294589695)
          (UInt256.shiftRight m (UInt256.ofNat 8))) (UInt256.shiftLeft (UInt256.land m
            (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8))) (UInt256.ofNat 16)))
        (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.land (UInt256.ofNat 71777214294589695)
          (UInt256.shiftRight m (UInt256.ofNat 8))) (UInt256.shiftLeft (UInt256.land m
            (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8))) (UInt256.ofNat 281470681808895))
          (UInt256.ofNat 16))) (UInt256.ofNat 32))
      (UInt256.shiftLeft (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895)
        (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 71777214294589695)
          (UInt256.shiftRight m (UInt256.ofNat 8))) (UInt256.shiftLeft (UInt256.land m
            (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8))) (UInt256.ofNat 16)))
        (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.land (UInt256.ofNat 71777214294589695)
          (UInt256.shiftRight m (UInt256.ofNat 8))) (UInt256.shiftLeft (UInt256.land m
            (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8))) (UInt256.ofNat 281470681808895))
          (UInt256.ofNat 16))) (UInt256.ofNat 32))) (UInt256.ofNat 192) = u64ChunkWord m := by
  have h8 : UInt256.lor (UInt256.land (UInt256.ofNat 71777214294589695)
      (UInt256.shiftRight m (UInt256.ofNat 8))) (UInt256.shiftLeft (UInt256.land m
        (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) = swap8 m := by
    rw [u256_lor_comm, u256_land_comm (UInt256.ofNat 71777214294589695)]; rfl
  have h16 (v : UInt256) : UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895)
      (UInt256.shiftRight v (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land v
        (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16)) = swap16 v := by
    rw [u256_lor_comm, u256_land_comm (UInt256.ofNat 281470681808895)]; rfl
  rw [h8, h16, u256_lor_comm (UInt256.shiftRight _ _)]
  rfl

theorem le64Value_lt (m : UInt256) : le64Value m < 2 ^ 64 := by
  have hw : (u64ChunkWord m).toNat < 2 ^ 256 := (u64ChunkWord m).val.isLt
  show (UInt256.shiftRight (u64ChunkWord m) (UInt256.ofNat 192)).toNat < 2 ^ 64
  rw [ushrN_toNat _ 192 (by decide), Nat.div_lt_iff_lt_mul (by positivity)]
  calc (u64ChunkWord m).toNat < 2 ^ 256 := hw
    _ = 2 ^ 64 * 2 ^ 192 := by norm_num

/-! ## Expression evaluation helpers -/

theorem evalBin {cfg : Config} {stele : Frame} {evm : EVM.State} {op : BinaryOp} {l r : Expr}
    {lv rv res : Value} (hand : op ≠ .and) (hor : op ≠ .or)
    (hl : evalExpr? cfg stele evm l = .ok lv) (hr : evalExpr? cfg stele evm r = .ok rv)
    (hop : evalBinaryOp? op lv rv = .ok res) :
    evalExpr? cfg stele evm (.binary op l r) = .ok res := by
  rw [evalExpr_binary_nonshort hand hor]
  simp only [hl, hr, EvalResult.bind, bind]
  exact hop

theorem evalVarL {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident} {v : Value}
    (h : stele.locals.get? name = some v) : evalExpr? cfg stele evm (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (stele.locals.get? name) = _
  rw [h]; rfl

theorem evalLit {cfg : Config} {stele : Frame} {evm : EVM.State} (n : Int) :
    evalExpr? cfg stele evm (.intLit n) = .ok (.int n) := by
  rw [evalExpr?]; rfl

theorem evalCastInt {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {i : Int}
    (t : IntType) (he : evalExpr? cfg stele evm e = .ok (.int i)) :
    evalExpr? cfg stele evm (.cast e (.elem (.int t))) = .ok (.int (normalizeInt t i)) := by
  rw [evalExpr?]
  simp only [he, EvalResult.bind, bind, castValue_int, EvalResult.ofOption]

theorem assignLocal_ok {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident}
    {old value : Value} (hget : stele.locals.get? name = some old) :
    assignStorageRef? cfg stele evm .localVar { base := name } value =
      .ok ({ stele with locals := stele.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match stele.locals.get? name with
    | some _ => EvalResult.ok (({ stele with locals := stele.locals.insert name value } : Frame), evm)
    | none => EvalResult.error EvalError.unboundVariable) = _
  rw [hget]

/-! ## The passes as Stele expressions -/

theorem evalSwap8 {cfg : Config} {stele : Frame} {evm : EVM.State} {m : UInt256}
    (hv : stele.locals.get? "v" = some (.int (Int.ofNat m.toNat))) :
    evalExpr? cfg stele evm
      (.binary (.bitOr u256T)
        (.binary (.shl u256T) (.binary (.bitAnd u256T) (.var "v") (.intLit 71777214294589695))
          (.intLit 8))
        (.binary (.bitAnd u256T) (.binary (.shr u256T) (.var "v") (.intLit 8))
          (.intLit 71777214294589695))) =
      .ok (.int (Int.ofNat (swap8 m).toNat)) :=
  evalBin (by decide) (by decide)
    (evalBin (by decide) (by decide)
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _)
        (evalBitAnd_word m (UInt256.ofNat 71777214294589695) rfl (by decide)))
      (evalLit _) (evalShl_word _ 8 (by decide) rfl))
    (evalBin (by decide) (by decide)
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _) (evalShr_word m 8 (by decide) rfl))
      (evalLit _) (evalBitAnd_word _ (UInt256.ofNat 71777214294589695) rfl (by decide)))
    (evalBitOr_word _ _ rfl rfl)

theorem evalSwap16 {cfg : Config} {stele : Frame} {evm : EVM.State} {m : UInt256}
    (hv : stele.locals.get? "v" = some (.int (Int.ofNat m.toNat))) :
    evalExpr? cfg stele evm
      (.binary (.bitOr u256T)
        (.binary (.shl u256T) (.binary (.bitAnd u256T) (.var "v") (.intLit 281470681808895))
          (.intLit 16))
        (.binary (.bitAnd u256T) (.binary (.shr u256T) (.var "v") (.intLit 16))
          (.intLit 281470681808895))) =
      .ok (.int (Int.ofNat (swap16 m).toNat)) :=
  evalBin (by decide) (by decide)
    (evalBin (by decide) (by decide)
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _)
        (evalBitAnd_word m (UInt256.ofNat 281470681808895) rfl (by decide)))
      (evalLit _) (evalShl_word _ 16 (by decide) rfl))
    (evalBin (by decide) (by decide)
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _) (evalShr_word m 16 (by decide) rfl))
      (evalLit _) (evalBitAnd_word _ (UInt256.ofNat 281470681808895) rfl (by decide)))
    (evalBitOr_word _ _ rfl rfl)

theorem evalChunkExpr {cfg : Config} {stele : Frame} {evm : EVM.State} {m : UInt256}
    (hv : stele.locals.get? "v" = some (.int (Int.ofNat m.toNat))) :
    evalExpr? cfg stele evm
      (.binary (.shl u256T)
        (.binary (.bitOr u256T) (.binary (.shl u256T) (.var "v") (.intLit 32))
          (.binary (.shr u256T) (.var "v") (.intLit 32)))
        (.intLit 192)) =
      .ok (.int (Int.ofNat (chunkOf m).toNat)) :=
  evalBin (by decide) (by decide)
    (evalBin (by decide) (by decide)
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _) (evalShl_word m 32 (by decide) rfl))
      (evalBin (by decide) (by decide) (evalVarL hv) (evalLit _) (evalShr_word m 32 (by decide) rfl))
      (evalBitOr_word _ _ rfl rfl))
    (evalLit _) (evalShl_word _ 192 (by decide) rfl)

/-! ## The `u64_chunk` and `le64` bodies -/

abbrev u64ChunkFn : FunctionDecl := contract.functions[2]!
abbrev le64Fn : FunctionDecl := contract.functions[3]!

/-- `u64_chunk(value)` returns the chunk of a word argument. -/
theorem u64ChunkBody (cfg : Config) (stele : Frame) (evm : EVM.State) (m : UInt256) :
    ∃ F, ExecFuncBody cfg
      { stele with locals := (∅ : Store).insert "value" (.int (Int.ofNat m.toNat)) }
      evm u64ChunkFn.body (.returned F evm (some [.int (Int.ofNat (u64ChunkWord m).toNat)])) := by
  have hcast : evalExpr? cfg
      { stele with locals := (∅ : Store).insert "value" (.int (Int.ofNat m.toNat)) } evm
      (.cast (.var "value") (.elem (.int u256T))) = .ok (.int (Int.ofNat m.toNat)) := by
    rw [evalCastInt u256T (evalVarL (v := .int (Int.ofNat m.toNat)) (by simp)),
      normalizeInt_uint256_word m]
  exact ⟨_, ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.letDecl hcast) <|
    ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inl rfl)
      (evalSwap8 (m := m) (by simp)) (assignLocal_ok (old := .int (Int.ofNat m.toNat)) (by simp))) <|
    ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inl rfl)
      (evalSwap16 (m := swap8 m) (by simp))
      (assignLocal_ok (old := .int (Int.ofNat (swap8 m).toNat)) (by simp))) <|
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
      (evalChunkExpr (m := swap16 (swap8 m)) (by simp))))⟩

theorem le64Value_norm (m : UInt256) :
    normalizeInt u64T (Int.ofNat (le64Value m)) = Int.ofNat (le64Value m) :=
  normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr (by simpa [EVM.twoPow] using le64Value_lt m))

theorem le64_encodePacked (m : UInt256) :
    encodePackedValue? (.elem (.int u64T)) (.int (Int.ofNat (le64Value m))) = some (le64Bytes m) := by
  have hword : encodeABIWord? (.elem (.int u64T)) (.int (Int.ofNat (le64Value m))) =
      some (EVM.word (le64Value m)) := by
    simp only [encodeABIWord?]
    rw [if_neg (by decide), if_pos ⟨Int.natCast_nonneg _,
      Int.ofNat_lt.mpr (by simpa [EVM.twoPow] using le64Value_lt m)⟩]
    rfl
  simp only [encodePackedValue?, hword]
  rfl

/-- `le64(value)` returns the chunk's top eight bytes as `bytes`. -/
theorem le64Body (cfg : Config) (stele : Frame) (hc : stele.contract = contract) (evm : EVM.State)
    (m : UInt256) :
    ∃ F, ExecFuncBody cfg
      { stele with locals := (∅ : Store).insert "value" (.int (Int.ofNat m.toNat)) }
      evm le64Fn.body (.returned F evm (some [.bytes ⟨(le64Bytes m).toArray⟩])) := by
  obtain ⟨F1, hchunk⟩ := u64ChunkBody cfg
    { stele with locals := (∅ : Store).insert "value" (.int (Int.ofNat m.toNat)) } evm m
  have hshr : evalExpr? cfg
      { stele with locals := (((∅ : Store).insert "value" (.int (Int.ofNat m.toNat))).insert
          "chunk" (.int (Int.ofNat (u64ChunkWord m).toNat))) } evm
      (.binary (.shr u256T) (.var "chunk") (.intLit 192)) =
      .ok (.int (Int.ofNat (le64Value m))) :=
    evalBin (by decide) (by decide) (evalVarL (store_get_self _ _ _)) (evalLit _)
      (evalShr_word _ 192 (by decide) rfl)
  have hcast := evalCastInt u64T hshr
  rw [le64Value_norm] at hcast
  have hpack := evalPackedArgs_single hcast (le64_encodePacked m)
  have hret : evalExpr? cfg
      { stele with locals := (((∅ : Store).insert "value" (.int (Int.ofNat m.toNat))).insert
          "chunk" (.int (Int.ofNat (u64ChunkWord m).toNat))) } evm
      (.abiEncodePacked [(.elem (.int u64T), .cast (.binary (.shr u256T) (.var "chunk") (.intLit 192))
        (.elem (.int u64T)))]) = .ok (.bytes ⟨(le64Bytes m).toArray⟩) := by
    rw [evalExpr?]
    simp only [hpack, EvalResult.bind, bind, pure]
  exact ⟨_, ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (internalCallFunctionReturn (callee := u64ChunkFn)
      (evalExprs?_singleton (evalVarL (v := .int (Int.ofNat m.toNat)) (by simp)))
      (by rw [hc]; rfl) rfl hchunk) <|
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret))⟩

/-! ## The `get_deposit_count` body -/

/-- `uint64(x)` as the bytecode computes it: the low 64 bits. -/
abbrev mask64 (c : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.ofNat 192)) c

theorem mask64_toNat (c : UInt256) : (mask64 c).toNat = c.toNat % 2 ^ 64 := by
  rw [uland_toNat, show (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.ofNat 192)).toNat =
    2 ^ 64 - 1 by decide, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]

theorem normalize_u64_word (c : UInt256) :
    normalizeInt u64T (Int.ofNat c.toNat) = Int.ofNat (mask64 c).toNat := by
  rw [mask64_toNat]
  simp only [normalizeInt, EVM.twoPow]
  push_cast
  rfl

theorem depositCount_read {L : Store} {evm : EVM.State} (hL : L.get? "deposit_count" = none) :
    evalExpr? config { contract := contract, locals := L } evm
      (.storage { base := "deposit_count", steps := [] }) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨32⟩).toNat)) :=
  evalExpr_storage_scalar_value (layout := solidityLayout! [contract.structs] [contract.storage])
    (t := .int u256T) (loc := uint256Loc ⟨32⟩) (er := { base := "deposit_count", steps := [] }) hL
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by show storageTypeAt? contract.storage _ = _; decide) rfl rfl (storageLocLoad_uint256 evm ⟨32⟩)

/-- `get_deposit_count()` returns `le64` of the low 64 bits of slot 32. -/
theorem getCountBody (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ∃ F, ExecTransitionBody config contract evm ∅ get_deposit_countTransition.body
      (.returned F evm (some [.bytes ⟨(le64Bytes (mask64
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨32⟩))).toArray⟩])) := by
  obtain ⟨F1, hle⟩ := le64Body config { contract := contract, locals := ∅ } rfl evm
    (mask64 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨32⟩))
  have harg := evalCastInt u64T (depositCount_read (L := ∅) (evm := evm) (by simp))
  rw [normalize_u64_word] at harg
  exact ⟨_, ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (internalCallFunctionReturn (callee := le64Fn)
      (evalExprs?_singleton harg) rfl rfl hle) <|
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
      (evalVarL (by simp [resumeAfterInternalCall, collapseReturns]))))⟩

/-! ## The ABI encoding of the returned `bytes` -/

theorem le64Bytes_length (m : UInt256) : (le64Bytes m).length = 8 := by
  simp [le64Bytes, word_toBytesBE_length_32]

theorem le64Bytes_fromBE (m : UInt256) : fromBytesBigEndian (le64Bytes m) = le64Value m := by
  have hq := le64Value_lt m
  have hwq : (EVM.word (le64Value m)).toNat = le64Value m :=
    ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from rfl]; omega)
  have hlen : (EVM.word (le64Value m)).toBytesBE.length = 32 := word_toBytesBE_length_32 _
  have hdroplen : ((EVM.word (le64Value m)).toBytesBE.drop 24).length = 8 := by
    rw [List.length_drop, hlen]
  have hsplit := fromBytesBigEndian_append ((EVM.word (le64Value m)).toBytesBE.take 24)
    ((EVM.word (le64Value m)).toBytesBE.drop 24)
  have hdiv := fromBytesBigEndian_append_div ((EVM.word (le64Value m)).toBytesBE.take 24)
    ((EVM.word (le64Value m)).toBytesBE.drop 24)
  rw [List.take_append_drop, hdroplen, fromBytesBE_word, hwq] at hsplit hdiv
  rw [Nat.div_eq_of_lt (by simpa using hq)] at hdiv
  rw [← hdiv, Nat.zero_mul, Nat.zero_add] at hsplit
  exact hsplit.symm

theorem le64Word_bytes (m : UInt256) :
    EVM.Word.toBytesBE (UInt256.shiftLeft (UInt256.shiftRight (u64ChunkWord m) (UInt256.ofNat 192))
      (UInt256.ofNat 192)) = le64Bytes m ++ List.replicate 24 0 := by
  have hq := le64Value_lt m
  apply fromBytesBigEndian_inj_of_length
  · rw [word_toBytesBE_length_32, List.length_append, le64Bytes_length, List.length_replicate]
  · rw [fromBytesBE_word, fromBytesBigEndian_append_zeros, le64Bytes_fromBE, ushlN_toNat _ 192 (by decide)]
    show le64Value m * 2 ^ 192 % 2 ^ 256 = le64Value m * 2 ^ (8 * 24)
    rw [Nat.mod_eq_of_lt (by
      calc le64Value m * 2 ^ 192 < 2 ^ 64 * 2 ^ 192 := Nat.mul_lt_mul_of_pos_right hq (by positivity)
        _ = 2 ^ 256 := by norm_num)]

theorem le64_padded (m : UInt256) :
    (ABI.padRightToWord (le64Bytes m)).toByteArray =
      (UInt256.shiftLeft (UInt256.shiftRight (u64ChunkWord m) (UInt256.ofNat 192))
        (UInt256.ofNat 192)).toByteArray := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray, le64Word_bytes]
  unfold ABI.padRightToWord ABI.zeroBytes
  rw [le64Bytes_length]
  rfl

theorem le64_returnEncoding (m : UInt256) :
    encodeReturnValues? [ABIType.bytes] [.bytes ⟨(le64Bytes m).toArray⟩] =
      some ((UInt256.ofNat 32).toByteArray ++ ((UInt256.ofNat 8).toByteArray ++
        (UInt256.shiftLeft (UInt256.shiftRight (u64ChunkWord m) (UInt256.ofNat 192))
          (UInt256.ofNat 192)).toByteArray)) := by
  have hsize : (⟨(le64Bytes m).toArray⟩ : ByteArray).size = 8 := by
    show (le64Bytes m).toArray.size = 8
    rw [List.size_toArray]; exact le64Bytes_length m
  have hlist : (⟨(le64Bytes m).toArray⟩ : ByteArray).toList = le64Bytes m := by
    rw [byteArray_toList_eq]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
    encodeABIValue?, isDynamicABIType, staticABIEncodedSize?, Option.bind, bind, if_true,
    List.nil_append, List.append_nil, Nat.add_zero, List.length_nil, hsize, hlist]
  congr 1
  rw [mk_toArray_eq, list_toByteArray_append, list_toByteArray_append, natBytes_toByteArray',
    natBytes_toByteArray', le64_padded]

end FeProofs.Deposit
