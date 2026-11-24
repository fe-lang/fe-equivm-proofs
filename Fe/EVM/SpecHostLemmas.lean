import Fe.EVM.SpecHost
import Fe.EVM.Entry
import Fe.Sem.Theory.HostCodec
import Reasoning.Memory
import FeProofs.Lib.BytesCodec

/-!
# Reasoning about the interpreter on the EVM host

What a proof that an interpreter entry on `specHost` ends as a model's entry needs, for any
contract:

* `specHost`'s operations as `rfl` equations (`simp` cannot unfold `specHost` itself: Lean
  generates no equations for the array-literal patterns of its `messageCall` and
  `createAccount`);
* fe-spec's byte codecs against EVMLean's: `bytesNat_eq`, `natBytes_eq`, `readBytes_zero_32`,
  `selector_eq`, `calldataWord_eq`;
* `specEntry`, an interpreter entry as an `FeM` entry, generic in the program;
* `RefinesOn.of_common`: a certificate of the bytecode against one model transfers to another
  that ends as a common model does.

A contract's capstone is then: the host-generic `runtime_spec`, one `EndsAs` per arm, and
`RefinesOn.of_common`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Fe.EVM

/-! ## The host's operations -/

section
variable (r : Nat) (c : List (String × ByteArray))

@[simp] theorem specHost_callDataSize :
    (specHost r c).ctx .callDataSize = (do return (← calldatasize).toNat) := rfl
@[simp] theorem specHost_callValue :
    (specHost r c).ctx .callValue = (do return (← callvalue).toNat) := rfl
@[simp] theorem specHost_caller : (specHost r c).ctx .caller = (do return (← caller).toNat) := rfl
@[simp] theorem specHost_callDataRead (o l : Nat) :
    (specHost r c).callDataRead o l = (do return (← read).calldata.readWithPadding o l) := rfl
@[simp] theorem specHost_sload (k : Nat) :
    (specHost r c).sload k = (do return (← sload (.ofNat k)).toNat) := rfl
@[simp] theorem specHost_sstore (k v : Nat) :
    (specHost r c).sstore k v = sstore (.ofNat k) (.ofNat v) := rfl
@[simp] theorem specHost_alloc (n : Nat) :
    (specHost r c).alloc n = (do return (← alloc (.ofNat n)).toNat) := rfl
@[simp] theorem specHost_memWrite (a : Nat) (d : ByteArray) :
    (specHost r c).memWrite a d = mstoreBytes (.ofNat a) d := rfl
@[simp] theorem specHost_memRead (a l : Nat) :
    (specHost r c).memRead a l = (do return (← get).memory.readWithPadding a l) := rfl
@[simp] theorem specHost_codeSize :
    (specHost r c).ctx .codeSize = (do return (← codesize).toNat) := rfl
@[simp] theorem specHost_regionLen : (specHost r c).ctx .currentCodeRegionLen = pure r := rfl
@[simp] theorem specHost_codeRead (o l : Nat) :
    (specHost r c).codeRead o l = (do return (← read).code.readWithPadding o l) := rfl
@[simp] theorem specHost_log (ts : Array Nat) (d : ByteArray) :
    (specHost r c).log ts d = emit (ts.map .ofNat) d := rfl
@[simp] theorem specHost_keccak256 (b : ByteArray) :
    (specHost r c).keccak256 b = pure (fromByteArrayBigEndian (KEC b)) := rfl

end

/-! ## Byte codecs -/

theorem foldl_be (l : List UInt8) (a : Nat) :
    l.foldl (fun acc x => acc * 256 + x.toNat) a = a * 256 ^ l.length + fromBytes' l.reverse := by
  induction l generalizing a with
  | nil => simp [fromBytes']
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, fromBytes'_append, List.length_reverse,
      show (2 : ℕ) ^ (8 * xs.length) = 256 ^ xs.length by rw [pow_mul]; norm_num]
    simp only [fromBytes', List.length_cons, pow_succ, UInt8.toNat]
    have : (x.toFin : ℕ) = x.toBitVec.toNat := rfl
    rw [this]; ring

theorem bytesNat_eq (b : ByteArray) : Fe.Sem.bytesNat b = fromByteArrayBigEndian b := by
  unfold Fe.Sem.bytesNat fromByteArrayBigEndian fromBytesBigEndian
  rw [← Array.foldl_toList, foldl_be, Ethereum.byteArray_toList_eq]
  simp

theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  apply ByteArray.ext; exact Array.toList_inj.mp h

theorem bsize (b : ByteArray) : b.size = b.data.toList.length := (Array.length_toList).symm

theorem readBytes_zero_32 (cd : ByteArray) : cd.readBytes 0 32 = cd.readWithPadding 0 32 := by
  apply bytes_ext
  have hcs := copySlice32_toList cd
  have hsz : (cd.copySlice 0 ByteArray.empty 0 32).size = min 32 cd.size := by
    rw [bsize, hcs, List.length_take, bsize]
  unfold ByteArray.readBytes ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp only [show (0 < 2 ^ 64 && 32 < 2 ^ 64) = true by decide, ite_true]
  rw [ByteArray.toList_data_append, hcs]
  by_cases h0 : cd.size = 0
  · have hz : cd.data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [← bsize]; exact h0)
    simp [h0, hz, hsz, byteArray_zeroes_toList]
  · simp [h0, hsz, byteArray_zeroes_toList, ByteArray.data_extract,
      Array.toList_extract, List.extract, ByteArray.size_extract]

/-- The interpreter's selector, the first word of calldata over `2 ^ 224`, is the selector word
    the dispatcher compares. -/
theorem selector_eq (cd : ByteArray) :
    Fe.Sem.bytesNat (cd.readWithPadding 0 32) / 2 ^ 224 = (selWord cd).toNat := by
  rw [bytesNat_eq, selWord, readBytes_zero_32, uInt256OfByteArray_eq]
  have hlt := fromByteArrayBigEndian_readWithPadding0_32_lt cd
  simp only [UInt256.shiftRight, UInt256.toNat]
  split
  · exact absurd ‹_› (by decide)
  have e : (UInt256.ofNat (fromByteArrayBigEndian (cd.readWithPadding 0 32))).val.val =
      fromByteArrayBigEndian (cd.readWithPadding 0 32) := UInt256.toNat_ofNat_of_lt hlt
  show _ = ((UInt256.ofNat _).val.val >>> (224 : Fin UInt256.size).val) % UInt256.size
  rw [e, show ((224 : Fin UInt256.size).val) = 224 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hlt)]

/-- A word as the interpreter writes it is EVMLean's 32 bytes of it. -/
theorem natBytes_eq (v : Nat) (hv : v < UInt256.size) :
    Fe.Sem.natBytes v 32 = UInt256.toByteArray (UInt256.ofNat v) := by
  have h := toByteArray_ofNat_fromByteArrayBigEndian_of_size (Fe.Sem.natBytes_size v 32)
  rw [← bytesNat_eq, Fe.Sem.bytesNat_natBytes, Nat.mod_eq_of_lt (by simpa [UInt256.size] using hv)] at h
  exact h.symm


/-- The calldata word at `off` as the interpreter reads it is the model's `calldataWord`. -/
theorem calldataWord_eq (cd : ByteArray) (off : Nat) (h : off + 32 ≤ cd.size) :
    UInt256.ofNat (Fe.Sem.bytesNat (cd.readWithPadding off 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) = calldataWord cd off := by
  rw [readWithPadding_eq_extract cd off h, bytesNat_eq, calldataWord,
    FeProofs.Lib.readBytes32_extract cd h, uInt256OfByteArray_eq]
  apply Reasoning.Theory.u256_inj
  simp only [UInt256.toNat, UInt256.ofNat, Id.run, Fin.ofNat, Fin.val_mk]
  show _ % _ % UInt256.size = _ % UInt256.size
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) = UInt256.size from rfl, Nat.mod_mod]

/-! ## Entries and certificates -/

/-- An interpreter entry as a model entry: reserve low memory, as compiled entries do, and run
    it from no cells.  An entry only halts or fails; should the specification give up
    (`SpecError`) the run is taken not to terminate. -/
def specEntry (m : Fe.Sem.InterpM Env World Empty) : FeM ByteArray := do
  reserve
  match ← (m.run {}).run with
  | .ok (e, _) => nomatch e
  | .error _ => Fe.M.diverge

/-- A result that agrees with a run agrees with the run it ends as. -/
theorem Agrees.to_endsAs {p : Profile} {evm : EvmResult}
    {e m : Option (Except (Exit World) (ByteArray × World))}
    (he : EndsAs e m) (h : Agrees p evm e) : Agrees p evm m := by
  cases he with
  | stop_ok ha hl _ | stop_stop ha hl _ | ok_ok ha hl _ | ok_stop ha hl _ =>
    simpa only [Agrees, ha, hl] using h
  | exit f => exact h
  | panic_revert code => exact h
  | diverge => exact h

/-- Two runs that end as a third does agree with the same EVM results. -/
theorem Agrees.of_endsAs_common {p : Profile} {evm : EvmResult}
    {a e m : Option (Except (Exit World) (ByteArray × World))}
    (ha : EndsAs a m) (he : EndsAs e m) (h : Agrees p evm e) : Agrees p evm a :=
  Agrees.of_endsAs ha (Agrees.to_endsAs he h)

/-- A certificate of the bytecode against model `m` transfers to `m'` when, on every admitted
    call from every initial world, both entries end as a common model's does. -/
theorem RefinesOn.of_common {p : Profile} {bytecode : ByteArray} {m m' : ContractModel}
    {admits : ExecutionEnv → Prop} (h : RefinesOn p bytecode m admits)
    (hi : m'.immutables = m.immutables) (common : FeM ByteArray)
    (hm : ∀ σ A feed I, admits I → EndsAs (m.runtime.exec I (World.init σ A feed))
      (common.exec I (World.init σ A feed)))
    (hm' : ∀ σ A feed I, admits I → EndsAs (m'.runtime.exec I (World.init σ A feed))
      (common.exec I (World.init σ A feed))) :
    RefinesOn p bytecode m' admits := by
  intro σ σ₀ g A I tail hcode htail hown hadm
  rcases h σ σ₀ g A I tail hcode (hi ▸ htail) hown hadm with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs_common (hm' σ A feed I hadm) (hm σ A feed I hadm) h⟩

end Fe.EVM
