import FeProofs.ScalarStore.SpecBytes
import FeProofs.ScalarStore.ModelCorrect
import FeProofs.ScalarStore.RuntimeCorrect
import FeSpecProofs.ScalarStore

/-!
# FeScalarStore: the bytecode refines the interpreter's semantics

fe-spec's interpreter on the EVM host (`Fe/EVM/SpecHost.lean`), run on the serialized program
(`Fe.Proofs.scalarStore`, loaded from `fixtures/scalar_store.json`), ends as the hand-written
model's runtime entry does, so the bytecode certificate carries over to it.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.ScalarStore.Spec

/-- The EVM host the runtime code runs on: FeScalarStore has no immutable fields and creates no
    contracts. -/
abbrev host : Fe.Host.Host Env World := specHost 0 []

/-- The interpreter's runtime entry of FeScalarStore on the EVM: reserve low memory, as the
    compiled entry does, and run `Fe.Sem.runtime`.  An entry only halts or fails; should the
    specification give up (`SpecError`, which `runtime_spec` rules out) the run is taken not to
    terminate. -/
def runtimeM : FeM ByteArray := do
  reserve
  match ← ((Fe.Sem.runtime Fe.Proofs.scalarStore host).run {}).run with
  | .ok (e, _) => nomatch e
  | .error _ => Fe.M.diverge

/-! The host's operations this contract uses.  (`simp` cannot unfold `specHost` itself: Lean
generates no equations for its match on array literals in `messageCall`.) -/

@[simp] theorem host_callDataSize :
    host.ctx .callDataSize = (do return (← calldatasize).toNat) := rfl
@[simp] theorem host_callValue : host.ctx .callValue = (do return (← callvalue).toNat) := rfl
@[simp] theorem host_callDataRead (o l : Nat) :
    host.callDataRead o l = (do return (← read).calldata.readWithPadding o l) := rfl
@[simp] theorem host_sload (k : Nat) : host.sload k = (do return (← sload (.ofNat k)).toNat) := rfl
@[simp] theorem host_sstore (k v : Nat) : host.sstore k v = sstore (.ofNat k) (.ofNat v) := rfl
@[simp] theorem host_alloc (n : Nat) : host.alloc n = (do return (← alloc (.ofNat n)).toNat) := rfl
@[simp] theorem host_memWrite (a : Nat) (d : ByteArray) :
    host.memWrite a d = mstoreBytes (.ofNat a) d := rfl
@[simp] theorem host_memRead (a l : Nat) :
    host.memRead a l = (do return (← get).memory.readWithPadding a l) := rfl

/-- On calldata with the selector of `get()`, the interpreter's runtime entry ends as the
    hand-written model's does. -/
theorem get_endsAs (I : ExecutionEnv) (w : World) (hmem : w.memory.size + 32 < UInt256.size)
    (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (h1 : selIs I (feScalarStoreSelBytes 1)) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  unfold runtimeM
  rw [Fe.Proofs.ScalarStore.runtime_spec]
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
  have hsel : Fe.Sem.bytesNat (I.calldata.readWithPadding 0 32) / 2 ^ 224 = 1833756220 := by
    rw [FeProofs.Spec.selector_eq, selWord_hit (getEvmSelector hsz) h1]; rfl
  simp only [Nat.reducePow] at hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [runtime_get hsz h0 h1 hwv]
    have hroom : w.reserved.memory.size + 32 < UInt256.size :=
      reserveMemory_room hmem (by decide)
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.getEntry, hn, Nat.not_lt.mpr hsz, hsel, hwv,
      alloc, callvalue, toNat32, hroom, mstoreBytes]
    have hA : (UInt256.ofNat w.reserved.memory.size).toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w.reserved.memory.size := by
      rw [UInt256.toNat_ofNat_of_lt (by omega)]
      exact Nat.mod_eq_of_lt (by unfold UInt256.size at hroom; omega)
    have hv : (slotWord I w.accounts (UInt256.ofNat 0)).toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        (slotWord I w.accounts (UInt256.ofNat 0)).toNat :=
      Nat.mod_eq_of_lt (slotWord I w.accounts (UInt256.ofNat 0)).val.isLt
    have hzs : ({ data := Array.replicate 32 0 } : ByteArray).size = 32 := by
      show (Array.replicate 32 (0 : UInt8)).size = 32; exact Array.size_replicate
    have hbase : (({ data := Array.replicate 32 0 } : ByteArray).write 0
        (w.reserved.memory ++ { data := Array.replicate 32 0 }) w.reserved.memory.size 32).size =
        w.reserved.memory.size + 32 := by
      rw [byteArray_write_size_of_inBounds _ _ _ _ (le_of_eq hzs.symm)
        (by rw [ByteArray.size_append, hzs])]
      rw [ByteArray.size_append, hzs]
    have hlt : w.reserved.memory.size < UInt256.size := by omega
    rw [UInt256.toNat_ofNat_of_lt hlt] at hA
    simp only [hA, hv, UInt256.toNat_ofNat_of_lt hlt, Fe.Sem.natBytes_size, hzs]
    have hd : (Fe.Sem.natBytes (slotWord I w.accounts (UInt256.ofNat 0)).toNat 32).extract 0 32 =
        (slotWord I w.accounts (UInt256.ofNat 0)).toByteArray := by
      have h := ByteArray.extract_zero_size
        (b := Fe.Sem.natBytes (slotWord I w.accounts (UInt256.ofNat 0)).toNat 32)
      rw [Fe.Sem.natBytes_size] at h
      rw [h, FeProofs.Spec.natBytes_eq (slotWord I w.accounts (UInt256.ofNat 0)).toNat
        (slotWord I w.accounts (UInt256.ofNat 0)).val.isLt, u256_ofNat_toNat]
    rw [write32_read_back _ _ _ (by rw [Fe.Sem.natBytes_size]) (by rw [hbase]; omega), hd]
    exact .stop_ok rfl rfl rfl
  · rw [runtime_get_value hsz h0 h1 hwv]
    have hwv' : I.weiValue.toNat ≠ 0 := fun h => hwv (u256_inj h)
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.getEntry, hn, Nat.not_lt.mpr hsz, hsel,
      callvalue, hwv']
    exact .exit _

end FeProofs.ScalarStore.Spec
