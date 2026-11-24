import Fe.EVM.SpecHostLemmas
import FeProofs.ScalarStore.SonatinaCorrect
import FeProofs.ScalarStore.ModelCorrect
import FeProofs.ScalarStore.RuntimeCorrect
import FeProofs.Lib.BytesCodec
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

/-- The interpreter's runtime entry of FeScalarStore on the EVM (`specEntry`).  `specEntry`'s
    `reserve` (low memory grown to `0x60` bytes) is an EVM-host entry shim outside
    `Fe.Sem.runtime`, the same one the exported entry starts with; a `SpecError` is made
    divergence, which `runtime_exits` rules out. -/
def runtimeM : FeM ByteArray := specEntry (Fe.Sem.runtime Fe.Proofs.scalarStore host)

/-- On calldata with the selector of `get()`, the interpreter's runtime entry ends as the
    hand-written model's does. -/
theorem get_endsAs (I : ExecutionEnv) (w : World) (hmem : w.memory.size + 32 < UInt256.size)
    (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (h1 : selIs I (feScalarStoreSelBytes 1)) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  unfold runtimeM specEntry
  rw [Fe.Proofs.ScalarStore.runtime_spec]
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
  have hsel : Fe.Sem.bytesNat (I.calldata.readWithPadding 0 32) / 2 ^ 224 = 1833756220 := by
    rw [Fe.EVM.selector_eq, selWord_hit (getEvmSelector hsz) h1]; rfl
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
      rw [h, Fe.EVM.natBytes_eq (slotWord I w.accounts (UInt256.ofNat 0)).toNat
        (slotWord I w.accounts (UInt256.ofNat 0)).val.isLt, u256_ofNat_toNat]
    rw [write32_read_back _ _ _ (by rw [Fe.Sem.natBytes_size]) (by rw [hbase]; omega), hd]
    exact .stop_ok rfl rfl rfl
  · rw [runtime_get_value hsz h0 h1 hwv]
    have hwv' : I.weiValue.toNat ≠ 0 := fun h => hwv (u256_inj h)
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.getEntry, hn, Nat.not_lt.mpr hsz, hsel,
      callvalue, hwv']
    exact .exit _

/-- Calldata shorter than a selector. -/
theorem short_endsAs (I : ExecutionEnv) (w : World) (hshort : I.calldata.size < 4) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
  rw [runtime_short hshort]
  unfold runtimeM specEntry
  rw [Fe.Proofs.ScalarStore.runtime_spec]
  simp [M.exec_bind, hn, hshort]
  exact .exit _

/-- A selector of neither arm. -/
theorem noMatch_endsAs (I : ExecutionEnv) (w : World) (hsz : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64)
    (h0 : ¬ selIs I (feScalarStoreSelBytes 0)) (h1 : ¬ selIs I (feScalarStoreSelBytes 1)) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
  have miss : ∀ i, (¬ selIs I (feScalarStoreSelBytes i)) →
      (feScalarStoreSelBytes i == I.calldata.extract 0 4) = false :=
    fun i h => by simpa [selIs] using h
  have w0 := selWord_miss (setEvmSelector hsz) (miss 0 h0)
  have w1 := selWord_miss (getEvmSelector hsz) (miss 1 h1)
  have hs0 : Fe.Sem.bytesNat (I.calldata.readWithPadding 0 32) / 2 ^ 224 ≠ 1627277233 := by
    rw [Fe.EVM.selector_eq]; intro h; exact w0 (u256_inj h)
  have hs1 : Fe.Sem.bytesNat (I.calldata.readWithPadding 0 32) / 2 ^ 224 ≠ 1833756220 := by
    rw [Fe.EVM.selector_eq]; intro h; exact w1 (u256_inj h)
  simp only [Nat.reducePow] at hs0 hs1
  rw [runtime_noMatch hsz h0 h1]
  unfold runtimeM specEntry
  rw [Fe.Proofs.ScalarStore.runtime_spec]
  simp [M.exec_bind, hn, Nat.not_lt.mpr hsz, hs0, hs1]
  exact .exit _

/-- On calldata with the selector of `set(uint256)`. -/
theorem set_endsAs (I : ExecutionEnv) (w : World) (hsz : 4 ≤ I.calldata.size)
    (hfits : I.calldata.size < 2 ^ 64) (h0 : selIs I (feScalarStoreSelBytes 0)) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
  have hw := selWord_hit (setEvmSelector hsz) h0
  have hs0 : Fe.Sem.bytesNat (I.calldata.readWithPadding 0 32) / 2 ^ 224 = 1627277233 := by
    rw [Fe.EVM.selector_eq, hw]; rfl
  simp only [Nat.reducePow] at hs0
  have hmod : I.calldata.size % 18446744073709551616 = I.calldata.size := Nat.mod_eq_of_lt hfits
  have hbad := badHead_iff I.calldata 1 hfits
  unfold runtimeM specEntry
  rw [Fe.Proofs.ScalarStore.runtime_spec]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rw [runtime_set_value hsz h0 hwv]
    have hwv' : I.weiValue.toNat ≠ 0 := fun h => hwv (u256_inj h)
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.setEntry, hn, Nat.not_lt.mpr hsz, hs0,
      callvalue, hwv']
    exact .exit _
  by_cases hshort : I.calldata.size < 36
  · rw [runtime_set_head hsz h0 hwv (hbad.mpr (by omega))]
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.setEntry, hn, Nat.not_lt.mpr hsz, hs0,
      callvalue, hwv, hmod, hshort]
    exact .exit _
  have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
  have hword := calldataWord_eq I.calldata 4 (by omega)
  by_cases hperm : I.perm = true
  · rw [runtime_set hsz h0 hwv hgood hperm]
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.setEntry, hn, Nat.not_lt.mpr hsz, hs0,
      callvalue, hwv, hmod, hshort, exec_sstore, hperm, hword]
    exact .stop_ok rfl rfl rfl
  · rw [runtime_set_static hsz h0 hwv hgood (by simpa using hperm)]
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.setEntry, hn, Nat.not_lt.mpr hsz, hs0,
      callvalue, hwv, hmod, hshort, exec_sstore, hperm]
    exact .exit _

/-- The interpreter's runtime entry ends as the hand-written model's does, on calldata below
    `2 ^ 64` bytes (the bound std's ABI decoder assumes, `CalldataFits`). -/
theorem runtime_endsAs (I : ExecutionEnv) (w : World) (hmem : w.memory.size + 32 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs (runtimeM.exec I w) (Model.runtime.exec I w) := by
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact short_endsAs I w (by omega)
  by_cases h0 : selIs I (feScalarStoreSelBytes 0)
  · exact set_endsAs I w hsz hfits h0
  by_cases h1 : selIs I (feScalarStoreSelBytes 1)
  · exact get_endsAs I w hmem hsz hfits h0 h1
  · exact noMatch_endsAs I w hsz hfits h0 h1

/-- **The interpreter never gives up on FeScalarStore**: on calldata below `2 ^ 64` bytes, the
    interpreter's runtime entry on the EVM host, from reserved memory, ends in a Fe exit (a
    return, a revert or a stop): never a `SpecError` and never divergence.  (`RefinesOn` alone
    would admit a model that diverges where the bytecode is `Exhausted`; this rules it out.) -/
theorem runtime_exits (I : ExecutionEnv) (w : World) (hmem : w.memory.size + 32 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    ∃ f, (((Fe.Sem.runtime Fe.Proofs.scalarStore host).run {}).run).exec I w.reserved =
      some (.error f) := by
  have hm : ∃ y, Model.runtime.exec I w = some y := by
    by_cases hsz : 4 ≤ I.calldata.size
    swap
    · exact ⟨_, runtime_short (by omega)⟩
    by_cases h0 : selIs I (feScalarStoreSelBytes 0)
    · by_cases hwv : I.weiValue = ⟨0⟩
      swap
      · exact ⟨_, runtime_set_value hsz h0 hwv⟩
      by_cases hbad : BadHead I.calldata 1
      · exact ⟨_, runtime_set_head hsz h0 hwv hbad⟩
      cases hperm : I.perm
      · exact ⟨_, runtime_set_static hsz h0 hwv hbad hperm⟩
      · exact ⟨_, runtime_set hsz h0 hwv hbad hperm⟩
    by_cases h1 : selIs I (feScalarStoreSelBytes 1)
    · by_cases hwv : I.weiValue = ⟨0⟩
      · exact ⟨_, runtime_get hsz h0 h1 hwv⟩
      · exact ⟨_, runtime_get_value hsz h0 h1 hwv⟩
    · exact ⟨_, runtime_noMatch hsz h0 h1⟩
  have h := runtime_endsAs I w hmem hfits
  obtain ⟨y, hy⟩ := hm
  rw [hy] at h
  generalize hr : runtimeM.exec I w = r at h
  cases h <;> obtain ⟨f, -, hf⟩ := specEntry_exits hr <;> exact ⟨f, hf⟩

/-- FeScalarStore with the interpreter's runtime entry.  Deployment is the exported one: the
    interpreter's `initEntry` is proved in `SpecDeploy.lean` (`fullContract`). -/
def contract : ContractModel := { Exported.contract with runtime := runtimeM }

/-- **The runtime bytecode of FeScalarStore refines fe-spec's interpreter** of its serialized
    program on the EVM host, at profile `P1` (accounts, return data, logs and revert payloads),
    on calldata below `2 ^ 64` bytes: the exported contract's `P1` certificate
    (`feScalarStoreRefinesExportedP1`, through the Sonatina sidecar), transferred because the
    interpreter and the exported entry both end as the hand-written model does.

    The claim is this theorem together with `runtime_exits`: `RefinesOn` admits a diverging
    model wherever the bytecode is `Exhausted`, and `specEntry` makes a `SpecError` divergence,
    so this type alone does not say the interpreter never gives up; `runtime_exits` does.

    `CalldataFits` is load-bearing.  For calldata of `2 ^ 64` bytes or more the interpreter and
    the bytecode differ in both directions: the interpreter, following std, checks the
    calldata size truncated to `u64` (`size % 2 ^ 64 < 36`, `set_entry_spec`), while the
    bytecode checks the full size (`BadHead`: Sonatina removes the `trunc i64; zext i256` of
    the size under its calldata-size bound).  This is the known calldata-size assumption of
    every certificate here, not a new divergence. -/
theorem feScalarStoreRefinesSpec : RefinesOn .P1 feScalarStoreBytecode contract CalldataFits :=
  RefinesOn.of_common Sonatina.feScalarStoreRefinesExportedP1 rfl Model.runtime
    (fun σ A feed I hfits => Exported.runtime_endsAs I (World.init σ A feed)
      (by simp [World.init, UInt256.size]) hfits)
    (fun σ A feed I hfits => runtime_endsAs I (World.init σ A feed)
      (by simp [World.init, UInt256.size]) hfits)

end FeProofs.ScalarStore.Spec
