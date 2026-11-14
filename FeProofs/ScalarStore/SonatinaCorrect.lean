import FeProofs.ScalarStore.SonatinaRun
import FeProofs.ScalarStore.ExportedStd

/-!
# FeScalarStore: the bytecode refines the exported contract at P1

The machine IR's runtime ends as the exported runtime entry does on each call
(`runtime_endsAs`), and its constructor as the exported deployment entry does on one argument
word (`init_endsAs`), so the machine IR implements the exported contract and the checker's
certificate of the sidecar carries over to it at profile `P1`.  Each case of the proofs is the
exported side by `simp` with the std lemmas (`ExportedStd.lean`), the machine IR's side by its
run lemma (`SonatinaRun.lean`), closed by an `EndsAs` constructor.  The init IR reads its
argument and the runtime it returns from its own code, the creation code with the argument
after it.
-/

namespace FeProofs.ScalarStore.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open Exported (decodeSet_exec decodeGet_exec initEntry_exec)

variable (I : ExecutionEnv) (w : World)

/- The exported entries, their arms and the primitives they reach unfold under `simp` here. -/
attribute [local simp] Exported.runtime Exported.recv0_arm0_entry Exported.recv0_arm1_entry
  Exported.recv0_arm0 Exported.recv0_arm1 Exported.init Exported.Field.stored Place.storage store
  load sload entry selector_exec exec_nonPayable exec_sstore returnNone_exec

/-- The machine IR's runtime ends as the exported runtime entry does, on calldata below `2 ^ 64`
    bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 32 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry Exported.runtime).exec I w) ((sidecar.model .machine).runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    Reasoning.Theory.ulit_toNat' _ (by unfold UInt256.size; omega)
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · rw [entry_exec (f := .revert .empty) (by simp [hn, show I.calldata.size < 4 by omega]),
      ir_runtime (fun m ic => ir_short m ic I w (by omega))]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := by omega
  have s0 := selWord_eq_iff (cd := I.calldata) (k := 0x60fe47b1) (by decide)
  have s1 := selWord_eq_iff (cd := I.calldata) (k := 0x6d4ce63c) (by decide)
  have hdec := decodeSet_exec I w hsz hfits
  by_cases h0 : selWord I.calldata = UInt256.ofNat 0x60fe47b1
  · -- `set(uint256)`
    have hs := s0.mp h0
    rw [show (entry Exported.runtime).exec I w = (entry Exported.recv0_arm1_entry).exec I w by
      simp [hn, hn4, h0]]
    by_cases hwv : I.weiValue = ⟨0⟩
    swap
    · rw [entry_exec (f := .revert .empty) (by simp [hwv]),
        ir_runtime (fun m ic => ir_set_value m ic w hsz hfits hs hwv)]
      exact .exit _
    by_cases hshort : I.calldata.size < 36
    · rw [entry_exec (f := .revert .empty) (by simp [hwv, hdec, hshort]),
        ir_runtime (fun m ic => ir_set_head m ic w hsz hfits hs hwv hshort)]
      exact .exit _
    by_cases hperm : I.perm = true
    · rw [entry_exec (f := .stop .empty
          { w with accounts := storeWord I.codeOwner w.accounts (.ofNat 0) (word I.calldata 4) })
          (by simp [hwv, hdec, hshort, hperm]),
        ir_runtime (fun m ic => ir_set m ic w hsz hfits hs hwv (by omega) hperm)]
      exact .stop_stop rfl rfl rfl
    · rw [entry_exec (f := .static) (by simp [hwv, hdec, hshort, hperm]),
        ir_runtime (fun m ic => ir_set_static m ic w hsz hfits hs hwv (by omega)
          (by simpa using hperm))]
      exact .exit _
  by_cases h1 : selWord I.calldata = UInt256.ofNat 0x6d4ce63c
  · -- `get()`
    have hs := s1.mp h1
    rw [show (entry Exported.runtime).exec I w = (entry Exported.recv0_arm0_entry).exec I w by
      simp [hn, hn4, h1, show UInt256.ofNat 0x6d4ce63c ≠ UInt256.ofNat 0x60fe47b1 by decide]]
    by_cases hwv : I.weiValue = ⟨0⟩
    swap
    · rw [entry_exec (f := .revert .empty) (by simp [hwv]),
        ir_runtime (fun m ic => ir_get_value m ic w hsz hfits hs hwv)]
      exact .exit _
    rw [entry_exec (f := .stop (slotWord I w.accounts (.ofNat 0)).toByteArray
          { w with memory := returned w.memory (slotWord I w.accounts (.ofNat 0)) })
          (by simp [hwv, decodeGet_exec, FeProofs.Lib.returnU256_exec I w _ hmem]),
      ir_runtime (fun m ic => ir_get m ic w hsz hfits hs hwv)]
    exact .stop_stop rfl rfl rfl
  · -- no arm's selector
    rw [entry_exec (f := .revert .empty) (by simp [hn, hn4, h0, h1]),
      ir_runtime (fun m ic => ir_noMatch m ic w hsz hfits (mt s0.mpr h0) (mt s1.mpr h1))]
    exact .exit _

/-- The machine IR implements the exported contract on calldata below `2 ^ 64` bytes. -/
theorem feScalarStoreImplements :
    Implements Exported.contract (sidecar.model .machine) CalldataFits :=
  fun I σ A feed hfits => ⟨feed, runtime_endsAs I (World.init σ A feed)
    (by simp [World.init, UInt256.size]) hfits⟩

/-- The runtime bytecode refines the exported contract at profile `P1`, on calldata below
    `2 ^ 64` bytes: the checker's certificate of the sidecar, whose runtime bytes are the
    pinned ones, composed with `feScalarStoreImplements`. -/
theorem feScalarStoreRefinesExportedP1 :
    RefinesOn .P1 feScalarStoreBytecode Exported.contract CalldataFits :=
  RefinesOn.of_implements (sidecar_runtime ▸ sidecar_sound.1) feScalarStoreImplements rfl

/-! ## Deployment -/

/-- The machine IR's constructor ends as the exported deployment entry does, on one argument
    word after the pinned creation code. -/
theorem init_endsAs (v : UInt256) (hroom : w.memory.size + 32 < UInt256.size)
    (hcode : I.code = feScalarStoreCreationBytecode ++ ctorTail v) (hperm : I.perm = true) :
    EndsAs ((Exported.init_entry (ctorTail v) >>= fun tail =>
        pure (feScalarStoreBytecode ++ tail)).exec I w)
      (((sidecar.model .machine).init (ctorTail v) >>= fun tail =>
        pure (ByteArray.empty ++ tail)).exec I w) := by
  obtain ⟨hrt, hcs⟩ := creation_runtime
  have hts : (ctorTail v).size = 32 := Reasoning.Theory.word_toBytesBE_toByteArray_size v
  have hsize : I.code.size = 165 := by rw [hcode, ByteArray.size_append, hcs, hts]
  have harg : I.code.extract 133 165 = ctorTail v := by
    rw [hcode, Reasoning.Theory.extract_append_right_window _ _ _ _ (by omega), hcs]
    show (ctorTail v).extract 0 32 = _
    rw [← hts, Reasoning.Theory.byteArray_extract_self]
  -- The prologue's world, whose memory reaches past address 96.
  let w₀ := { w with memory := (UInt256.ofNat 96).toByteArray.write 0 w.memory 64 32 }
  have hmem : 96 ≤ w₀.memory.size :=
    Reasoning.Theory.toByteArray_write_size_ge_off_add32 _ _ 64
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le (by decide) USize.le_size))
  have hword : uInt256OfByteArray ((I.code.write 133 w₀.memory 96 32).readWithPadding 96 32) =
      v := by
    rw [write_window _ _ _ _ _ (by decide) (by omega), harg,
      Reasoning.Theory.write32_read_back _ _ _ (by omega) hmem, ← hts,
      Reasoning.Theory.byteArray_extract_self, Exported.ctorTail_eq,
      Reasoning.Theory.uInt256OfByteArray_toByteArray]
  have hret : ∀ M, (I.code.write 53 M 0 80).readWithPadding 0 80 = feScalarStoreBytecode := by
    intro M
    rw [Reasoning.Theory.write0_read_back_from_gen _ _ _ _ (by decide) (by omega) (by decide),
      hcode, Reasoning.Theory.extract_append_left _ _ _ _ (by omega), hrt]
  rw [Fe.M.exec_bind (m := (sidecar.model .machine).init (ctorTail v)), Fe.M.exec_bind,
    initEntry_exec I w v hroom]
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [ir_init_run (fun m ic hs0 hs1 => ir_init m ic w₀ hs0 hs1 hwv hperm hsize hword), hret]
    simp [hwv, hperm]
    exact .ok_stop rfl rfl rfl
  · rw [ir_init_run (fun m ic _ _ => ir_init_value m ic w₀ hwv)]
    simp [hwv]
    exact .exit _

/-- The machine IR's constructor implements the exported one on one argument word. -/
theorem feScalarStoreImplementsDeploy :
    ImplementsDeploy Exported.contract (sidecar.model .machine) feScalarStoreCreationBytecode
      feScalarStoreBytecode .empty (fun args => ∃ v, args = ctorTail v) := by
  rintro I σ A feed args ⟨v, rfl⟩ hcode hperm
  exact ⟨feed, init_endsAs I _ v (by simp [World.init, UInt256.size]) hcode hperm⟩

/-- Deployment by the pinned creation bytecode with one ABI-encoded `uint256` argument refines
    the exported deployment entry at profile `P1`: the checker's certificate of the sidecar,
    whose init bytes are the pinned ones, composed with `feScalarStoreImplementsDeploy`. -/
theorem feScalarStoreDeployRefinesExportedP1 :
    RefinesDeploy .P1 feScalarStoreCreationBytecode feScalarStoreBytecode Exported.contract
      (fun args => ∃ v, args = ctorTail v) :=
  RefinesDeploy.of_implements (fun σ σ₀ g A I args _ hcode hperm =>
    sidecar_sound.2 σ σ₀ g A I args trivial (by rw [sidecar_init]; exact hcode) hperm)
    feScalarStoreImplementsDeploy

end FeProofs.ScalarStore.Sonatina
