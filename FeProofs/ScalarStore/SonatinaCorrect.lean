import FeProofs.ScalarStore.SonatinaRun
import FeProofs.ScalarStore.RuntimeCorrect

/-!
# FeScalarStore: the bytecode refines the exported contract at P1

The machine IR ends as the hand-written model does on each call (`model_endsAs`), so it
implements the exported contract (`feScalarStoreImplements`, through `runtime_endsAs`), and the
checker's certificate of the sidecar carries over to the exported contract at profile `P1`.
Deployment goes the same way (`init_ir_endsAs`, `feScalarStoreImplementsDeploy`): the init IR
reads its argument and the runtime it returns from its own code, the creation code with the
argument after it.
-/

namespace FeProofs.ScalarStore.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

variable (I : ExecutionEnv) (w : World)

/-- The machine IR's runtime ends as the hand-written model's does, on calldata below `2 ^ 64`
    bytes. -/
theorem model_endsAs (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs (Model.runtime.exec I w) ((sidecar.model .machine).runtime.exec I w) := by
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · have hlt : I.calldata.size < 4 := by omega
    rw [runtime_short hlt, ir_runtime (fun m ic => ir_short m ic I w hlt)]
    exact .exit _
  have hsel : ∀ (i : Fin 2) (k : Nat) (hk : k < UInt256.size),
      UInt256.eq (.ofNat k) (selWord I.calldata) =
        (if (feScalarStoreSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩) →
      (selIs I (feScalarStoreSelBytes i) ↔
        (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 = k) := by
    intro i k hk he
    rw [← selWord_toNat]
    constructor
    · intro h
      rw [selWord_hit he h, Check.toNat_ofNat_lt hk]
    · intro h
      by_contra hn
      exact selWord_miss he (by simpa [selIs] using hn)
        (Check.eq_of_toNat (by rw [h, Check.toNat_ofNat_lt hk]))
  have s0 := hsel 0 1627277233 (by decide) (setEvmSelector hsz)
  have s1 := hsel 1 1833756220 (by decide) (getEvmSelector hsz)
  have hbad := badHead_iff I.calldata 1 hfits
  by_cases h0 : selIs I (feScalarStoreSelBytes 0)
  · have hs := s0.mp h0
    by_cases hwv : I.weiValue = ⟨0⟩
    swap
    · rw [runtime_set_value hsz h0 hwv,
        ir_runtime (fun m ic => ir_set_value m ic w hsz hfits hs hwv)]
      exact .exit _
    by_cases hshort : I.calldata.size < 36
    · rw [runtime_set_head hsz h0 hwv (hbad.mpr (by omega)),
        ir_runtime (fun m ic => ir_set_head m ic w hsz hfits hs hwv hshort)]
      exact .exit _
    have hgood : ¬ BadHead I.calldata 1 := fun h => hshort (by have := hbad.mp h; omega)
    by_cases hperm : I.perm = true
    · rw [runtime_set hsz h0 hwv hgood hperm,
        ir_runtime (fun m ic => ir_set m ic w hsz hfits hs hwv (by omega) hperm)]
      exact .ok_stop rfl rfl rfl
    · rw [runtime_set_static hsz h0 hwv hgood (by simpa using hperm),
        ir_runtime (fun m ic => ir_set_static m ic w hsz hfits hs hwv (by omega)
          (by simpa using hperm))]
      exact .exit _
  have hn0 := mt s0.mpr h0
  by_cases h1 : selIs I (feScalarStoreSelBytes 1)
  · have hs := s1.mp h1
    by_cases hwv : I.weiValue = ⟨0⟩
    swap
    · rw [runtime_get_value hsz h0 h1 hwv,
        ir_runtime (fun m ic => ir_get_value m ic w hsz hfits hs hwv)]
      exact .exit _
    rw [runtime_get hsz h0 h1 hwv, ir_runtime (fun m ic => ir_get m ic w hsz hfits hs hwv)]
    exact .ok_stop rfl rfl rfl
  rw [runtime_noMatch hsz h0 h1,
    ir_runtime (fun m ic => ir_noMatch m ic w hsz hfits hn0 (mt s1.mpr h1))]
  exact .exit _

/-- The machine IR implements the exported contract on calldata below `2 ^ 64` bytes: it ends as
    the hand-written model does, which ends as the exported entry does. -/
theorem feScalarStoreImplements :
    Implements Exported.contract (sidecar.model .machine) CalldataFits :=
  fun I σ A feed hfits => ⟨feed, (Exported.runtime_endsAs I (World.init σ A feed)
    (by simp [World.init, UInt256.size]) hfits).trans (model_endsAs I _ hfits)⟩

/-- The runtime bytecode refines the exported contract at profile `P1`, on calldata below
    `2 ^ 64` bytes: the checker's certificate of the sidecar, whose runtime bytes are the
    pinned ones, composed with `feScalarStoreImplements`. -/
theorem feScalarStoreRefinesExportedP1 :
    RefinesOn .P1 feScalarStoreBytecode Exported.contract CalldataFits :=
  RefinesOn.of_implements (sidecar_runtime ▸ sidecar_sound.1) feScalarStoreImplements rfl

/-! ## Deployment -/

/-- The machine IR's constructor ends as the hand-written model's does, on one argument word
    after the pinned creation code. -/
theorem init_ir_endsAs (v : UInt256)
    (hcode : I.code = feScalarStoreCreationBytecode ++ ctorTail v) (hperm : I.perm = true) :
    EndsAs ((Model.init (ctorTail v) >>= fun _ => pure feScalarStoreBytecode).exec I w)
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
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [init_ok v hwv hperm, Fe.M.exec_bind, ir_init_run (fun m ic hs0 hs1 =>
      ir_init m ic w₀ hs0 hs1 hwv hperm hsize hword), hret]
    exact .ok_stop rfl rfl rfl
  · rw [init_value hwv, Fe.M.exec_bind, ir_init_run (fun m ic _ _ => ir_init_value m ic w₀ hwv)]
    exact .exit _

/-- The machine IR's constructor implements the exported one on one argument word: it ends as
    the hand-written model's does, which ends as the exported entry does. -/
theorem feScalarStoreImplementsDeploy :
    ImplementsDeploy Exported.contract (sidecar.model .machine) feScalarStoreCreationBytecode
      feScalarStoreBytecode .empty (fun args => ∃ v, args = ctorTail v) := by
  rintro I σ A feed args ⟨v, rfl⟩ hcode hperm
  exact ⟨feed, (Exported.init_endsAs v _ I (World.init σ A feed)
    (by simp [World.init, UInt256.size])).trans (init_ir_endsAs I _ v hcode hperm)⟩

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
