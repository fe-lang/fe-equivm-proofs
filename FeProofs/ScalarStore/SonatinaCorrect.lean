import FeProofs.ScalarStore.SonatinaRun
import FeProofs.ScalarStore.RuntimeCorrect

/-!
# FeScalarStore: the bytecode refines the exported contract at P1

The machine IR ends as the hand-written model does on each call (`model_endsAs`), so it
implements the exported contract (`feScalarStoreImplements`, through `runtime_endsAs`), and the
checker's certificate of the sidecar carries over to the exported contract at profile `P1`.
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

end FeProofs.ScalarStore.Sonatina
