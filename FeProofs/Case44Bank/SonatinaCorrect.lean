import FeProofs.Case44Bank.SonatinaRun
import FeProofs.Case44Bank.ExportedStd

/-!
# Case44Bank: the bytecode refines the exported contract at P1

The machine IR's runtime ends as the exported runtime entry does on each call
(`runtime_endsAs`), on storage that has an account at the code owner, and its constructor as
the exported deployment entry does (`init_endsAs`), so the machine IR implements the exported
contract and the checker's certificate of the sidecar carries over to it at profile `P1`
(`feCase44BankRefinesExportedP1`, `feCase44BankDeployRefinesExportedP1`).  It is the first
certificate of a contract whose runtime makes an internal call.

The runtime calls `credit` twice.  Each side has one lemma about its `credit` from any world
and arguments (`Exported.credit_exec`, `ir_credit`), which both call sites rewrite with; the
arm (`arm_credit`) case-splits on the overflow of each checked addition, in the order both
sides make them, and closes each case by an `EndsAs` constructor.  The two sides differ in one
place: after storing the total, the exported arm loads it back, and the machine IR uses the word
it stored (Sonatina forwards the store to the load).  They agree when the store takes effect,
which `storeWord` does only when the account map has an account at the code owner
(`slotWord_storeWord`); without one, the exported arm reads the total as 0 and the machine IR
does not, so the account is a hypothesis of `runtime_endsAs`.
-/

namespace FeProofs.Case44Bank.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

/-! ## The arm -/

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/- The exported arm entry, its arm and the primitives they reach unfold under `simp` here. -/
attribute [local simp] Exported.recv0_arm0_entry Exported.recv0_arm0 Exported.balancesField
  Exported.totalField Place.storage store load sload entry exec_nonPayable exec_sstore

/-- The room a step of the exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size]); omega))

/-! The words of a `Credit` call and the storage each step of the arm leaves, as both sides
compute them. -/
set_option hygiene false in
local notation "cWho" => uInt256OfByteArray (I.calldata.readBytes 4 32)
set_option hygiene false in
local notation "cAmt" => uInt256OfByteArray (I.calldata.readBytes 36 32)
set_option hygiene false in
local notation "cSlot" => mapSlot cWho ⟨0⟩
set_option hygiene false in
local notation "cσ₁" =>
  storeWord I.codeOwner w.accounts cSlot (slotWord I w.accounts cSlot + cAmt)
set_option hygiene false in
local notation "cσ₂" => storeWord I.codeOwner cσ₁ cSlot (slotWord I cσ₁ cSlot + cAmt)
set_option hygiene false in
local notation "cTot" => slotWord I cσ₂ (UInt256.ofNat 1)
set_option hygiene false in
local notation "cσ₃" => storeWord I.codeOwner cσ₂ (UInt256.ofNat 1) (cTot + cAmt)

section Arm

variable {I} (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64)
include hsz hfits

set_option maxHeartbeats 8000000 in
/-- `Credit`: the exported arm entry ends as the machine IR's run from the arm's entry block
    does, from any environment, on storage that has an account at the code owner.  Each call of
    `credit` is the callee's lemma (`Exported.credit_exec` on the exported side, `ir_credit` on
    the machine IR's), rewritten at both call sites under the case split on its overflow. -/
theorem arm_credit (hm : m.func? "credit" = some creditFunc)
    (hown : ∃ acc, w.accounts.get? I.codeOwner = some acc)
    (hmem : w.memory.size + 512 < UInt256.size) (E : Sonatina.Env) (p : Option Nat) :
    EndsAs ((entry Exported.recv0_arm0_entry).exec I w)
      (Check.endRun ((runBlocks m ic runtimeFunc E p 5).exec I w)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  have hdec := Exported.decodeCredit_exec I w hsz hfits
  have hc := fun w => ir_credit m ic I w hm
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _
  have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
  by_cases hshort : I.calldata.size < 68
  · have hlt : (I.calldata.size : Int) - 4 < 64 := by omega
    simp [hwv, hdec, hshort]
    repeat ir_step
    exact .exit _
  have hlt : ¬ (I.calldata.size : Int) - 4 < 64 := by omega
  by_cases hna : NotAddress (Fe.EVM.word I.calldata 4)
  · have ha := (notAddress_iff _).mp hna
    simp only [Fe.EVM.word] at ha
    simp [hwv, hdec, hshort, hna]
    repeat ir_step
    exact .exit _
  have ha : (Fe.EVM.word I.calldata 4).toNat >>> 160 = 0 := by
    by_contra h; exact hna ((notAddress_iff _).mpr h)
  simp only [Fe.EVM.word] at ha hdec hna
  -- The first credit's check.
  by_cases o1 : UInt256.size ≤ (slotWord I w.accounts (mapSlot
      (uInt256OfByteArray (I.calldata.readBytes 4 32)) ⟨0⟩)).toNat +
      (uInt256OfByteArray (I.calldata.readBytes 36 32)).toNat
  · have o1L := o1
    simp only [UInt256.size] at o1L
    simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1]
    repeat ir_step
    exact .panic_revert 17
  have o1L := o1
  simp only [UInt256.size] at o1L
  by_cases hperm : I.perm = true
  swap
  · simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1,
      hperm]
    repeat ir_step
    exact .exit _
  -- The second credit's check, on the storage the first leaves.
  by_cases o2 : UInt256.size ≤ (slotWord I cσ₁ cSlot).toNat + (cAmt).toNat
  · have o2L := o2
    simp only [UInt256.size] at o2L
    simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1,
      hperm, o2]
    repeat ir_step
    exact .panic_revert 17
  have o2L := o2
  simp only [UInt256.size] at o2L
  -- The total's check.
  by_cases o3 : UInt256.size ≤ (cTot).toNat + (cAmt).toNat
  · have o3L := o3
    simp only [UInt256.size] at o3L
    simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1,
      hperm, o2, checkedAdd, o3]
    repeat ir_step
    exact .panic_revert 17
  have o3L := o3
  simp only [UInt256.size] at o3L
  -- The exported arm reads the total back; the machine IR uses the word it stored.
  have hown₂ : ∃ acc, (cσ₂).get? I.codeOwner = some acc :=
    storeWord_owner (storeWord_owner hown)
  have hfwd := fun v => slotWord_storeWord (k := UInt256.ofNat 1) (v := v) hown₂
  by_cases o4 : UInt256.size ≤ (slotWord I cσ₃ cSlot).toNat + (cTot + cAmt).toNat
  · have o4L := o4
    simp only [UInt256.size] at o4L
    simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1,
      hperm, o2, checkedAdd, o3, FeProofs.Lib.locateAddress_exec, hfwd, o4]
    repeat ir_step [wrap_add_toNat, add_toNat_lt]
    exact .panic_revert 17
  have o4L := o4
  simp only [UInt256.size] at o4L
  simp (disch := room) [hwv, hdec, hshort, hna, Exported.credit_exec, ofNat_zero_eq, o1,
    hperm, o2, checkedAdd, o3, FeProofs.Lib.locateAddress_exec, hfwd, o4,
    FeProofs.Lib.returnU256_exec]
  repeat ir_step [wrap_add_toNat, add_toNat_lt]
  exact .stop_stop rfl rfl rfl

end Arm

/-! ## The runtime -/

/-- The machine IR's runtime, run from its entry block in the runtime section's module, whose
    `credit` is `creditFunc`: the runtime section names no free pointer, so there is no
    prologue. -/
theorem ir_runtime_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    (h : ∀ m ic, m.func? "credit" = some creditFunc →
      EndsAs X (Check.endRun ((runBlocks m ic runtimeFunc ∅ none 0).exec I w))) :
    EndsAs X ((sidecar.model .machine).runtime.exec I w) := by
  rw [show (sidecar.model .machine).runtime = sidecar.runSection "runtime" .machine from rfl,
    Check.runSection_eq (f := runtimeFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simp
  exact h _ _ (by rfl)

/-- The machine IR's runtime ends as the exported runtime entry does, on calldata below `2 ^ 64`
    bytes and storage that has an account at the code owner. -/
theorem runtime_endsAs (hown : OwnerExists w.accounts I)
    (hmem : w.memory.size + 512 < UInt256.size) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry Exported.runtime).exec I w) ((sidecar.model .machine).runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    Reasoning.Theory.ulit_toNat' _ (by unfold UInt256.size; omega)
  apply ir_runtime_endsAs
  intro m ic hm
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · rw [entry_exec (f := .revert .empty) (by
        simp [Exported.runtime, hn, show I.calldata.size < 4 by omega]),
      ir_short m ic I w (by omega)]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := by omega
  by_cases h1 : selWord I.calldata = UInt256.ofNat 0x00000001
  · obtain ⟨E, p, hr⟩ := ir_dispatch m ic I w hsz hfits ((selWord_eq_iff (by decide)).mp h1)
    rw [show (entry Exported.runtime).exec I w = (entry Exported.recv0_arm0_entry).exec I w by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h1], hr]
    exact arm_credit m ic w hsz hfits hm (ownerExists_iff_get?.mp hown) hmem E p
  rw [entry_exec (f := .revert .empty) (by
      simp [Exported.runtime, hn, hn4, selector_exec, h1]),
    ir_noMatch m ic I w hsz hfits (fun h => h1 ((selWord_eq_iff (by decide)).mpr h))]
  exact .exit _

/-! ## Deployment -/

/-- A section's run never returns, so what follows it does not run. -/
theorem init_bind_eq (args : ByteArray) (g : ByteArray → FeM ByteArray) :
    (((sidecar.model .machine).init args) >>= g).exec I w =
      ((sidecar.model .machine).init args).exec I w := by
  rw [Fe.M.exec_bind]
  cases h : ((sidecar.model .machine).init args).exec I w with
  | none => rfl
  | some x =>
    cases x with
    | error e => rfl
    | ok p => exact absurd h (Check.runSection_not_ok sidecar "init" .machine I w p.1 p.2)

/-- The machine IR's constructor: the init section names no free pointer, so the init function
    runs from its entry block, with the symbols of the init section. -/
theorem ir_init_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    {args : ByteArray}
    (h : ∀ m ic, ic.symbol "&Case44Bank_runtime" = some (19, 176) →
      EndsAs X (Check.endRun ((runBlocks m ic initFunc ∅ none 0).exec I w))) :
    EndsAs X (((sidecar.model .machine).init args).exec I w) := by
  rw [show (sidecar.model .machine).init args = sidecar.runSection "init" .machine from rfl,
    Check.runSection_eq (f := initFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simp
  exact h _ _ rfl

/-- The machine IR's constructor ends as the exported deployment entry does, on any argument
    bytes after the pinned creation code: neither reads them, and both return the runtime
    code. -/
theorem init_endsAs (args : ByteArray) (hcode : I.code = case44BankCreationBytecode ++ args) :
    EndsAs ((Exported.init_entry args >>= fun tail =>
        pure (case44BankBytecode ++ tail)).exec I w)
      (((sidecar.model .machine).init args >>= fun tail =>
        pure (ByteArray.empty ++ tail)).exec I w) := by
  obtain ⟨hrt, hcs⟩ := creation_runtime
  have hsize : 195 ≤ I.code.size := by rw [hcode, ByteArray.size_append, hcs]; omega
  have hret : ∀ M, (I.code.write 19 M 0 176).readWithPadding 0 176 = case44BankBytecode := by
    intro M
    rw [Reasoning.Theory.write0_read_back_from_gen _ _ _ _ (by decide) (by omega) (by decide),
      hcode, Reasoning.Theory.extract_append_left _ _ _ _ (by omega), hrt]
  rw [init_bind_eq, Fe.M.exec_bind, Exported.initEntry_exec]
  apply ir_init_endsAs
  intro m ic hs
  by_cases hwv : I.weiValue = ⟨0⟩
  · rw [ir_init m ic I w hs hwv, hret]
    simp [hwv]
    exact .ok_stop rfl rfl rfl
  · rw [ir_init_value m ic I w hwv]
    simp [hwv]
    exact .exit _

/-! ## The certificates -/

/-- The machine IR implements the exported contract on calldata below `2 ^ 64` bytes, at an
    account that exists. -/
theorem feCase44BankImplements :
    Implements Exported.contract (sidecar.model .machine) CalldataFits :=
  fun I σ A feed hown hfits => ⟨feed, runtime_endsAs I (World.init σ A feed) hown
    (by simp [World.init, UInt256.size]) hfits⟩

/-- The machine IR's constructor implements the exported one on the empty argument string: the
    constructor takes no arguments. -/
theorem feCase44BankImplementsDeploy :
    ImplementsDeploy Exported.contract (sidecar.model .machine) case44BankCreationBytecode
      case44BankBytecode .empty (fun args => args = ByteArray.empty) := by
  rintro I σ A feed args - hcode - -
  exact ⟨feed, init_endsAs I _ args hcode⟩

/-- The runtime bytecode refines the exported contract at profile `P1`, on calldata below
    `2 ^ 64` bytes at an account that exists: the checker's certificate of the sidecar, whose
    runtime bytes are the pinned ones, composed with `feCase44BankImplements`. -/
theorem feCase44BankRefinesExportedP1 :
    RefinesOn .P1 case44BankBytecode Exported.contract CalldataFits :=
  RefinesOn.of_implements (sidecar_runtime ▸ sidecar_sound.1) feCase44BankImplements rfl

/-- Deployment by the pinned creation bytecode with no arguments refines the exported deployment
    entry at profile `P1`. -/
theorem feCase44BankDeployRefinesExportedP1 :
    RefinesDeploy .P1 case44BankCreationBytecode case44BankBytecode Exported.contract
      (fun args => args = ByteArray.empty) :=
  RefinesDeploy.of_implements (fun σ σ₀ g A I args _ hcode hown hperm =>
    sidecar_sound.2 σ σ₀ g A I args trivial (by rw [sidecar_init]; exact hcode) hown hperm)
    feCase44BankImplementsDeploy

end FeProofs.Case44Bank.Sonatina
