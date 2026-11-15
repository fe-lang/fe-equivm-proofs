import FeProofs.ERC20.SonatinaArms
import FeProofs.ERC20.SonatinaTransfer
import FeProofs.ERC20.SonatinaTransferFrom

/-!
# FeERC20: the bytecode the pinned Fe commit compiles refines the exported contract at P1

The machine IR's runtime ends as the exported runtime entry does on each call
(`runtime_endsAs`): the dispatcher's selector test is the exported one (`selWord_eq_iff`), the
machine IR goes on at the arm's entry block (`ir_dispatch`), and each arm ends as the exported
arm entry does (`SonatinaArms.lean`, `SonatinaTransfer.lean`, `SonatinaTransferFrom.lean`).
The constructor goes the same way (`init_endsAs`).  The checker's certificate of the sidecar
then carries over to the exported contract at profile `P1`.

These certificates are of `P1/runtime.hex` and `P1/creation.hex`, the bytecode the pinned Fe
commit compiles (`P1/FeERC20.build.json`); the P0 certificates (`RuntimeCorrect.lean`) are of an
older compiler's (`FeERC20.build.json`).  `Exported.contract` is the model of both.
-/

namespace FeProofs.ERC20.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina
open Exported (decodeTransfer_exec decodeApprove_exec decodeTransferFrom_exec
  decodeBalanceOf_exec decodeAllowance_exec decodeTotalSupply_exec initEntry_exec)

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/- The exported constructor and the primitives it reaches unfold under `simp` here; the arms'
   entries do not, so that the dispatcher's goes to them. -/
attribute [local simp] Exported.balancesField Exported.allowancesField Exported.supplyField
  Place.storage store load sload entry exec_nonPayable exec_sstore

/-- The room a step of an exported arm needs, from the room the arm has. -/
local macro "room" : tactic =>
  `(tactic| ((try simp only [keyed_size, returned_size, FeProofs.Lib.withArg_size]); omega))

/-- The machine IR's runtime, run from its entry block: the runtime section names no free
    pointer, so there is no prologue. -/
theorem ir_runtime_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    (h : ∀ m ic, EndsAs X (Check.endRun ((runBlocks m ic runtimeFunc ∅ none 0).exec I w))) :
    EndsAs X ((sidecar.model .machine).runtime.exec I w) := by
  rw [show (sidecar.model .machine).runtime = sidecar.runSection "runtime" .machine from rfl,
    Check.runSection_eq (f := runtimeFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simpa using h _ _

set_option maxHeartbeats 4000000 in
/-- The machine IR's runtime ends as the exported runtime entry does, on calldata below `2 ^ 64`
    bytes. -/
theorem runtime_endsAs (hmem : w.memory.size + 1024 < UInt256.size)
    (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry Exported.runtime).exec I w) ((sidecar.model .machine).runtime.exec I w) := by
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    Reasoning.Theory.ulit_toNat' _ (by unfold UInt256.size; omega)
  apply ir_runtime_endsAs
  intro m ic
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · rw [entry_exec (f := .revert .empty) (by
        simp [Exported.runtime, hn, show I.calldata.size < 4 by omega]),
      ir_short m ic I w (by omega)]
    exact .exit _
  have hn4 : ¬ I.calldata.size < 4 := by omega
  -- An arm: the exported dispatcher goes to its entry, the machine IR to its block.
  have arm : ∀ {k b : Nat} {e : FeM Empty}, (k, b) ∈ [(0x095ea7b3, 5), (0x18160ddd, 12),
      (0x23b872dd, 15), (0x70a08231, 33), (0xa9059cbb, 40), (0xdd62ed3e, 54)] →
      k < UInt256.size → selWord I.calldata = UInt256.ofNat k →
      (entry Exported.runtime).exec I w = (entry e).exec I w →
      (∀ E p, EndsAs ((entry e).exec I w)
        (Check.endRun ((runBlocks m ic runtimeFunc E p b).exec I w))) →
      EndsAs ((entry Exported.runtime).exec I w)
        (Check.endRun ((runBlocks m ic runtimeFunc ∅ none 0).exec I w)) := by
    intro k b e hk hkb hs he harm
    obtain ⟨E, p, hr⟩ := ir_dispatch m ic I w hsz hfits hk ((selWord_eq_iff hkb).mp hs)
    rw [he, hr]
    exact harm E p
  have hne : ∀ {a b : Nat}, a ≠ b → a < UInt256.size → b < UInt256.size →
      UInt256.ofNat a ≠ UInt256.ofNat b := fun hab ha hb h =>
    hab (by simpa [Check.toNat_ofNat_lt ha, Check.toNat_ofNat_lt hb] using
      congrArg UInt256.toNat h)
  -- The selector words differ.
  have hd : ∀ a b : Nat, a ≠ b → a < UInt256.size → b < UInt256.size →
      (UInt256.ofNat a = UInt256.ofNat b) = False := fun a b hab ha hb =>
    eq_false (hne hab ha hb)
  by_cases h1 : selWord I.calldata = UInt256.ofNat 0x095ea7b3
  · exact arm (by simp) (by decide) h1 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h1])
      (arm_approve m ic w hsz hfits (by omega))
  by_cases h2 : selWord I.calldata = UInt256.ofNat 0x18160ddd
  · exact arm (by simp) (by decide) h2 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h2,
        hd 0x18160ddd 0x095ea7b3 (by decide) (by decide) (by decide)])
      (arm_totalSupply m ic I w (by omega))
  by_cases h3 : selWord I.calldata = UInt256.ofNat 0x23b872dd
  · exact arm (by simp) (by decide) h3 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h3,
        hd 0x23b872dd 0x095ea7b3 (by decide) (by decide) (by decide),
        hd 0x23b872dd 0x18160ddd (by decide) (by decide) (by decide)])
      (arm_transferFrom m ic w hsz hfits hmem)
  by_cases h4 : selWord I.calldata = UInt256.ofNat 0x70a08231
  · exact arm (by simp) (by decide) h4 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h4,
        hd 0x70a08231 0x095ea7b3 (by decide) (by decide) (by decide),
        hd 0x70a08231 0x18160ddd (by decide) (by decide) (by decide),
        hd 0x70a08231 0x23b872dd (by decide) (by decide) (by decide)])
      (arm_balanceOf m ic w hsz hfits (by omega))
  by_cases h5 : selWord I.calldata = UInt256.ofNat 0xa9059cbb
  · exact arm (by simp) (by decide) h5 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h5,
        hd 0xa9059cbb 0x095ea7b3 (by decide) (by decide) (by decide),
        hd 0xa9059cbb 0x18160ddd (by decide) (by decide) (by decide),
        hd 0xa9059cbb 0x23b872dd (by decide) (by decide) (by decide),
        hd 0xa9059cbb 0x70a08231 (by decide) (by decide) (by decide)])
      (arm_transfer m ic w hsz hfits (by omega))
  by_cases h6 : selWord I.calldata = UInt256.ofNat 0xdd62ed3e
  · exact arm (by simp) (by decide) h6 (by
      simp [Exported.runtime, entry, hn, hn4, selector_exec, h6,
        hd 0xdd62ed3e 0x095ea7b3 (by decide) (by decide) (by decide),
        hd 0xdd62ed3e 0x18160ddd (by decide) (by decide) (by decide),
        hd 0xdd62ed3e 0x23b872dd (by decide) (by decide) (by decide),
        hd 0xdd62ed3e 0x70a08231 (by decide) (by decide) (by decide),
        hd 0xdd62ed3e 0xa9059cbb (by decide) (by decide) (by decide)])
      (arm_allowance m ic w hsz hfits (by omega))
  rw [entry_exec (f := .revert .empty) (by
      simp [Exported.runtime, hn, hn4, selector_exec, h1, h2, h3, h4, h5, h6]),
    ir_noMatch m ic I w hsz hfits (by
      intro k hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact fun h => by
          first
          | exact h1 ((selWord_eq_iff (by decide)).mpr h)
          | exact h2 ((selWord_eq_iff (by decide)).mpr h)
          | exact h3 ((selWord_eq_iff (by decide)).mpr h)
          | exact h4 ((selWord_eq_iff (by decide)).mpr h)
          | exact h5 ((selWord_eq_iff (by decide)).mpr h)
          | exact h6 ((selWord_eq_iff (by decide)).mpr h))]
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

/-- The machine IR's constructor: the prologue stores the free pointer 160 at address 64, then
    the init function runs from its entry block, with the symbols of the init section. -/
theorem ir_init_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    {args : ByteArray}
    (h : ∀ m ic, ic.symbol "." = some (0, 986) → ic.symbol "&FeERC20_runtime" = some (124, 862) →
      EndsAs X (Check.endRun ((runBlocks m ic initFunc ∅ none 0).exec I
        { w with memory := (UInt256.ofNat 160).toByteArray.write 0 w.memory 64 32 }))) :
    EndsAs X (((sidecar.model .machine).init args).exec I w) := by
  rw [show (sidecar.model .machine).init args = sidecar.runSection "init" .machine from rfl,
    Check.runSection_eq (f := initFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simp [Fe.EVM.mstore, Check.toNat_ofNat, UInt256.size]
  exact h _ _ rfl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The machine IR's constructor ends as the exported deployment entry does, on one argument
    word after `P1/creation.hex`. -/
theorem init_endsAs (v : UInt256) (hroom : w.memory.size + 256 < UInt256.size)
    (hcode : I.code = feERC20P1CreationBytecode ++ ctorTail v) (hperm : I.perm = true) :
    EndsAs ((Exported.init_entry (ctorTail v) >>= fun tail =>
        pure (feERC20P1Bytecode ++ tail)).exec I w)
      (((sidecar.model .machine).init (ctorTail v) >>= fun tail =>
        pure (ByteArray.empty ++ tail)).exec I w) := by
  obtain ⟨hrt, hcs⟩ := creation_runtime
  have hts : (ctorTail v).size = 32 := Reasoning.Theory.word_toBytesBE_toByteArray_size v
  have hsize : I.code.size = 1018 := by rw [hcode, ByteArray.size_append, hcs, hts]
  have harg : I.code.extract 986 1018 = v.toByteArray := by
    rw [hcode, Reasoning.Theory.extract_append_right_window _ _ _ _ (by omega), hcs]
    show (ctorTail v).extract 0 32 = _
    rw [← hts, Reasoning.Theory.byteArray_extract_self, Exported.ctorTail_eq]
  have hcopy : ∀ M, I.code.write 986 M 160 32 = v.toByteArray.write 0 M 160 32 := fun M => by
    rw [write_window _ _ _ _ _ (by decide) (by omega), harg]
  have hret : ∀ M, (I.code.write 124 M 0 862).readWithPadding 0 862 = feERC20P1Bytecode := by
    intro M
    rw [Reasoning.Theory.write0_read_back_from_gen _ _ _ _ (by decide) (by omega) (by decide),
      hcode, Reasoning.Theory.extract_append_left _ _ _ _ (by omega), hrt]
  have hgap : ∀ (M : ByteArray) (off : Nat), off < 2 ^ 32 → off - M.size < USize.size :=
    fun M off h => lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le h USize.le_size)
  have hread : ∀ (M : ByteArray) (u : UInt256) (off : Nat), off < 2 ^ 32 →
      (u.toByteArray.write 0 M off 32).readWithPadding off 32 = u.toByteArray :=
    fun M u off h => Reasoning.Theory.toByteArray_write_read_back_of_gap u M off (hgap M off h)
  have h96 : ∀ (M : ByteArray) (u : UInt256), 96 ≤ (u.toByteArray.write 0 M 160 32).size :=
    fun M u => le_trans (by decide)
      (Reasoning.Theory.toByteArray_write_size_ge_off_add32 u M 160 (hgap M 160 (by decide)))
  clear hcode
  rw [init_bind_eq]
  apply ir_init_endsAs
  intro m ic hs0 hs1
  rw [Fe.M.exec_bind, initEntry_exec I w v (by omega)]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hv : I.weiValue.toNat = 0 := by rw [hwv]; rfl
    simp (disch := room) [hwv, Exported.init, Exported.Evm_caller, Exported.Address_zero,
      FeProofs.Lib.locateAddress_exec, Exported.emitTransferLit_exec, hperm]
    split_ifs with hroom
    swap
    · exact absurd (by simp only [keyed_size, FeProofs.Lib.withArg_size]; omega) hroom
    simp
    repeat ir_step [wrap, hcopy, hread, h96, hret, pair_slot_at,
      Reasoning.Theory.uInt256OfByteArray_toByteArray]
    exact .ok_stop rfl rfl rfl
  · have hv : I.weiValue.toNat ≠ 0 := fun h => hwv (Check.eq_of_toNat (by simpa using h))
    simp [hwv]
    repeat ir_step
    exact .exit _

/-! ## The certificates -/

/-- The machine IR implements the exported contract on calldata below `2 ^ 64` bytes. -/
theorem feERC20Implements :
    Implements Exported.contract (sidecar.model .machine) CalldataFits :=
  fun I σ A feed _ hfits => ⟨feed, runtime_endsAs I (World.init σ A feed)
    (by simp [World.init, UInt256.size]) hfits⟩

/-- The machine IR's constructor implements the exported one on one argument word. -/
theorem feERC20ImplementsDeploy :
    ImplementsDeploy Exported.contract (sidecar.model .machine) feERC20P1CreationBytecode
      feERC20P1Bytecode .empty (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro I σ A feed args ⟨v, rfl⟩ hcode _ hperm
  exact ⟨feed, init_endsAs I _ v (by simp [World.init, UInt256.size]) hcode hperm⟩

/-- `P1/runtime.hex` refines the exported contract at profile `P1`, on calldata below `2 ^ 64`
    bytes: the checker's certificate of the sidecar, whose runtime bytes are these, composed
    with `feERC20Implements`. -/
theorem feERC20RefinesExportedP1 :
    RefinesOn .P1 feERC20P1Bytecode Exported.contract CalldataFits :=
  RefinesOn.of_implements (sidecar_runtime ▸ sidecar_sound.1) feERC20Implements rfl

/-- Deployment by `P1/creation.hex` with one ABI-encoded `uint256` argument refines the exported
    deployment entry at profile `P1`. -/
theorem feERC20DeployRefinesExportedP1 :
    RefinesDeploy .P1 feERC20P1CreationBytecode feERC20P1Bytecode Exported.contract
      (fun args => ∃ v : UInt256, args = ctorTail v) :=
  RefinesDeploy.of_implements (fun σ σ₀ g A I args _ hcode hown hperm =>
    sidecar_sound.2 σ σ₀ g A I args trivial (by rw [sidecar_init]; exact hcode) hown hperm)
    feERC20ImplementsDeploy

end FeProofs.ERC20.Sonatina
