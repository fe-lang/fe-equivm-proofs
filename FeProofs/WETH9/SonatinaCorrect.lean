import FeProofs.WETH9.SonatinaArms
import FeProofs.WETH9.SonatinaTransfer
import FeProofs.WETH9.SonatinaWithdraw
import FeProofs.WETH9.SonatinaString
import FeProofs.WETH9.SonatinaInit

/-!
# FeWETH9: the pinned bytecode refines the exported contract at P1

The machine IR's runtime ends as the exported runtime entry does on each call
(`runtime_endsAs`): the dispatcher's selector tests are the exported ones (`selWord_eq_iff`), the
machine IR goes on at the arm's entry block (`ir_dispatch`) or at the fallback's
(`ir_fallback`), and each arm ends as the exported arm entry does (`SonatinaArms.lean`,
`SonatinaTransfer.lean`, `SonatinaWithdraw.lean`, `SonatinaString.lean`).  The constructor goes the same way (`init_endsAs`, `SonatinaInit.lean`).  The checker's
certificate of the sidecar then carries over to the exported contract at profile `P1`.
-/

namespace FeProofs.WETH9.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/- Mathlib's `bind` and `map` lemmas of other monads, and `le_of_subsingleton`, which searches
   for a `Subsingleton` instance at every `≤`, only slow `simp` down here. -/
attribute [-simp] Filter.bind_def List.bind_eq_flatMap Part.bind_eq_bind Set.bind_def
  Option.bind_eq_bind Filter.map_def List.map_eq_map Option.map_eq_map Part.map_eq_map
  Set.fmap_eq_image le_of_subsingleton

variable (m : Module) (ic : Fe.Sonatina.Ctx) (I : ExecutionEnv) (w : World)

/-- The selector as the machine IR computes it. -/
abbrev sel : Nat := (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224

/-- The selectors of the arms and their entry blocks in the machine IR. -/
abbrev armTable : List (Nat × Nat) :=
  [(0x06fdde03, 5), (0x095ea7b3, 8), (0x18160ddd, 15), (0x23b872dd, 18), (0x2e1a7d4d, 27),
    (0x313ce567, 39), (0x70a08231, 42), (0x95d89b41, 49), (0xa9059cbb, 52), (0xd0e30db0, 59),
    (0xdd62ed3e, 60)]

set_option maxHeartbeats 8000000 in
/-- The dispatcher: on a selector of the table, the run goes on at the arm's entry block. -/
theorem ir_dispatch (hsz : 4 ≤ I.calldata.size) (hfits : I.calldata.size < 2 ^ 64) {k b : Nat}
    (hk : (k, b) ∈ armTable) (hsel : sel I = k) :
    ∃ E p, (runBlocks m ic runtimeFunc ∅ none 0).exec I w =
      (runBlocks m ic runtimeFunc E p b).exec I w := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts hsz hfits
  unfold sel at hsel
  simp only [armTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, _, by ir_step; ir_step; ir_step; ir_step; rfl⟩

set_option maxHeartbeats 8000000 in
/-- Calldata too short for a selector, or a selector of no arm: the run goes on at the
    fallback's block. -/
theorem ir_fallback (hfits : I.calldata.size < 2 ^ 64)
    (h : I.calldata.size < 4 ∨ ∀ k ∈ armTable.map (·.1), sel I ≠ k) :
    ∃ E p, (runBlocks m ic runtimeFunc ∅ none 0).exec I w =
      (runBlocks m ic runtimeFunc E p 4).exec I w := by
  have h' : I.calldata.size % UInt256.size = I.calldata.size :=
    Nat.mod_eq_of_lt (by unfold UInt256.size; omega)
  simp only [UInt256.size] at h'
  by_cases hs : I.calldata.size < 4
  · exact ⟨_, _, by ir_step; ir_step; rfl⟩
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := calldata_facts (by omega) hfits
  have h := h.resolve_left hs
  simp only [armTable, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  unfold sel at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4
  have := Ne.symm h5; have := Ne.symm h6; have := Ne.symm h7; have := Ne.symm h8
  have := Ne.symm h9; have := Ne.symm h10; have := Ne.symm h11
  by_cases hl1 : (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 < 826074471
  · by_cases hl2 : (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 < 404098525
    · exact ⟨_, _, by ir_step; ir_step; ir_step; ir_step; ir_step; rfl⟩
    · exact ⟨_, _, by ir_step; ir_step; ir_step; ir_step; ir_step; rfl⟩
  · by_cases hl2 : (uInt256OfByteArray (I.calldata.readBytes 0 32)).toNat >>> 224 < 2835717307
    · exact ⟨_, _, by ir_step; ir_step; ir_step; ir_step; ir_step; rfl⟩
    · exact ⟨_, _, by ir_step; ir_step; ir_step; ir_step; ir_step; rfl⟩

/-- `UInt256.ofNat` of two values below `2 ^ 256` is equal exactly when they are. -/
theorem ofNat_eq_iff {a b : Nat} : UInt256.ofNat a = UInt256.ofNat b ↔ a % UInt256.size = b % UInt256.size :=
  ⟨fun h => by simpa [Check.toNat_ofNat] using congrArg UInt256.toNat h,
    fun h => Check.eq_of_toNat (by simpa [Check.toNat_ofNat] using h)⟩

/-- The machine IR's runtime: the prologue stores the free pointer 224 at address 64, then the
    root runs from its entry block. -/
theorem ir_runtime_endsAs {X : Option (Except (Fe.Exit World) (ByteArray × World))}
    (h : ∀ m ic, m.func? "deposit" = some depositFunc → m.func? "load" = some loadFunc →
      m.func? "stored_len" = some storedLenFunc → m.func? "revert_error" = some revertErrorFunc →
      m.func? "return_value__g7f54" = some returnValueFunc →
      m.func? "transfer_from" = some transferFromFunc →
      EndsAs X (Check.endRun ((runBlocks m ic runtimeFunc ∅ none 0).exec I
        { w with memory := runtimeMem w.memory }))) :
    EndsAs X ((sidecar.model .machine).runtime.exec I w) := by
  rw [show (sidecar.model .machine).runtime = sidecar.runSection "runtime" .machine from rfl,
    Check.runSection_eq (f := runtimeFunc) rfl rfl rfl rfl rfl rfl rfl]
  simp only [Check.pre, if_pos, Fe.M.exec_bind]
  simp [Fe.EVM.mstore, Check.toNat_ofNat, UInt256.size]
  exact h _ _ rfl rfl rfl rfl rfl rfl

set_option maxHeartbeats 16000000 in
/-- The machine IR's runtime ends as the exported runtime entry does, on calldata below `2 ^ 64`
    bytes, from the empty memory a call starts with. -/
theorem runtime_endsAs (hw : w.memory = ByteArray.empty) (hfits : I.calldata.size < 2 ^ 64) :
    EndsAs ((entry Exported.runtime).exec I w) ((sidecar.model .machine).runtime.exec I w) := by
  have hmem : w.memory.size + 1024 < UInt256.size := by rw [hw]; decide
  have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    Reasoning.Theory.ulit_toNat' _ (by unfold UInt256.size; omega)
  apply ir_runtime_endsAs
  intro m ic hdep hl hs hr hrv htf
  have fb : (entry Exported.runtime).exec I w = (entry Exported.recv1_arm0_entry).exec I w →
      (I.calldata.size < 4 ∨ ∀ k ∈ armTable.map (·.1), sel I ≠ k) →
      EndsAs ((entry Exported.runtime).exec I w) (Check.endRun ((runBlocks m ic runtimeFunc ∅
        none 0).exec I { w with memory := runtimeMem w.memory })) := by
    intro he h
    obtain ⟨E, p, hr⟩ := ir_fallback m ic I { w with memory := runtimeMem w.memory } hfits h
    rw [he, hr]
    exact arm_fallback ic I w hdep (by omega) _ E p
  by_cases hsz : 4 ≤ I.calldata.size
  swap
  · exact fb (by simp [Exported.runtime, entry, hn, show I.calldata.size < 4 by omega])
      (.inl (by omega))
  have hn4 : ¬ I.calldata.size < 4 := by omega
  have arm : ∀ {k b : Nat} {e : FeM Empty}, (k, b) ∈ armTable →
      k < UInt256.size → selWord I.calldata = UInt256.ofNat k →
      (entry Exported.runtime).exec I w = (entry e).exec I w →
      (∀ E p, EndsAs ((entry e).exec I w)
        (Check.endRun ((runBlocks m ic runtimeFunc E p b).exec I
          { w with memory := runtimeMem w.memory }))) →
      EndsAs ((entry Exported.runtime).exec I w)
        (Check.endRun ((runBlocks m ic runtimeFunc ∅ none 0).exec I
          { w with memory := runtimeMem w.memory })) := by
    intro k b e hk hkb hs he harm
    obtain ⟨E, p, hr⟩ := ir_dispatch m ic I { w with memory := runtimeMem w.memory } hsz hfits hk
      ((selWord_eq_iff hkb).mp hs)
    rw [he, hr]
    exact harm E p
  have ex : ∀ k, selWord I.calldata = UInt256.ofNat k → (entry Exported.runtime).exec I w =
      (entry (if UInt256.ofNat k = UInt256.ofNat 0x06fdde03 then Exported.recv_Name_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x095ea7b3 then Exported.recv_Approve_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x18160ddd then Exported.recv_TotalSupply_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x23b872dd then Exported.recv_TransferFrom_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x2e1a7d4d then Exported.recv_Withdraw_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x313ce567 then Exported.recv_Decimals_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x70a08231 then Exported.recv_BalanceOf_entry
        else if UInt256.ofNat k = UInt256.ofNat 0x95d89b41 then Exported.recv_Symbol_entry
        else if UInt256.ofNat k = UInt256.ofNat 0xa9059cbb then Exported.recv_Transfer_entry
        else if UInt256.ofNat k = UInt256.ofNat 0xd0e30db0 then Exported.recv_Deposit_entry
        else if UInt256.ofNat k = UInt256.ofNat 0xdd62ed3e then Exported.recv_Allowance_entry
        else Exported.recv1_arm0_entry)).exec I w := by
    intro k hk
    simp only [Exported.runtime, entry, Fe.M.exec_bind]
    simp [hn, hn4, selector_exec, hk]
  by_cases h1 : selWord I.calldata = UInt256.ofNat 0x06fdde03
  · exact arm (by simp) (by decide) h1 (by rw [ex _ h1]; simp)
      (arm_name ic I w hl hs hr hrv hw hfits)
  by_cases h2 : selWord I.calldata = UInt256.ofNat 0x095ea7b3
  · exact arm (by simp) (by decide) h2 (by rw [ex _ h2]; simp [ofNat_eq_iff, UInt256.size])
      (arm_approve ic w hsz hfits (by omega) _)
  by_cases h3 : selWord I.calldata = UInt256.ofNat 0x18160ddd
  · exact arm (by simp) (by decide) h3 (by rw [ex _ h3]; simp [ofNat_eq_iff, UInt256.size])
      (arm_totalSupply ic I w (by omega) _)
  by_cases h4 : selWord I.calldata = UInt256.ofNat 0x23b872dd
  · exact arm (by simp) (by decide) h4 (by rw [ex _ h4]; simp [ofNat_eq_iff, UInt256.size])
      (arm_transferFrom ic w hsz hfits htf hmem _)
  by_cases h5 : selWord I.calldata = UInt256.ofNat 0x2e1a7d4d
  · exact arm (by simp) (by decide) h5 (by rw [ex _ h5]; simp [ofNat_eq_iff, UInt256.size])
      (arm_withdraw ic w hsz hfits (by omega) _)
  by_cases h6 : selWord I.calldata = UInt256.ofNat 0x313ce567
  · exact arm (by simp) (by decide) h6 (by rw [ex _ h6]; simp [ofNat_eq_iff, UInt256.size])
      (arm_decimals ic I w (by omega) _)
  by_cases h7 : selWord I.calldata = UInt256.ofNat 0x70a08231
  · exact arm (by simp) (by decide) h7 (by rw [ex _ h7]; simp [ofNat_eq_iff, UInt256.size])
      (arm_balanceOf ic w hsz hfits (by omega) _)
  by_cases h8 : selWord I.calldata = UInt256.ofNat 0x95d89b41
  · exact arm (by simp) (by decide) h8 (by rw [ex _ h8]; simp [ofNat_eq_iff, UInt256.size])
      (arm_symbol ic I w hl hs hr hrv hw hfits)
  by_cases h9 : selWord I.calldata = UInt256.ofNat 0xa9059cbb
  · exact arm (by simp) (by decide) h9 (by rw [ex _ h9]; simp [ofNat_eq_iff, UInt256.size])
      (arm_transfer ic w hsz hfits htf hmem _)
  by_cases h10 : selWord I.calldata = UInt256.ofNat 0xd0e30db0
  · exact arm (by simp) (by decide) h10 (by rw [ex _ h10]; simp [ofNat_eq_iff, UInt256.size])
      (arm_deposit ic I w hdep (by omega) _)
  by_cases h11 : selWord I.calldata = UInt256.ofNat 0xdd62ed3e
  · exact arm (by simp) (by decide) h11 (by rw [ex _ h11]; simp [ofNat_eq_iff, UInt256.size])
      (arm_allowance ic w hsz hfits (by omega) _)
  exact fb (by simp [Exported.runtime, entry, hn, hn4, selector_exec, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11]) (.inr (by
    intro k hk
    simp only [armTable, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by
        first
        | exact h1 ((selWord_eq_iff (by decide)).mpr h)
        | exact h2 ((selWord_eq_iff (by decide)).mpr h)
        | exact h3 ((selWord_eq_iff (by decide)).mpr h)
        | exact h4 ((selWord_eq_iff (by decide)).mpr h)
        | exact h5 ((selWord_eq_iff (by decide)).mpr h)
        | exact h6 ((selWord_eq_iff (by decide)).mpr h)
        | exact h7 ((selWord_eq_iff (by decide)).mpr h)
        | exact h8 ((selWord_eq_iff (by decide)).mpr h)
        | exact h9 ((selWord_eq_iff (by decide)).mpr h)
        | exact h10 ((selWord_eq_iff (by decide)).mpr h)
        | exact h11 ((selWord_eq_iff (by decide)).mpr h)))

/-! ## The certificates -/

/-- The machine IR implements the exported contract on calldata below `2 ^ 64` bytes. -/
theorem feWETH9Implements :
    Implements Exported.contract (sidecar.model .machine) CalldataFits :=
  fun I σ A feed _ hfits => ⟨feed, runtime_endsAs I (World.init σ A feed) rfl hfits⟩

/-- The machine IR's constructor implements the exported one, on no arguments. -/
theorem feWETH9ImplementsDeploy :
    ImplementsDeploy Exported.contract (sidecar.model .machine) feWETH9CreationBytecode
      feWETH9Bytecode .empty (· = ByteArray.empty) := by
  rintro I σ A feed args rfl hcode _ hperm
  exact ⟨feed, init_endsAs I _ rfl hcode hperm⟩

/-- `runtime.hex` refines the exported contract at profile `P1`, on calldata below `2 ^ 64`
    bytes: the checker's certificate of the sidecar, whose runtime bytes are these, composed
    with `feWETH9Implements`. -/
theorem feWETH9RefinesExportedP1 :
    RefinesOn .P1 feWETH9Bytecode Exported.contract CalldataFits :=
  RefinesOn.of_implements (sidecar_runtime ▸ sidecar_sound.1) feWETH9Implements rfl

/-- Deployment by `creation.hex` with no arguments refines the exported deployment entry at
    profile `P1`. -/
theorem feWETH9DeployRefinesExportedP1 :
    RefinesDeploy .P1 feWETH9CreationBytecode feWETH9Bytecode Exported.contract
      (· = ByteArray.empty) :=
  RefinesDeploy.of_implements (fun σ σ₀ g A I args _ hcode hown hperm =>
    sidecar_sound.2 σ σ₀ g A I args trivial (by rw [sidecar_init]; exact hcode) hown hperm)
    feWETH9ImplementsDeploy

end FeProofs.WETH9.Sonatina
