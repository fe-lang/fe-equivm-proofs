import Reasoning.Reach
import Fe.EVM.Refine
import Fe.EVM.Calls

/-!
# From a finished EVM trace to model refinement

EquiVM's terminals `RDret`, `RDrev` and `RDstatic` say how a run of the bytecode ends, or that it
runs out of gas.  Paired with the model's run on the same inputs, each gives agreement.

`RDret` does not expose the final substate and `RDrev` hides the revert payload, so these lemmas
conclude at profile `P0` only.

A `CALL` inside a trace is EVMLean's `Θ` on gas, a substate and an original account map the
trace does not expose; `call_feed` gives the entry of the feed with which the model's `call`
makes the same message call.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

variable {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256} {code : ByteArray}
  {r : Option (Except (Exit World) (ByteArray × World))}

/-- The bytecode returns `o` with account map `σ'`, and so does the model. -/
theorem agrees_of_ret {o : ByteArray} {σ' : AccountMap} {w' : World}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : r = some (.ok (o, w'))) (hw : w'.accounts = σ') :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    exact Or.inr ⟨_, _, by rw [hxi, hw, hacc], fun h => by cases h⟩

/-- The bytecode returns `o` with account map `σ'`, and the model stops with the same. -/
theorem agrees_of_stop {o : ByteArray} {σ' : AccountMap} {w' : World}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o)
    (hm : r = some (.error (.stop o w'))) (hw : w'.accounts = σ') :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    exact Or.inr ⟨_, _, by rw [hxi, hw, hacc], fun h => by cases h⟩

/-- The bytecode reverts, and the model fails with a revert or a panic. -/
theorem agrees_of_rev {f : Exit World}
    (hcode : I.code = code)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hm : r = some (.error f)) (hf : f.reverts = true) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | ⟨g', o, hX⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    refine Or.inr ?_
    cases f with
    | revert data => exact ⟨g', o, hxi, fun h => by cases h⟩
    | panic code => exact ⟨g', o, hxi, fun h => by cases h⟩
    | static => cases hf
    | trap => cases hf
    | oob => cases hf
    | stop o w => cases hf

/-- The bytecode halts on a static-mode violation, and the model fails the same way. -/
theorem agrees_of_static
    (hcode : I.code = code)
    (h : RDstatic code g (initState σ σ₀ g A I))
    (hm : r = some (.error .static)) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨ Agrees .P0 (Ξ σ σ₀ g.toUInt256 A I) r := by
  subst hcode hm
  rcases h with hoog | hst
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · exact Or.inr (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hst))

/-! ## Decoding -/

/-- A calldata word at or above `2 ^ 160` is not an address. -/
theorem notAddress_of {w : UInt256} (h : ¬ w.toNat < EVM.addressModulus) : NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

theorem not_notAddress_of {w : UInt256} (h : w.toNat < EVM.addressModulus) : ¬ NotAddress w := by
  simpa [NotAddress, EVM.addressModulus] using h

/-- Calldata too short for `n` words, or so long that the signed length check rejects it. -/
theorem badHead_of {cd : ByteArray} {n : ℕ} (h : cd.size < 4 + 32 * n ∨ 2 ^ 255 + 4 ≤ cd.size) :
    BadHead cd n := h

theorem not_badHead_of {cd : ByteArray} {n : ℕ} (hlen : 4 + 32 * n ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) : ¬ BadHead cd n := by
  unfold BadHead; omega

/-- The model's storage write is the account-map update the trace lemmas use. -/
theorem storeWord_eq_sstoreAccountMap (owner : AccountAddress) (σ : AccountMap)
    (slot val : UInt256) : storeWord owner σ slot val = sstoreAccountMap owner σ slot val := rfl

/-! ## External calls -/

set_option maxHeartbeats 1000000 in
/-- EquiVM's `RD.callValueMadeOr`, with the gas the callee gets as `forwardedGas` of some cap: the
    proof is EquiVM's, which shows the gas is `Ccallgas` and does not say so. -/
theorem callValueMade_forwardedGas {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata σ k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hperm : ee.perm = true ∨ valueWord = ⟨0⟩)
    (hbalance : valueWord ≤ (σ.get? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (cap : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, o) = Ethereum.EVM.Θ σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          (forwardedGas cap gasArg valueWord) (UInt256.ofNat ee.gasPrice) valueWord valueWord
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header
          ee.blobVersionedHashes ee.blocks ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o σ' k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hσ₀⟩
  · exact ⟨_, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ valueWord ≠ { val := 0 }) = False :=
      eq_false (by
        rintro ⟨hp, hv⟩
        rcases hperm with h | h
        · exact hp (by rw [hee]; exact h)
        · exact hv h)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hσ : s.accountMap = σ := hacc
    have hbalT :
        (valueWord ≤ (s.accountMap.get? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true hbalance
    have hbalOpt :
        (valueWord ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner)) = True := by
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner) =
          (s.accountMap.get? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Std.ExtTreeMap.get? s.accountMap s.executionEnv.codeOwner <;> rfl]
      exact hbalT
    have hgtF :
        (valueWord > (s.accountMap.get? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          False := by
      rw [hee, hσ]
      exact eq_false (by
        intro hlt
        have hLeNat :
            valueWord.val.val ≤
              ((σ.get? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val := hbalance
        have hGtNat :
            ((σ.get? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val <
              valueWord.val.val := hlt
        exact Nat.not_lt_of_ge hLeNat hGtNat)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtF, hdeqF,
      and_true, if_true, Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨_, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      set mc := memoryExpansionCost s Operation.CALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
        gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
        with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        valueWord gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
        with hG
      set cg := UInt256.ofNat G with hcg
      set θs := Θ s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes
        s.executionEnv.blocks s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.1.toNat) with hgv
      have hw1 : s.σ₀ = s0.σ₀ := hσ₀
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
          (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
          (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes
          s.executionEnv.blocks s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) valueWord gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - θs.2.1.toNat) with hcallCharge
      have hcallChargePos : 1 ≤ callCharge := by
        rw [hcallCharge]
        omega
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - θs.2.1.toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      obtain ⟨cap, hcap⟩ := forwardedGas_Ccallgas (AccountAddress.ofUInt256 target)
        (AccountAddress.ofUInt256 target) valueWord gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate
      replace hcap : forwardedGas cap gasArg valueWord = cg := by rw [hcap, hcg, hG]
      refine ⟨θs.1, θs.2.2.2.1, θs.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cap, k + 1,
        C + callCharge, ⟨θs.2.1, θs.2.2.1, ?_⟩, ?_⟩
      · rw [hcap, ← hee, ← hσ, ← hmem, ← hw1, ← hθs]
      · unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hσ₀

/-- A `CALL` in a trace and the model's `call` on the same accounts and input bytes: for some
    entry of the feed, the model's call returns the status the bytecode pushes, with the accounts
    and return data the trace goes on with, whether the call is made or not.  The call moves no
    value or has write permission, so it is not a static-mode violation. -/
theorem call_feed {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t)
      mem aw rdata σ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : I.perm = true ∨ value = ⟨0⟩)
    (hov : t.length + 1 ≤ 1024) {w : World} {argsPtr argsLen retPtr retLen : UInt256}
    (rest : List Supply) (hacc : w.accounts = σ)
    (hargs : w.memory.readWithPadding argsPtr.toNat argsLen.toNat =
      mem.readWithPadding inOffset.toNat inSize.toNat) :
    ∃ (s : Supply) (z : Bool) (o : ByteArray) (σ' : AccountMap) (logs : LogSeries)
      (aw' : UInt256) (k' C' : ℕ),
      (call gasArg target value argsPtr argsLen retPtr retLen).exec I
          { w with feed := s :: rest } =
        some (.ok (if z then ⟨1⟩ else ⟨0⟩, { w with
          accounts := σ'
          logs := logs
          memory := o.write 0 w.memory retPtr.toNat (min retLen (.ofNat o.size)).toNat
          returnData := o
          feed := rest })) ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
        (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
        aw' o σ' k' C' := by
  have hcall : ∀ s : Supply,
      (call gasArg target value argsPtr argsLen retPtr retLen).exec I { w with feed := s :: rest } =
        (message gasArg I.codeOwner (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) value value argsPtr argsLen retPtr retLen I.perm).exec I
          { w with feed := s :: rest } := by
    intro s
    have hns : ¬ (I.perm = false ∧ value ≠ ⟨0⟩) := by
      rintro ⟨hp, hv⟩
      rcases hperm with h | h
      · rw [hp] at h; cases h
      · exact hv h
    simp only [call, M.exec_bind, M.exec_read, if_neg hns]
  have hopt : (σ.get? I.codeOwner |>.option ⟨0⟩ (·.balance)) =
      (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)) := by
    cases σ.get? I.codeOwner <;> rfl
  let s₀ : Supply := ⟨⟨0⟩, default, s0.σ₀⟩
  by_cases hmade : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth.val < 1024
  · obtain ⟨σ', z, o, AIn, cap, k', C', ⟨g'', A', hΘ⟩, rd⟩ :=
      callValueMade_forwardedGas h hdec hperm hmade.1 hmade.2 hov
    let s : Supply := ⟨cap, AIn, s0.σ₀⟩
    rw [accountAddress_roundtrip, ← hargs, ← hacc] at hΘ
    refine ⟨s, z, o, σ', w.logs ++ appended AIn A', _, k', C', ?_, rd⟩
    rw [hcall, message_made (w := { w with feed := s :: rest }) (s := s) (rest := rest) rfl
      (by simp only [hacc, hopt]; exact ⟨hmade.1, hmade.2⟩) hΘ]
  · have hnot : ¬ (value ≤ ((w.accounts.get? I.codeOwner).option ⟨0⟩ (·.balance)) ∧
        I.depth < 1024) := by
      rw [hacc, hopt]; exact hmade
    have rd : ∃ k' C', RD code I g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty σ k' C' := by
      by_cases hb : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance))
      · have hd : I.depth = 1024 := by
          apply Fin.ext
          have := I.depth.isLt
          have : ¬ I.depth.val < 1024 := fun hlt => hmade ⟨hb, hlt⟩
          change I.depth.val = 1024
          omega
        exact RD.callValueDepthLimitOr h hperm hdec hd hov
      · by_cases hd : I.depth = 1024
        · exact RD.callValueDepthLimitOr h hperm hdec hd hov
        · have hdl : I.depth.val < 1024 := by
            have := I.depth.isLt
            have : I.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
            omega
          exact RD.callValueInsufficientBalanceOr h hperm hdec hb hdl hov
    obtain ⟨k', C', rd⟩ := rd
    refine ⟨s₀, false, ByteArray.empty, σ, w.logs ++ appended s₀.substate s₀.substate, _, k', C',
      ?_, rd⟩
    rw [hcall, message_notMade (w := { w with feed := s₀ :: rest }) (s := s₀) (rest := rest) rfl
      hnot, ← hacc]
    rfl

end Fe.EVM
