import Fe.Sonatina.H.Sem
import Fe.Sonatina.RealFeed

/-!
# The bytes refine the handover object (design §7.4)

`RefinesForH`, `RefinesOnH` and `RefinesDeployH` are `RefinesForFut`, `RefinesOnFut` and
`RefinesDeployFut` (`Fe/Sonatina/RealFeed.lean`) with H's handover object in the place of a
model: on every call the bytes run out of gas or of stack, or, under the call's real feed, some
run of the handover IR is `ub` or `exhausted`, or ends as the bytes do.  The excuses hold under
the real feed only (review 22, C1).

`RefinesOnFut.toH` and `RefinesDeployFut.toH` compose the two halves: links 4 and 5 (the bytes
refine a model of the IR right after lowering, under the real feed) with Stage 3 (that model
implements the handover object under H, `ImplementsH`, `ImplementsDeployH`).  Both are stated
for any model, runtime bytes and arguments.  The design's `RefinesDeployH` has no `validArgs`;
this one takes it, as `RefinesDeployFut` does, so that the composition holds for any; the
design's form is `validArgs := fun _ => True`.  `stage3_sound` and `o0_sound` are not stated:
they need Stage 3's checker.
-/

namespace Fe.Sonatina.H

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The bytes refine the handover object on one call (§7.4): they run out of gas or stack; or,
    under the call's real feed, some run of the handover IR is `ub` or `exhausted`, or ends as
    the bytes do. -/
def RefinesForH (p : Profile) (h : Object) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : Prop :=
  Exhausted (Ξ σ σ₀ g A I) ∨
    ∃ feed, RealFeed σ σ₀ g A I feed ∧ ∃ out, h.Runtime I (World.init σ A feed) out ∧
      (out = .ub ∨ out = .exhausted ∨ ∃ r, out = .ends r ∧ Agrees p (Ξ σ σ₀ g A I) (some r))

/-- `RefinesForH` on every call of `code`, with no immutable fields after it, at an account that
    exists, that `admits` holds of (§7.4). -/
def RefinesOnH (p : Profile) (code : ByteArray) (h : Object) (admits : ExecutionEnv → Prop) :
    Prop :=
  ∀ σ σ₀ g A I tail, I.code = code ++ tail → tail.size = 0 → OwnerExists σ I → admits I →
    RefinesForH p h σ σ₀ g A I

/-- The creation bytes refine the handover object's constructor on every deployment with
    arguments `validArgs` holds of (§7.4, with `validArgs` as `RefinesDeployFut` has it). -/
def RefinesDeployH (p : Profile) (creation : ByteArray) (h : Object)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true →
    Exhausted (Ξ σ σ₀ g A I) ∨
      ∃ feed, RealFeed σ σ₀ g A I feed ∧ ∃ out, h.Deploy args I (World.init σ A feed) out ∧
        (out = .ub ∨ out = .exhausted ∨ ∃ r, out = .ends r ∧ Agrees p (Ξ σ σ₀ g A I) (some r))

/-- A handover outcome that matches a machine result the bytes agree with is an excuse or
    agrees with the bytes itself. -/
theorem Matches.agrees {p : Profile} {evm : EvmResult} {out : Outcome}
    {r : Except (Exit World) (ByteArray × World)} (hm : Matches out r)
    (hag : Agrees p evm (some r)) :
    out = .ub ∨ out = .exhausted ∨ ∃ r', out = .ends r' ∧ Agrees p evm (some r') := by
  rcases hm with h | h | ⟨r', e, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨r', e, Agrees.of_endsAs he hag⟩)

end Fe.Sonatina.H

namespace Fe.EVM

open Ethereum Ethereum.EVM Fe Fe.Sonatina.H

/-- Links 4 and 5 composed with Stage 3 on calls: if the bytes refine the model `m` under each
    call's real feed and `m` implements the handover object under H, the bytes refine the
    handover object.  `himm`: `RefinesOnFut` asks `tail.size = m.immutables`, `RefinesOnH`
    asks `tail.size = 0`. -/
theorem RefinesOnFut.toH {p : Profile} {code : ByteArray} {m : ContractModel} {h : Object}
    {admits : ExecutionEnv → Prop} (hb : RefinesOnFut p code m admits)
    (hm : ImplementsH h m admits) (himm : m.immutables = 0) : RefinesOnH p code h admits := by
  intro σ σ₀ g A I tail hc ht ho ha
  rcases hb σ σ₀ g A I tail hc (himm ▸ ht) ho ha with hx | ⟨feed, hreal, hag⟩
  · exact .inl hx
  · -- `Agrees` excludes a diverging run (`Agrees p evm none = False`), so the machine run ends.
    cases hrun : m.runtime.exec I (World.init σ A feed) with
    | none => rw [hrun] at hag; exact hag.elim
    | some r =>
      rw [hrun] at hag
      obtain ⟨out, hout, hmat⟩ := hm I σ A feed r ho ha hrun
      exact .inr ⟨feed, hreal, out, hout, hmat.agrees hag⟩

/-- Links 4 and 5 composed with Stage 3 on deployments, for any runtime bytes the model's
    result is put after and any arguments. -/
theorem RefinesDeployFut.toH {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {h : Object} {validArgs : ByteArray → Prop}
    (hb : RefinesDeployFut p creation runtime m validArgs)
    (hm : ImplementsDeployH h m creation runtime validArgs) :
    RefinesDeployH p creation h validArgs := by
  intro σ σ₀ g A I args hv hc ho hp
  rcases hb σ σ₀ g A I args hv hc ho hp with hx | ⟨feed, hreal, hag⟩
  · exact .inl hx
  · cases hrun : (m.init args >>= fun tail => pure (runtime ++ tail)).exec I
        (World.init σ A feed) with
    | none => rw [hrun] at hag; exact hag.elim
    | some r =>
      rw [hrun] at hag
      obtain ⟨out, hout, hmat⟩ := hm I σ A feed args r hv hc ho hp hrun
      exact .inr ⟨feed, hreal, out, hout, hmat.agrees hag⟩

end Fe.EVM
