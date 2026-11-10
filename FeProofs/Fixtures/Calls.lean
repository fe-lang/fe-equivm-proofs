import Fe.EVM.Calls

/-!
# The external-call primitives on simple inputs

Checks that the primitives of `Fe.EVM.Calls` elaborate by their bare names beside EVMLean's own
`call` and `create`, as exported code uses them, and that they do what their descriptions say
where that is easy to see.  Applied to arguments, `call` and `create` resolve by type; named
alone, as in a `simp` set, they are ambiguous and need their namespace.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.Fixtures.Calls

section
set_option linter.unusedVariables false

/-- Each primitive once, named as `fe-lean-export` names the extern it models. -/
def probe (addr : UInt256) : FeM UInt256 := do
  let v0 ← gas
  let v1 := (UInt256.ofNat 0)
  let v2 ← call v0 addr v1 v1 v1 v1 v1
  let v3 ← staticcall v0 addr v1 v1 v1 v1
  let v4 ← staticcallPrecompile v0 addr v1 v1 v1 v1
  let v5 ← delegatecall v0 addr v1 v1 v1 v1
  let v6 ← returndatasize
  returndatacopy v1 v1 v6
  let v7 ← create v1 v1 v1
  let v8 ← create2 v1 v1 v1 v1
  let v9 ← extcodehash addr
  extcodecopy addr v1 v1 v1
  return v9

end

/-- `gas()` reads the feed's next entry and takes it. -/
theorem gas_exec (s : Supply) (σ : AccountMap) (A : Substate) (I : ExecutionEnv) :
    gas.exec I (World.init σ A [s]) = some (.ok (s.gas, World.init σ A)) := rfl

/-- `returndatacopy` past the end of the return data exits with `oob`. -/
theorem returndatacopy_oob (dest offset len : UInt256) (I : ExecutionEnv) (w : World)
    (h : w.returnData.size < offset.toNat + len.toNat) :
    (returndatacopy dest offset len).exec I w = some (.error .oob) := by
  simp [returndatacopy, h]

/-- Before any call there is no return data, so copying a byte of it exits with `oob`. -/
theorem returndatacopy_first (dest : UInt256) (σ : AccountMap) (A : Substate) (I : ExecutionEnv) :
    (returndatacopy dest (UInt256.ofNat 0) (UInt256.ofNat 1)).exec I (World.init σ A) =
      some (.error .oob) :=
  returndatacopy_oob _ _ _ _ _ Nat.zero_lt_one

/-- A `call` with nothing left in the feed does not terminate. -/
theorem call_empty_feed (gas addr value argsPtr argsLen retPtr retLen : UInt256)
    (I : ExecutionEnv) (w : World) (hfeed : w.feed = []) (hperm : I.perm = true) :
    (call gas addr value argsPtr argsLen retPtr retLen).exec I w = none := by
  simp [Fe.EVM.call, message, next, hfeed, hperm]

/-- A `staticcall` that returns leaves each word of the caller's storage as it was: an `sload`
    after it reads what one before it read. -/
theorem staticcall_keeps_slot {I : ExecutionEnv} {w w' : World}
    {gas addr argsPtr argsLen retPtr retLen x : UInt256}
    (h : (staticcall gas addr argsPtr argsLen retPtr retLen).exec I w = some (.ok (x, w')))
    (slot : UInt256) : slotWord I w'.accounts slot = slotWord I w.accounts slot := by
  have word : ∀ σ : AccountMap,
      slotWord I σ slot = (σ.getD I.codeOwner default).storage.getD slot ⟨0⟩ := by
    intro σ
    rw [slotWord, Std.ExtTreeMap.getD_eq_getD_getElem? (t := σ), Std.ExtTreeMap.get?_eq_getElem?]
    cases σ[I.codeOwner]? <;> rfl
  rw [word, word, (staticcall_keeps_storage h I.codeOwner).1]

end FeProofs.Fixtures.Calls
