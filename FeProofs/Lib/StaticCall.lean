import Fe.EVM.Calls

/-!
# Static calls of exported code

`Fe.EVM.staticcall` as exported code makes it to a precompile: from the feed's next entry `s`,
the call `staticT I σ g s a d` of the input bytes `d` at the address word `a`, with the result
`staticR` (`Θ`'s below depth 1024, else a failure with no output).  `staticcall_exec` states a
static call in that form: two runs that call the same address with the same accounts, feed entry
and input bytes, whatever their memory, make the same call with the same result, so a proof can
name `staticR …` once for both.

`staticR_sha256`: a call of the SHA-256 precompile (address 2) that succeeds returns
`SHA256.hash d`, EVMLean's digest of the input (what `Ξ_SHA256` returns), whatever gas it had,
on accounts that are not empty (`OwnerExists` gives that).
-/

namespace FeProofs.Lib

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM

/-- The message call a static call of the input bytes `d` at the address word `a` makes from
    accounts `σ`, with the gas argument `g` and the feed's entry `s`. -/
def staticT (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply) (a : UInt256)
    (d : ByteArray) : ThetaCall where
  σ := σ
  σ₀ := s.orig
  A := s.substate
  s := I.codeOwner
  o := I.sender
  r := AccountAddress.ofUInt256 a
  c := toExecute σ (AccountAddress.ofUInt256 a)
  g := forwardedGas s.gas g ⟨0⟩
  p := .ofNat I.gasPrice
  v := ⟨0⟩
  v' := ⟨0⟩
  d := d
  e := I.depth + 1
  H := I.header
  bvh := I.blobVersionedHashes
  blocks := I.blocks
  w := false

/-- Its result: `Θ`'s below depth 1024, else no call, a failure with no output. -/
def staticR (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply) (a : UInt256)
    (d : ByteArray) : AccountMap × UInt256 × Substate × Bool × ByteArray :=
  if I.depth < 1024 then (staticT I σ g s a d).run else (σ, ⟨0⟩, s.substate, false, .empty)

/-- The world after a static call from `w` of the input `d`, its first `k` bytes of output at
    `r`: the result's accounts, the logs it appended, its output as the return data, the feed's
    rest, and the call recorded when it was made. -/
def staticWorld (I : ExecutionEnv) (w : World) (g : UInt256) (s : Supply) (rest : List Supply)
    (a : UInt256) (d : ByteArray) (r k : UInt256) : World :=
  { w with
    accounts := (staticR I w.accounts g s a d).1
    logs := w.logs ++ appended s.substate (staticR I w.accounts g s a d).2.2.1
    memory := (staticR I w.accounts g s a d).2.2.2.2.write 0 w.memory r.toNat
      (min k (UInt256.ofNat (staticR I w.accounts g s a d).2.2.2.2.size)).toNat
    returnData := (staticR I w.accounts g s a d).2.2.2.2
    feed := rest
    calls := if I.depth < 1024 then w.calls ++ [Made.theta (staticT I w.accounts g s a d)]
      else w.calls }

theorem zero_le_word (x : UInt256) : (⟨0⟩ : UInt256) ≤ x := Nat.zero_le _

/-- `gas()` on a feed with an entry: the entry's gas word. -/
theorem gas_exec {I : ExecutionEnv} {w : World} {s : Supply} {rest : List Supply}
    (hfeed : w.feed = s :: rest) :
    Fe.EVM.gas.exec I w = some (.ok (s.gas, { w with feed := rest })) := by
  simp [Fe.EVM.gas, Fe.EVM.next, hfeed]

/-- `gas()` on an empty feed does not terminate. -/
theorem gas_exec_nil {I : ExecutionEnv} {w : World} (hfeed : w.feed = []) :
    Fe.EVM.gas.exec I w = none := by
  simp [Fe.EVM.gas, Fe.EVM.next, hfeed]

/-- A static call on a feed with an entry: the call `staticT` with the result `staticR`, on the
    `n` bytes of memory at `p`. -/
theorem staticcall_exec {I : ExecutionEnv} {w : World} {s : Supply} {rest : List Supply}
    (hfeed : w.feed = s :: rest) (g a p n r k : UInt256) :
    (Fe.EVM.staticcall g a p n r k).exec I w =
      some (.ok (if (staticR I w.accounts g s a (w.memory.readWithPadding p.toNat n.toNat)).2.2.2.1
          then ⟨1⟩ else ⟨0⟩,
        staticWorld I w g s rest a (w.memory.readWithPadding p.toNat n.toNat) r k)) := by
  simp only [Fe.EVM.staticcall, Fe.EVM.message, Fe.EVM.next, hfeed, Fe.M.exec_bind,
    Fe.M.exec_read, Fe.M.exec_get, Fe.M.exec_set, Fe.M.exec_pure, zero_le_word, true_and]
  unfold staticWorld staticR
  by_cases hd : I.depth < 1024 <;> simp only [hd, ite_true, ite_false] <;> rfl

/-- A static call on an empty feed does not terminate. -/
theorem staticcall_nil {I : ExecutionEnv} {w : World} (hfeed : w.feed = [])
    (g a p n r k : UInt256) : (Fe.EVM.staticcall g a p n r k).exec I w = none := by
  simp [Fe.EVM.staticcall, Fe.EVM.message, Fe.EVM.next, hfeed]

theorem ofUInt256_two : AccountAddress.ofUInt256 (UInt256.ofNat 2) = (2 : AccountAddress) := rfl

/-- Address 2 is a precompile's, whatever the accounts. -/
theorem sha256_toExecute (σ : AccountMap) :
    toExecute σ (2 : AccountAddress) = .Precompiled 2 := by
  unfold toExecute
  rw [ite_eq_left (by decide +kernel)]

/-- `Θ`'s dispatch on a precompile's address, at address 2. -/
theorem theta_match_two {β : AccountAddress → Sort u} (f1 : Unit → β 1) (f2 : Unit → β 2)
    (f3 : Unit → β 3) (f4 : Unit → β 4) (f5 : Unit → β 5) (f6 : Unit → β 6) (f7 : Unit → β 7)
    (f8 : Unit → β 8) (f9 : Unit → β 9) (f10 : Unit → β 10) (fd : (x : AccountAddress) → β x) :
    Θ.match_3 β 2 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 fd = f2 () := rfl

set_option maxHeartbeats 1000000 in
/-- A call of the SHA-256 precompile that succeeds returns the digest of its input. -/
theorem staticR_sha256 {I : ExecutionEnv} {σ : AccountMap} {g : UInt256} {s : Supply}
    {d : ByteArray} (hz : (staticR I σ g s (UInt256.ofNat 2) d).2.2.2.1 = true) :
    (staticR I σ g s (UInt256.ofNat 2) d).2.2.2.2 = SHA256.hash d := by
  unfold staticR at hz ⊢
  by_cases hd : I.depth < 1024
  · simp only [hd, ite_true, ThetaCall.run, staticT, ofUInt256_two, sha256_toExecute] at hz ⊢
    unfold Θ at hz ⊢
    simp only [theta_match_two, Ξ_SHA256] at hz ⊢
    split_ifs at hz ⊢ <;> simp_all
  · simp [hd] at hz

/-- Two account maps whose accounts, where there is one, hold the same storage. -/
def SameStorage (σ σ' : AccountMap) : Prop :=
  ∀ o, (σ'.get? o).map (·.storage) = (σ.get? o).map (·.storage)

theorem SameStorage.refl (σ : AccountMap) : SameStorage σ σ := fun _ => rfl

theorem SameStorage.trans {σ σ' σ'' : AccountMap} (h : SameStorage σ σ') (h' : SameStorage σ' σ'') :
    SameStorage σ σ'' := fun o => (h' o).trans (h o)

theorem sameStorage_insert {σ : AccountMap} {r : AccountAddress} {acc : Account}
    (h : σ.get? r = some acc) (b : UInt256) : SameStorage σ (σ.insert r { acc with balance := b }) := by
  intro o
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at h ⊢
  split
  · next he => rw [← Std.ExtTreeMap.getElem?_congr he, h]; rfl
  · rfl

theorem sameStorage_step {σ σ1 : AccountMap} (h : SameStorage σ σ1) (r : AccountAddress)
    (b : Account → UInt256) :
    SameStorage σ (match σ1[r]? with
      | none => σ1
      | some acc => σ1.insert r { acc with balance := b acc }) := by
  split
  · exact h
  · next acc hr => exact h.trans (sameStorage_insert (by rw [Std.ExtTreeMap.get?_eq_getElem?]; exact hr) _)

/-- The contract's slot words through accounts with the same storage. -/
theorem SameStorage.slotWord {σ σ' : AccountMap} (h : SameStorage σ σ') (I : ExecutionEnv)
    (k : UInt256) : slotWord I σ' k = slotWord I σ k := by
  have ho := h I.codeOwner
  unfold Fe.EVM.slotWord
  rcases h1 : σ'.get? I.codeOwner with _ | a <;> rcases h2 : σ.get? I.codeOwner with _ | b <;>
    simp only [h1, h2, Option.map, Option.some.injEq, reduceCtorEq] at ho <;>
    simp [Option.option, ho]

set_option maxHeartbeats 1000000 in
/-- A call of the SHA-256 precompile, made or not, keeps every account's storage. -/
theorem staticR_sha256_storage (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply)
    (d : ByteArray) : SameStorage σ (staticR I σ g s (UInt256.ofNat 2) d).1 := by
  unfold staticR
  by_cases hd : I.depth < 1024
  · simp only [hd, ite_true, ThetaCall.run, staticT, ofUInt256_two, sha256_toExecute]
    unfold Θ
    simp only [theta_match_two, Ξ_SHA256, show ((⟨0⟩ : UInt256) != UInt256.ofNat 0) = false by decide,
      Bool.false_eq_true, ite_false]
    split_ifs
    all_goals first
      | exact SameStorage.refl _
      | exact sameStorage_step (sameStorage_step (SameStorage.refl σ) 2 _) I.codeOwner _
      | simp_all
  · simp only [hd, ite_false]; exact SameStorage.refl _

set_option maxHeartbeats 1000000 in
/-- A call of the SHA-256 precompile leaves the substate it was given: it appends no log. -/
theorem staticR_sha256_substate (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply)
    (d : ByteArray) : (staticR I σ g s (UInt256.ofNat 2) d).2.2.1 = s.substate := by
  unfold staticR
  by_cases hd : I.depth < 1024
  · simp only [hd, ite_true, ThetaCall.run, staticT, ofUInt256_two, sha256_toExecute]
    unfold Θ
    simp only [theta_match_two, Ξ_SHA256]
    split_ifs <;> rfl
  · simp only [hd, ite_false]

end FeProofs.Lib
