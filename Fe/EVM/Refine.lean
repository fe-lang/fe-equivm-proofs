import Fe.EVM.World

/-!
# Refinement of a Fe contract model by EVM bytecode

`Refines p bytecode model`: on every message call at an account that exists (`OwnerExists`) the
bytecode either runs out of gas or of stack, or does what the model does, as far as profile `p`
observes.  A model that calls other
contracts or reads its gas takes those inputs from a feed, and does what the bytecode does under
some feed.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM

/-- What a result observes.  `P0`: outcome kind, return data, account map.  `P1` adds event logs
    and revert payloads.  Neither observes gas. -/
inductive Profile where
  | P0
  | P1

/-- The return data of a panic, Solidity's `Panic(uint256)`: what std's `revert_error` of a
    panic reverts with (`revertPanic_exec` in `FeProofs/Lib/ExportedCorrect.lean`). -/
def panicData (code : Nat) : ByteArray :=
  ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (UInt256.ofNat code).toByteArray

abbrev EvmResult :=
  Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))

/-- The EVM result agrees with the model's run.  A model run that diverges agrees with nothing,
    so only running out of gas or of stack can match it.  A run that stops from inside a callee is a success,
    like one that returns.  A read past the end of the return data is the EVM's invalid memory
    access. -/
def Agrees (p : Profile) (evm : EvmResult) :
    Option (Except (Exit World) (ByteArray × World)) → Prop
  | none => False
  | some (.ok (out, w)) | some (.error (.stop out w)) =>
      ∃ g' A', evm = .ok (.success (w.accounts, g', A') out) ∧ (p = .P1 → A'.logSeries = w.logs)
  | some (.error (.revert data)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = data)
  | some (.error (.panic code)) =>
      ∃ g' o, evm = .ok (.revert g' o) ∧ (p = .P1 → o = panicData code)
  | some (.error .static) => evm = .error .StaticModeViolation
  | some (.error .trap) => evm = .error .InvalidInstruction
  | some (.error .oob) => evm = .error .InvalidMemoryAccess

/-- One model run ends as another does: with the same exit, or successfully with the same return
    data, accounts, logs and recorded calls, whether each returns or stops.  Memory may
    differ.  A panic ends as the revert with its payload does, which is what the bytecode
    does. -/
inductive EndsAs : Option (Except (Exit World) (ByteArray × World)) →
    Option (Except (Exit World) (ByteArray × World)) → Prop
  | stop_ok {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) (hc : w'.calls = w.calls) :
      EndsAs (some (.error (.stop out w'))) (some (.ok (out, w)))
  | stop_stop {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) (hc : w'.calls = w.calls) :
      EndsAs (some (.error (.stop out w'))) (some (.error (.stop out w)))
  | exit (f : Exit World) : EndsAs (some (.error f)) (some (.error f))
  | panic_revert (code : Nat) :
      EndsAs (some (.error (.panic code))) (some (.error (.revert (panicData code))))
  | ok_ok {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) (hc : w'.calls = w.calls) :
      EndsAs (some (.ok (out, w'))) (some (.ok (out, w)))
  | ok_stop {out : ByteArray} {w w' : World} (ha : w'.accounts = w.accounts)
      (hl : w'.logs = w.logs) (hc : w'.calls = w.calls) :
      EndsAs (some (.ok (out, w'))) (some (.error (.stop out w)))
  | diverge : EndsAs none none

/-- A result that agrees with a run agrees with any run that ends as it does. -/
theorem Agrees.of_endsAs {p : Profile} {evm : EvmResult}
    {a b : Option (Except (Exit World) (ByteArray × World))} (h : EndsAs a b)
    (hb : Agrees p evm b) : Agrees p evm a := by
  cases h with
  | stop_ok ha hl _ | stop_stop ha hl _ | ok_ok ha hl _ | ok_stop ha hl _ =>
    simpa only [Agrees, ha, hl] using hb
  | exit f => exact hb
  | panic_revert code => exact hb
  | diverge => exact hb

/-- A contract's model.  The deployed code is the runtime bytecode followed by the words of the
    contract's immutable fields, which the constructor computes and the runtime entry reads from
    the end of the running code. -/
structure ContractModel where
  /-- The constructor, from the argument bytes that follow the creation code to the bytes of
      the immutable fields. -/
  init : ByteArray → FeM ByteArray
  /-- The runtime entry, from calldata to return data. -/
  runtime : FeM ByteArray
  /-- The bytes the immutable fields take. -/
  immutables : Nat := 0

/-- The low memory a compiled section's entry code reserves before the contract's code runs: the
    scratch space at `0x00` and the free-pointer word at `0x40`.  A section that allocates stores
    its initial free pointer at `0x40`, which grows memory to at least `0x60` bytes, and its heap
    starts at or above `0x60`; a section that does not allocate has no heap.  So no allocation
    of the bytecode is at address 0, which core's `try_alloc_bytes` reads as a failed allocation.
    The model allocates at the end of memory (`alloc`), so its entries grow memory to this size
    first.  No exported code reads memory at a fixed address, so what these bytes hold is not
    observed: the model's are zeros where the bytecode's free-pointer word is not. -/
def reservedMemory : Nat := 0x60

/-- Memory grown with zeros to at least `reservedMemory` bytes, as a store at `0x40` grows it. -/
@[irreducible] def reserveMemory (memory : ByteArray) : ByteArray :=
  memory ++ ⟨Array.replicate (reservedMemory - memory.size) 0⟩

/-- The world with low memory reserved. -/
def World.reserved (w : World) : World := { w with memory := reserveMemory w.memory }

@[simp] theorem World.reserved_accounts (w : World) : w.reserved.accounts = w.accounts := rfl
@[simp] theorem World.reserved_logs (w : World) : w.reserved.logs = w.logs := rfl
@[simp] theorem World.reserved_returnData (w : World) : w.reserved.returnData = w.returnData := rfl
@[simp] theorem World.reserved_feed (w : World) : w.reserved.feed = w.feed := rfl
@[simp] theorem World.reserved_calls (w : World) : w.reserved.calls = w.calls := rfl

/-- What a section's entry code does before the contract's code runs: reserve low memory. -/
def reserve : FeM Unit := modify World.reserved

@[simp] theorem exec_reserve (I : ExecutionEnv) (w : World) :
    reserve.exec I w = some (.ok ((), w.reserved)) := rfl

theorem reserveMemory_size (memory : ByteArray) :
    (reserveMemory memory).size = max memory.size reservedMemory := by
  simp only [reserveMemory, ByteArray.size_append]
  change memory.size + (Array.replicate _ _).size = _
  rw [Array.size_replicate]
  omega

theorem World.reserved_size (w : World) : w.reserved.memory.size = max w.memory.size 96 :=
  reserveMemory_size w.memory

/-- Reserved memory has room for `k` more bytes when memory had, and low memory has. -/
theorem reserveMemory_room {memory : ByteArray} {k : Nat} (h : memory.size + k < UInt256.size)
    (hk : reservedMemory + k < UInt256.size) : (reserveMemory memory).size + k < UInt256.size := by
  rw [reserveMemory_size]
  omega

/-- The runtime entry: reserve low memory, then run the entry the exporter prints, which never
    returns, so it has no return data to give. -/
def entry (m : FeM Empty) : FeM ByteArray := do
  reserve
  m >>= fun e => nomatch e

/-- The deployment entry: reserve low memory, then run the constructor's entry the exporter
    prints, `init`, on the argument bytes. -/
def deploy (init : ByteArray → FeM ByteArray) (args : ByteArray) : FeM ByteArray := do
  reserve
  init args

/-- The runtime entry runs the exporter's entry on reserved memory. -/
theorem entry_eq (m : FeM Empty) (I : ExecutionEnv) (w : World) :
    (entry m).exec I w =
      (m >>= fun e => nomatch e : FeM ByteArray).exec I w.reserved := by
  simp only [entry, M.exec_bind, exec_reserve]

/-- The deployment entry runs the constructor's entry on reserved memory. -/
theorem deploy_bind_eq (init : ByteArray → FeM ByteArray) (args : ByteArray)
    (k : ByteArray → FeM ByteArray) (I : ExecutionEnv) (w : World) :
    (deploy init args >>= k).exec I w =
      (init args >>= k).exec I w.reserved := by
  simp only [deploy, M.exec_bind, exec_reserve]

/-- The bytecode halts for want of a resource the model does not have: gas, or room on the
    EVM's stack of 1024 words, which a deep enough recursion fills.  A caller cannot tell the two
    apart: the call fails, its changes are undone and the gas it was given is spent. -/
def Exhausted (evm : EvmResult) : Prop :=
  evm = .error .OutOfGass ∨ evm = .error .StackOverflow

/-- Refinement at fixed inputs: the bytecode runs out of gas or of stack, or some feed makes the
    model end as the bytecode does.  The feed is what the model cannot compute: the gas and the
    substate of each call it makes. -/
def RefinesFor (p : Profile) (m : ContractModel) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) : Prop :=
  Exhausted (Ξ σ σ₀ g A I)
    ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A feed))

/-- A certificate that excuses running out of gas only is one.  It shows more: the bytecode
    never overflows its stack. -/
theorem RefinesFor.of_gas {p : Profile} {m : ContractModel} {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (h : Ξ σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A feed))) :
    RefinesFor p m σ σ₀ g A I :=
  h.imp Or.inl id

/-- A certificate of a model that never consults the context, stated without a feed and
    excusing running out of gas only, is one. -/
theorem RefinesFor.closed {p : Profile} {m : ContractModel} {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (h : Ξ σ σ₀ g A I = .error .OutOfGass
      ∨ Agrees p (Ξ σ σ₀ g A I) (m.runtime.exec I (World.init σ A))) :
    RefinesFor p m σ σ₀ g A I :=
  h.imp Or.inl fun h => ⟨[], h⟩

/-- The account a frame runs at, `I.codeOwner`, exists in its account map.  The certificates
    speak only of such frames, which are the frames the EVM runs: a message call runs code only
    at an account that exists, and a creation adds the new account before it runs the init code.
    Without the account EVMLean's `SSTORE` drops the write, as `storeWord` does, so a load after
    a store reads 0, while the compiler forwards a stored value to a later load of the same slot.
    On such a frame a correct compilation and its source-level model can differ. -/
def OwnerExists (σ : AccountMap) (I : ExecutionEnv) : Prop := ∃ acc, σ[I.codeOwner]? = some acc

/-- `OwnerExists` with the lookup `slotWord` and `storeWord` make. -/
theorem ownerExists_iff_get? {σ : AccountMap} {I : ExecutionEnv} :
    OwnerExists σ I ↔ ∃ acc, σ.get? I.codeOwner = some acc := Iff.rfl

/-- The runtime bytecode refines the model on every message call that `admits` holds of, at an
    account that exists (`OwnerExists`), whatever the immutable fields after it hold. -/
def RefinesOn (p : Profile) (bytecode : ByteArray) (m : ContractModel)
    (admits : ExecutionEnv → Prop) : Prop :=
  ∀ σ σ₀ g A I tail, I.code = bytecode ++ tail → tail.size = m.immutables → OwnerExists σ I →
    admits I → RefinesFor p m σ σ₀ g A I

/-- A certificate of a contract without immutable fields is one of its runtime bytecode
    alone. -/
theorem RefinesOn.of_code {p : Profile} {bytecode : ByteArray} {m : ContractModel}
    {admits : ExecutionEnv → Prop} (hm : m.immutables = 0)
    (h : ∀ σ σ₀ g A I, I.code = bytecode → OwnerExists σ I → admits I →
      RefinesFor p m σ σ₀ g A I) :
    RefinesOn p bytecode m admits := by
  intro σ σ₀ g A I tail hcode htail hown hadmits
  have hempty : tail = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (hm ▸ htail)
  exact h σ σ₀ g A I (by rw [hcode, hempty, ByteArray.append_empty]) hown hadmits

/-- The runtime bytecode refines the model on every message call at an account that exists. -/
def Refines (p : Profile) (bytecode : ByteArray) (m : ContractModel) : Prop :=
  RefinesOn p bytecode m fun I => I.calldata.size < UInt256.size

/-- Calldata shorter than `2 ^ 64` bytes.  Fe's std reads a calldata length as a `u64`, and its
    backend assumes the length fits, so a model exported from std and the bytecode agree only on
    such calls.  No transaction comes near the bound. -/
def CalldataFits (I : ExecutionEnv) : Prop := I.calldata.size < 2 ^ 64

/-- Deployment: run with any valid argument bytes after it, at an account that exists
    (`OwnerExists`), the creation bytecode runs out of gas or of stack, or does what the model's
    constructor does, under some feed, and returns the runtime bytecode followed by the immutable
    fields the constructor computed. -/
def RefinesDeploy (p : Profile) (creation runtime : ByteArray) (m : ContractModel)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true →
    Exhausted (Ξ σ σ₀ g A I)
      ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I)
          ((m.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A feed))

/-- A deployment certificate of a constructor that never consults the context, stated without a
    feed, is one. -/
theorem RefinesDeploy.closed {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop}
    (h : ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
      I.perm = true →
      Ξ σ σ₀ g A I = .error .OutOfGass
        ∨ Agrees p (Ξ σ σ₀ g A I)
            ((m.init args >>= fun tail => pure (runtime ++ tail)).exec I (World.init σ A))) :
    RefinesDeploy p creation runtime m validArgs :=
  fun σ σ₀ g A I args hargs hcode hown hperm =>
    (h σ σ₀ g A I args hargs hcode hown hperm).imp Or.inl fun h => ⟨[], h⟩

/-- A constructor of a contract without immutable fields returns no bytes: the model's `init`
    is `init`, a computation of nothing, and the deployed code is the runtime bytecode. -/
theorem RefinesDeploy.of_unit {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop} {init : ByteArray → FeM Unit}
    (hm : ∀ args, m.init args = init args >>= fun _ => pure ByteArray.empty)
    (h : ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
      I.perm = true →
      Ξ σ σ₀ g A I = .error .OutOfGass
        ∨ ∃ feed, Agrees p (Ξ σ σ₀ g A I)
            ((init args >>= fun _ => pure runtime).exec I (World.init σ A feed))) :
    RefinesDeploy p creation runtime m validArgs := by
  intro σ σ₀ g A I args hargs hcode hown hperm
  simpa [hm, ByteArray.append_empty] using
    (h σ σ₀ g A I args hargs hcode hown hperm).imp Or.inl id

/-- `RefinesDeploy.of_unit` for a constructor that never consults the context, stated without
    a feed. -/
theorem RefinesDeploy.of_unit_closed {p : Profile} {creation runtime : ByteArray}
    {m : ContractModel} {validArgs : ByteArray → Prop} {init : ByteArray → FeM Unit}
    (hm : ∀ args, m.init args = init args >>= fun _ => pure ByteArray.empty)
    (h : ∀ σ σ₀ g A I args, validArgs args → I.code = creation ++ args → OwnerExists σ I →
      I.perm = true →
      Ξ σ σ₀ g A I = .error .OutOfGass
        ∨ Agrees p (Ξ σ σ₀ g A I)
            ((init args >>= fun _ => pure runtime).exec I (World.init σ A))) :
    RefinesDeploy p creation runtime m validArgs :=
  RefinesDeploy.of_unit hm fun σ σ₀ g A I args hargs hcode hown hperm =>
    (h σ σ₀ g A I args hargs hcode hown hperm).imp id fun h => ⟨[], h⟩

/-- A model run ends successfully: it returns, or stops from inside a callee. -/
def Succeeds (r : Option (Except (Exit World) (ByteArray × World))) (out : ByteArray)
    (w : World) : Prop :=
  r = some (.ok (out, w)) ∨ r = some (.error (.stop out w))

/-- A run that ends as another does succeeds when it does, with the same accounts and recorded
    calls. -/
theorem EndsAs.succeeds_calls {a b : Option (Except (Exit World) (ByteArray × World))}
    (h : EndsAs a b) {out : ByteArray} {w' : World} (ha : Succeeds a out w') :
    ∃ w, Succeeds b out w ∧ w.accounts = w'.accounts ∧ w.calls = w'.calls := by
  cases h with
  | stop_ok hacc _ hc | ok_ok hacc _ hc =>
    rcases ha with ha | ha <;> cases ha
    exact ⟨_, Or.inl rfl, hacc.symm, hc.symm⟩
  | stop_stop hacc _ hc | ok_stop hacc _ hc =>
    rcases ha with ha | ha <;> cases ha
    exact ⟨_, Or.inr rfl, hacc.symm, hc.symm⟩
  | exit f => exact ⟨w', ha.imp (fun h => by cases h) id, rfl, rfl⟩
  | panic_revert code | diverge => rcases ha with ha | ha <;> cases ha

/-- A run that ends as another does succeeds when it does, with the same accounts. -/
theorem EndsAs.succeeds {a b : Option (Except (Exit World) (ByteArray × World))}
    (h : EndsAs a b) {out : ByteArray} {w' : World} (ha : Succeeds a out w') :
    ∃ w, Succeeds b out w ∧ w.accounts = w'.accounts := by
  obtain ⟨w, hw, hacc, -⟩ := h.succeeds_calls ha
  exact ⟨w, hw, hacc⟩

/-- A property of the accounts every successful model run ends with, shown for every feed,
    holds of the accounts a successful EVM run ends with, when it runs out of gas or of stack
    or agrees with the model under some feed. -/
theorem Agrees.accounts {p : Profile} {evm : EvmResult}
    {run : List Supply → Option (Except (Exit World) (ByteArray × World))} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {o : ByteArray} {P : AccountMap → Prop}
    (h : Exhausted evm ∨ ∃ feed, Agrees p evm (run feed))
    (hP : ∀ feed out w, Succeeds (run feed) out w → P w.accounts)
    (hrun : evm = .ok (.success (σ', g', A') o)) : P σ' := by
  subst hrun
  rcases h with (hoog | hoog) | ⟨feed, hag⟩
  · cases hoog
  · cases hoog
  cases hm : run feed with
  | none => rw [hm] at hag; exact hag.elim
  | some res =>
    rw [hm] at hag
    cases res with
    | error f =>
      cases f with
      | revert data => obtain ⟨_, _, h, _⟩ := hag; cases h
      | panic code => obtain ⟨_, _, h, _⟩ := hag; cases h
      | static => cases hag
      | trap => cases hag
      | oob => cases hag
      | stop out w =>
        obtain ⟨_, _, h, _⟩ := hag
        injection h with h; injection h with h; injection h with h
        exact h ▸ hP feed out w (Or.inr hm)
    | ok pr =>
      obtain ⟨out, w⟩ := pr
      obtain ⟨_, _, h, _⟩ := hag
      injection h with h; injection h with h; injection h with h
      exact h ▸ hP feed out w (Or.inl hm)

/-- How a certificate is used: a property of the accounts the model can end with, shown for
    every feed, holds of the accounts the bytecode ends with. -/
theorem RefinesFor.accounts {p : Profile} {m : ContractModel} {σ σ₀ σ' : AccountMap}
    {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    {P : AccountMap → Prop} (h : RefinesFor p m σ σ₀ g A I)
    (hP : ∀ feed out w, Succeeds (m.runtime.exec I (World.init σ A feed)) out w → P w.accounts)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) : P σ' :=
  Agrees.accounts h hP hrun

/-- How a deployment certificate is used: a property of the accounts the constructor can end
    with, shown for every feed, holds of the accounts a successful deployment ends with. -/
theorem RefinesDeploy.accounts {p : Profile} {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop} {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {args o : ByteArray} {P : AccountMap → Prop}
    (h : RefinesDeploy p creation runtime m validArgs) (hargs : validArgs args)
    (hcode : I.code = creation ++ args) (hown : OwnerExists σ I) (hperm : I.perm = true)
    (hP : ∀ feed out w, Succeeds ((m.init args >>= fun tail => pure (runtime ++ tail)).exec I
      (World.init σ A feed)) out w → P w.accounts)
    (hrun : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) : P σ' :=
  Agrees.accounts (h σ σ₀ g A I args hargs hcode hown hperm) hP hrun

/-! ## `P1` is the finer profile

A result that agrees with a run at `P1` agrees with it at `P0`, so a `P1` certificate is a `P0`
one. -/

/-- `P1` agreement is `P0` agreement and more. -/
theorem Agrees.toP0 {evm : EvmResult} {r : Option (Except (Exit World) (ByteArray × World))}
    (h : Agrees .P1 evm r) : Agrees .P0 evm r := by
  unfold Agrees at h ⊢
  split <;> simp_all <;> grind

/-- A `P1` certificate of a bytecode is a `P0` one. -/
theorem RefinesOn.toP0 {code : ByteArray} {m : ContractModel} {admits : ExecutionEnv → Prop}
    (h : RefinesOn .P1 code m admits) : RefinesOn .P0 code m admits :=
  fun σ σ₀ g A I tail hc ht ho ha => (h σ σ₀ g A I tail hc ht ho ha).imp id
    fun ⟨feed, hf⟩ => ⟨feed, hf.toP0⟩

/-- A `P1` deployment certificate is a `P0` one. -/
theorem RefinesDeploy.toP0 {creation runtime : ByteArray} {m : ContractModel}
    {validArgs : ByteArray → Prop} (h : RefinesDeploy .P1 creation runtime m validArgs) :
    RefinesDeploy .P0 creation runtime m validArgs :=
  fun σ σ₀ g A I args hv hc ho hp => (h σ σ₀ g A I args hv hc ho hp).imp id
    fun ⟨feed, hf⟩ => ⟨feed, hf.toP0⟩

end Fe.EVM
