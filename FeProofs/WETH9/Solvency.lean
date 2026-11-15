import FeProofs.WETH9.Model
import Fe.EVM.Invariant
import Reasoning.EVMWord

/-!
# FeWETH9: the model stays solvent

A property of the hand-written model alone: the ether the contract holds covers the tokens its
storage records.  `Solvent acc`: for every list of keys whose balance slots are pairwise
distinct, the words at those slots add up to at most the account's balance.  Quantifying over
every such list makes it a predicate on the account alone, with no list of holders: two keys
whose balance slots coincide share one balance, which is counted once.

## The arms

- The getters change nothing.
- `approve` writes an allowance slot: it must be no key's balance slot (`Admits`).
- `transfer` and `transferFrom` move tokens between two balance slots, after `transferFrom` writes
  an allowance slot when the caller spends another's tokens, which must again be no key's balance
  slot.  The additions wrap on the EVM, but not here: taking the two keys as the list, the two
  balances add up to at most the contract's ether, which is below `2 ^ 256`.
- `deposit` and the fallback credit the caller with the call value.  Solvency holds of the
  account as it was before the value arrived, and the arm needs its ether to have risen by the
  call value (`deposit_solvent`).  That fails for a call from the contract to itself with value,
  which moves no ether: such a frame credits tokens it is not paid for, and must not be admitted.
  WETH9 calls only its caller, so it never calls itself, but the per-frame statement must exclude
  it.
- `withdraw` debits the caller, then sends the ether.  Before the call, the account is solvent
  with the tokens debited, and still with the ether gone (`withdraw_debit`); the call is
  whatever `Θ` returns, recorded (`withdraw_run`), and the run ends with its accounts: solvency
  after it is a hypothesis on each recorded call (`withdraw_solvent`), which the invariant
  discharges from `Deeper`.  `withdrawCall_*` and `recorded_call` give what `GoodTheta` asks
  of that call.

`runtime_solvent` puts the arms together: a run of the runtime entry that returns, admitted
(`Admits`), from an account that was solvent before the call's value arrived and has gained the
value since, ends solvent, if each call it records ends solvent.  `runtime_keeps` states it in
the terms of `ModelKeeps` (`entry_account`), through `noStop_runtime`: every run that succeeds
returns.  `runtime_calls` and `runtime_recorded`: a run records nothing or exactly the call
`withdraw` makes.

Storage writes do not change the sum of all balances (`total_storeWord`), which a model needs to
carry `total σ < 2 ^ 256` to its call.

## The constructor

It writes the heads of `name` and `symbol` at slots 0 and 1, and `decimals` at slot 2, from an
account whose storage is empty.  It keeps solvency if no key's balance slot is one of those
three (`init_solvent`).
-/

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM Reasoning.Theory

namespace FeProofs.WETH9

open Model

/-! ## The invariant -/

/-- The word at `slot` of an account's storage, as a natural number. -/
def tokens (acc : Account) (slot : UInt256) : ℕ := (acc.storage.getD slot ⟨0⟩).toNat

/-- The ether the account holds covers the tokens at every set of distinct balance slots. -/
def Solvent (acc : Account) : Prop :=
  ∀ S : List UInt256, (S.map balanceSlot).Nodup →
    (S.map fun h => tokens acc (balanceSlot h)).sum ≤ acc.balance.toNat

/-- The account at `a`, if any, is solvent. -/
def SolventAt (a : AccountAddress) (σ : AccountMap) : Prop :=
  ∀ acc, σ[a]? = some acc → Solvent acc

/-- The contract's account: it runs `code` and is solvent. -/
def Weth (code : ByteArray) (acc : Account) : Prop := acc.code = code ∧ Solvent acc

/-- `Solvent` over finite sets of balance slots, with the tokens and the ether apart. -/
def SolventF (g : UInt256 → ℕ) (B : ℕ) : Prop :=
  ∀ T : Finset UInt256, (∀ t ∈ T, ∃ h, balanceSlot h = t) → ∑ t ∈ T, g t ≤ B

theorem exists_keys (T : Finset UInt256) (hT : ∀ t ∈ T, ∃ h, balanceSlot h = t) :
    ∃ S : List UInt256, (S.map balanceSlot).Nodup ∧ (S.map balanceSlot).toFinset = T := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[], List.nodup_nil, rfl⟩
  | insert t T ht ih =>
    obtain ⟨S, hnd, hS⟩ := ih fun u hu => hT u (Finset.mem_insert_of_mem hu)
    obtain ⟨h, rfl⟩ := hT _ (Finset.mem_insert_self _ _)
    refine ⟨h :: S, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      exact ⟨fun hm => ht (hS ▸ List.mem_toFinset.mpr hm), hnd⟩
    · rw [List.map_cons, List.toFinset_cons, hS]

theorem solvent_iff (acc : Account) : Solvent acc ↔ SolventF (tokens acc) acc.balance.toNat := by
  constructor
  · intro h T hT
    obtain ⟨S, hnd, rfl⟩ := exists_keys T hT
    rw [List.sum_toFinset _ hnd, List.map_map]
    exact h S hnd
  · intro h S hnd
    have := h (S.map balanceSlot).toFinset fun t ht => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact ⟨k, rfl⟩
    rwa [List.sum_toFinset _ hnd, List.map_map] at this

/-! ## How solvency changes -/

section Core

variable {g g' : UInt256 → ℕ} {B B' : ℕ}

/-- No more tokens at any balance slot, and no less ether. -/
theorem SolventF.mono_le (h : SolventF g B) (hg : ∀ k, g' (balanceSlot k) ≤ g (balanceSlot k))
    (hB : B ≤ B') : SolventF g' B' := by
  intro T hT
  refine le_trans (Finset.sum_le_sum fun t ht => ?_) ((h T hT).trans hB)
  obtain ⟨k, rfl⟩ := hT t ht
  exact hg k

/-- Tokens unchanged at every balance slot, and no less ether. -/
theorem SolventF.mono (h : SolventF g B) (hg : ∀ k, g' (balanceSlot k) = g (balanceSlot k))
    (hB : B ≤ B') : SolventF g' B' :=
  h.mono_le (fun k => (hg k).le) hB

/-- Tokens at one balance slot that held at least `v` reduced by `v`: the ether may go down by
    `v` too. -/
theorem SolventF.debit (h : SolventF g B) (k : UInt256) {v : ℕ} (hv : v ≤ g (balanceSlot k))
    (hs : g' (balanceSlot k) + v = g (balanceSlot k))
    (hg : ∀ t, t ≠ balanceSlot k → (∃ h, balanceSlot h = t) → g' t = g t) :
    v ≤ B ∧ SolventF g' (B - v) := by
  have hins : ∀ T : Finset UInt256, (∀ t ∈ T, ∃ h, balanceSlot h = t) →
      (∑ t ∈ insert (balanceSlot k) T, g' t) + v = ∑ t ∈ insert (balanceSlot k) T, g t := by
    intro T hT
    have hmem := Finset.mem_insert_self (balanceSlot k) T
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
      Finset.sum_congr rfl fun t ht => hg t (Finset.ne_of_mem_erase ht)
        (by rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase ht) with h | h
            · exact ⟨k, h.symm⟩
            · exact hT t h)]
    linarith
  have hsub : ∀ T : Finset UInt256, (∀ t ∈ T, ∃ h, balanceSlot h = t) →
      ∀ t ∈ insert (balanceSlot k) T, ∃ h, balanceSlot h = t := fun T hT t ht => by
    rcases Finset.mem_insert.mp ht with h | h
    · exact ⟨k, h.symm⟩
    · exact hT t h
  refine ⟨?_, fun T hT => ?_⟩
  · have h1 := h {balanceSlot k} fun t ht => ⟨k, (Finset.mem_singleton.mp ht).symm⟩
    rw [Finset.sum_singleton] at h1
    omega
  · have h1 := hins T hT
    have h2 := h _ (hsub T hT)
    have h3 := Finset.sum_le_sum_of_subset (f := g') (Finset.subset_insert (balanceSlot k) T)
    omega

/-- Tokens at one balance slot raised by `v`: the ether must go up by `v` too. -/
theorem SolventF.credit (h : SolventF g B) (k : UInt256) {v : ℕ}
    (hs : g' (balanceSlot k) = g (balanceSlot k) + v)
    (hg : ∀ t, t ≠ balanceSlot k → (∃ h, balanceSlot h = t) → g' t = g t) :
    SolventF g' (B + v) := by
  intro T hT
  have hle : ∑ t ∈ T, g' t ≤ (∑ t ∈ T, g t) + v := by
    by_cases hmem : balanceSlot k ∈ T
    · rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
        Finset.sum_congr rfl fun t ht => hg t (Finset.ne_of_mem_erase ht)
          (hT t (Finset.mem_of_mem_erase ht)), hs]
      linarith
    · rw [Finset.sum_congr rfl fun t ht => hg t (fun he => hmem (he ▸ ht)) (hT t ht)]
      linarith
  exact hle.trans (Nat.add_le_add_right (h T hT) v)

/-- Two balances below the ether: no addition to one of them up to the other wraps. -/
theorem SolventF.pair (h : SolventF g B) {k k' : UInt256}
    (hne : balanceSlot k ≠ balanceSlot k') :
    g (balanceSlot k) + g (balanceSlot k') ≤ B := by
  have := h {balanceSlot k, balanceSlot k'} fun t ht => by
    rcases Finset.mem_insert.mp ht with h | h
    · exact ⟨k, h.symm⟩
    · exact ⟨k', (Finset.mem_singleton.mp h).symm⟩
  rwa [Finset.sum_pair hne] at this

theorem SolventF.single (h : SolventF g B) (k : UInt256) : g (balanceSlot k) ≤ B := by
  have := h {balanceSlot k} fun t ht => ⟨k, (Finset.mem_singleton.mp ht).symm⟩
  rwa [Finset.sum_singleton] at this

end Core

/-! ## Storage writes -/

/-- The account after the contract stores `val` at `slot`, as `storeWord` writes it. -/
def storeAcc (acc : Account) (slot val : UInt256) : Account :=
  if val == default then { acc with storage := acc.storage.erase slot }
  else { acc with storage := acc.storage.insert slot val }

theorem storeWord_some {a : AccountAddress} {σ : AccountMap} {acc : Account}
    (h : σ[a]? = some acc) (slot val : UInt256) :
    storeWord a σ slot val = σ.insert a (storeAcc acc slot val) := by
  unfold storeWord storeAcc
  rw [Std.ExtTreeMap.get?_eq_getElem?, h]
  rfl

theorem storeWord_none {a : AccountAddress} {σ : AccountMap} (h : σ[a]? = none)
    (slot val : UInt256) : storeWord a σ slot val = σ := by
  unfold storeWord
  rw [Std.ExtTreeMap.get?_eq_getElem?, h]
  rfl

@[simp] theorem storeAcc_balance (acc : Account) (slot val : UInt256) :
    (storeAcc acc slot val).balance = acc.balance := by
  unfold storeAcc; split <;> rfl

@[simp] theorem storeAcc_code (acc : Account) (slot val : UInt256) :
    (storeAcc acc slot val).code = acc.code := by
  unfold storeAcc; split <;> rfl

theorem tokens_storeAcc (acc : Account) (slot val t : UInt256) :
    tokens (storeAcc acc slot val) t = if t = slot then val.toNat else tokens acc t := by
  unfold storeAcc tokens
  have hc : (compare slot t = .eq) ↔ t = slot := by
    rw [Std.LawfulEqCmp.compare_eq_iff_eq]; exact eq_comm
  split
  · rename_i hv
    have hv : val = ⟨0⟩ := by simpa using! hv
    rw [Std.ExtTreeMap.getD_erase]
    by_cases ht : t = slot
    · rw [ite_eq_left (hc.mpr ht), ite_eq_left ht, hv]
    · rw [ite_eq_right (mt hc.mp ht), ite_eq_right ht]
  · rw [Std.ExtTreeMap.getD_insert]
    by_cases ht : t = slot
    · rw [ite_eq_left (hc.mpr ht), ite_eq_left ht]
    · rw [ite_eq_right (mt hc.mp ht), ite_eq_right ht]

theorem getElem?_storeWord {a : AccountAddress} {σ : AccountMap} (slot val : UInt256) :
    (storeWord a σ slot val)[a]? = (σ[a]?).map fun acc => storeAcc acc slot val := by
  cases h : σ[a]? with
  | none => rw [storeWord_none h, h]; rfl
  | some acc => rw [storeWord_some h]; simp

/-- **Storage writes keep the sum of all balances.** -/
theorem total_storeWord (a : AccountAddress) (σ : AccountMap) (slot val : UInt256) :
    total (storeWord a σ slot val) = total σ := by
  cases h : σ[a]? with
  | none => rw [storeWord_none h]
  | some acc => rw [storeWord_some h]; exact total_insert_same h (storeAcc_balance _ _ _)

/-- The word `sload` reads, from the account. -/
theorem slotWord_of {I : Env} {σ : AccountMap} {acc : Account} (h : σ[I.codeOwner]? = some acc)
    (slot : UInt256) : (slotWord I σ slot).toNat = tokens acc slot := by
  unfold slotWord tokens
  rw [Std.ExtTreeMap.get?_eq_getElem?, h]
  rfl

/-- A write to a slot that is no key's balance slot keeps solvency. -/
theorem solvent_storeAcc_other {acc : Account} (h : Solvent acc) {slot : UInt256}
    (hslot : ∀ k, slot ≠ balanceSlot k) (val : UInt256) : Solvent (storeAcc acc slot val) := by
  rw [solvent_iff] at h ⊢
  refine h.mono (fun k => ?_) (by simp)
  rw [tokens_storeAcc, ite_eq_right (hslot k).symm]

theorem SolventAt.storeWord_other {a : AccountAddress} {σ : AccountMap} (h : SolventAt a σ)
    {slot : UInt256} (hslot : ∀ k, slot ≠ balanceSlot k) (val : UInt256) :
    SolventAt a (storeWord a σ slot val) := by
  intro acc' hacc'
  rw [getElem?_storeWord] at hacc'
  obtain ⟨acc, hacc, rfl⟩ := Option.map_eq_some_iff.mp hacc'
  exact solvent_storeAcc_other (h acc hacc) hslot val

/-- A zero written anywhere keeps solvency. -/
theorem solvent_storeAcc_zero {acc : Account} (h : Solvent acc) (slot : UInt256) :
    Solvent (storeAcc acc slot ⟨0⟩) := by
  rw [solvent_iff] at h ⊢
  refine h.mono_le (fun k => ?_) (by simp)
  rw [tokens_storeAcc]
  split
  · exact Nat.zero_le _
  · exact le_rfl

/-- Solvency of the account at `a`, or of an empty one if there is none. -/
def SolventAt' (a : AccountAddress) (σ : AccountMap) : Prop := Solvent (σ.getD a default)

theorem getD_storeWord {a : AccountAddress} {σ : AccountMap} {slot val : UInt256}
    {acc : Account} (h : σ[a]? = some acc) :
    (storeWord a σ slot val).getD a default = storeAcc acc slot val := by
  rw [storeWord_some h, Std.ExtTreeMap.getD_insert_self]

theorem SolventAt'.storeWord {a : AccountAddress} {σ : AccountMap} (h : SolventAt' a σ)
    {slot val : UInt256} (hok : (∀ k, slot ≠ balanceSlot k) ∨ val = ⟨0⟩) :
    SolventAt' a (storeWord a σ slot val) := by
  unfold SolventAt' at h ⊢
  cases hacc : σ[a]? with
  | none => rw [storeWord_none hacc]; exact h
  | some acc =>
    rw [getD_storeWord hacc]
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hacc] at h
    rcases hok with hok | rfl
    · exact solvent_storeAcc_other h hok val
    · exact solvent_storeAcc_zero h slot

/-- An account with empty storage holds no tokens. -/
theorem solvent_of_empty {acc : Account} (h : acc.storage = default) : Solvent acc := by
  intro S _
  have : ∀ t, tokens acc t = 0 := fun t => by unfold tokens; rw [h]; rfl
  simp [this]

/-! ## Moving tokens -/

theorem sub_toNat {a b : UInt256} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  usub_toNat h

/-- Moving `v` tokens from the balance slot of `src`, which holds at least `v`, to that of `dst`,
    with the arithmetic of the model: the second write reads the slot after the first. -/
theorem solvent_move {acc : Account} (h : Solvent acc) (src dst v : UInt256)
    (hv : v.toNat ≤ tokens acc (balanceSlot src)) :
    let acc₂ := storeAcc acc (balanceSlot src) (acc.storage.getD (balanceSlot src) ⟨0⟩ - v)
    Solvent (storeAcc acc₂ (balanceSlot dst) (acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v)) := by
  intro acc₂
  have hx : (acc.storage.getD (balanceSlot src) ⟨0⟩ - v).toNat =
      tokens acc (balanceSlot src) - v.toNat :=
    sub_toNat hv
  have h₂ : ∀ t, tokens acc₂ t =
      if t = balanceSlot src then tokens acc (balanceSlot src) - v.toNat else tokens acc t := by
    intro t; rw [tokens_storeAcc, hx]
  rw [solvent_iff] at h ⊢
  by_cases hsd : balanceSlot dst = balanceSlot src
  · -- one slot: the tokens come back where they were
    have hback : acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v =
        acc.storage.getD (balanceSlot src) ⟨0⟩ := by
      apply u256_inj
      have : (acc₂.storage.getD (balanceSlot dst) ⟨0⟩).toNat =
          tokens acc (balanceSlot src) - v.toNat := by
        have := h₂ (balanceSlot dst); rw [ite_eq_left hsd] at this; exact this
      have hlt : (acc.storage.getD (balanceSlot src) ⟨0⟩).toNat < UInt256.size :=
        (acc.storage.getD (balanceSlot src) ⟨0⟩).val.isLt
      unfold tokens at hv this
      rw [UInt256.toNat_add_of_lt (by omega), this]
      omega
    refine h.mono (fun k => ?_) (by simp [acc₂])
    rw [tokens_storeAcc, hback, h₂]
    by_cases hk : balanceSlot k = balanceSlot src
    · rw [ite_eq_left (hk.trans hsd.symm), hk]; rfl
    · rw [ite_eq_right (fun he => hk (he.trans hsd)), ite_eq_right hk]
  · obtain ⟨hB, h₂s⟩ := h.debit src hv (g' := tokens acc₂)
      (by rw [h₂, ite_eq_left rfl]; omega) (fun t ht _ => by rw [h₂, ite_eq_right ht])
    have hy : (acc₂.storage.getD (balanceSlot dst) ⟨0⟩).toNat = tokens acc (balanceSlot dst) := by
      have := h₂ (balanceSlot dst); rw [ite_eq_right hsd] at this; exact this
    have hpair := h.pair (Ne.symm hsd)
    have hbal : acc.balance.toNat < UInt256.size := acc.balance.val.isLt
    have hadd : (acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v).toNat =
        tokens acc₂ (balanceSlot dst) + v.toNat := by
      rw [UInt256.toNat_add_of_lt (by rw [hy]; omega)]; rfl
    have h₃ := h₂s.credit dst (g' := tokens (storeAcc acc₂ (balanceSlot dst)
        (acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v)))
      (by rw [tokens_storeAcc, ite_eq_left rfl, hadd]) (fun t ht _ => by rw [tokens_storeAcc, ite_eq_right ht])
    rw [Nat.sub_add_cancel hB] at h₃
    simpa [acc₂] using h₃

/-- Debiting `v` tokens from the balance slot of `src`, which holds at least `v`: still solvent,
    and with `v` of the ether gone. -/
theorem solvent_debit {acc : Account} (h : Solvent acc) (src v : UInt256)
    (hv : v.toNat ≤ tokens acc (balanceSlot src)) :
    let acc₂ := storeAcc acc (balanceSlot src) (acc.storage.getD (balanceSlot src) ⟨0⟩ - v)
    Solvent acc₂ ∧ v.toNat ≤ acc₂.balance.toNat ∧
      Solvent { acc₂ with balance := acc₂.balance - v } := by
  intro acc₂
  have hx : (acc.storage.getD (balanceSlot src) ⟨0⟩ - v).toNat =
      tokens acc (balanceSlot src) - v.toNat := sub_toNat hv
  rw [solvent_iff] at h
  obtain ⟨hB, h₂⟩ := h.debit src hv (g' := tokens acc₂)
    (by rw [tokens_storeAcc, ite_eq_left rfl, hx]; omega)
    (fun t ht _ => by rw [tokens_storeAcc, ite_eq_right ht])
  have hb : acc₂.balance = acc.balance := storeAcc_balance _ _ _
  refine ⟨(solvent_iff _).mpr (h₂.mono (fun _ => rfl) (by rw [hb]; omega)), by rw [hb]; exact hB,
    (solvent_iff _).mpr (h₂.mono (fun _ => rfl) ?_)⟩
  show acc.balance.toNat - v.toNat ≤ (acc₂.balance - v).toNat
  rw [hb, sub_toNat hB]

/-- Crediting `v` tokens to the balance slot of `dst`, on an account whose ether rose by `v`
    since it was solvent. -/
theorem solvent_credit {acc₀ acc : Account} {v : UInt256} (h : Solvent acc₀)
    (hst : acc.storage = acc₀.storage)
    (hbal : acc.balance.toNat = acc₀.balance.toNat + v.toNat) (dst : UInt256) :
    Solvent (storeAcc acc (balanceSlot dst) (acc.storage.getD (balanceSlot dst) ⟨0⟩ + v)) := by
  rw [solvent_iff] at h ⊢
  have hle := h.single dst
  have htok : ∀ t, tokens acc t = tokens acc₀ t := fun t => by unfold tokens; rw [hst]
  have hlt : acc.balance.toNat < UInt256.size := acc.balance.val.isLt
  have hadd : (acc.storage.getD (balanceSlot dst) ⟨0⟩ + v).toNat =
      tokens acc₀ (balanceSlot dst) + v.toNat := by
    rw [UInt256.toNat_add_of_lt (by rw [← htok] at hle; unfold tokens at hle; omega), ← htok]; rfl
  have := h.credit dst (g' := tokens (storeAcc acc (balanceSlot dst)
      (acc.storage.getD (balanceSlot dst) ⟨0⟩ + v)))
    (by rw [tokens_storeAcc, ite_eq_left rfl, hadd])
    (fun t ht _ => by rw [tokens_storeAcc, ite_eq_right ht, htok])
  rw [storeAcc_balance, hbal]
  exact this

/-! ## Moving tokens in the account map -/

theorem slotWord_some {I : Env} {σ : AccountMap} {acc : Account} (h : σ[I.codeOwner]? = some acc)
    (slot : UInt256) : slotWord I σ slot = acc.storage.getD slot ⟨0⟩ := by
  unfold slotWord
  rw [Std.ExtTreeMap.get?_eq_getElem?, h]
  rfl

theorem slotWord_storeWord_ne {I : Env} (σ : AccountMap) {slot t : UInt256} (h : t ≠ slot)
    (v : UInt256) : slotWord I (storeWord I.codeOwner σ slot v) t = slotWord I σ t := by
  cases hacc : σ[I.codeOwner]? with
  | none => rw [storeWord_none hacc]
  | some acc =>
    have h' : (storeWord I.codeOwner σ slot v)[I.codeOwner]? = some (storeAcc acc slot v) := by
      rw [getElem?_storeWord, hacc]; rfl
    exact u256_inj (by rw [slotWord_of h', slotWord_of hacc, tokens_storeAcc, ite_eq_right h])

/-- `solvent_move`, as `transferFrom` writes the account map. -/
theorem SolventAt.move {I : Env} {σ : AccountMap} (h : SolventAt I.codeOwner σ)
    (src dst v : UInt256) (hv : ¬ (slotWord I σ (balanceSlot src)).toNat < v.toNat) :
    SolventAt I.codeOwner
      (storeWord I.codeOwner
        (storeWord I.codeOwner σ (balanceSlot src) (slotWord I σ (balanceSlot src) - v))
        (balanceSlot dst)
        (slotWord I (storeWord I.codeOwner σ (balanceSlot src) (slotWord I σ (balanceSlot src) - v))
          (balanceSlot dst) + v)) := by
  generalize hσ₂def : storeWord I.codeOwner σ (balanceSlot src)
    (slotWord I σ (balanceSlot src) - v) = σ₂
  cases hacc : σ[I.codeOwner]? with
  | none =>
    have h₂ : σ₂ = σ := hσ₂def ▸ storeWord_none hacc _ _
    rw [h₂, storeWord_none hacc]
    exact h
  | some acc =>
    have hσ₂ : σ₂ = σ.insert I.codeOwner (storeAcc acc (balanceSlot src)
        (acc.storage.getD (balanceSlot src) ⟨0⟩ - v)) := by
      rw [← hσ₂def, storeWord_some hacc, slotWord_some hacc]
    have h₂ : σ₂[I.codeOwner]? = some (storeAcc acc (balanceSlot src)
        (acc.storage.getD (balanceSlot src) ⟨0⟩ - v)) := by rw [hσ₂]; simp
    rw [storeWord_some h₂, slotWord_some h₂]
    intro acc' hacc'
    simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hacc'
    subst hacc'
    rw [slotWord_of hacc] at hv
    exact solvent_move (h acc hacc) src dst v (Nat.le_of_not_lt hv)

/-! ## The arms -/

section Arms

variable {I : Env} {w w' : World}

/-- **`approve`**: it writes an allowance slot, which must be no key's balance slot. -/
theorem approve_solvent {guy wad : UInt256} {r : Bool}
    (hrun : (approve guy wad).exec I w = some (.ok (r, w')))
    (hadm : ∀ k, allowanceSlot (UInt256.ofNat I.source.val) guy ≠ balanceSlot k)
    (h : SolventAt I.codeOwner w.accounts) : SolventAt I.codeOwner w'.accounts := by
  by_cases hp : I.perm = true
  · simp [approve, exec_sstore, exec_emit, hp] at hrun
    rw [← hrun.2]
    exact h.storeWord_other hadm _
  · simp [approve, exec_sstore, hp] at hrun

/-- **`transfer` and `transferFrom`**: the tokens move between two balance slots.  When the
    caller spends another's tokens, the allowance slot written must be no key's balance slot. -/
theorem transferFrom_solvent {src dst wad : UInt256} {r : Bool}
    (hrun : (transferFrom src dst wad).exec I w = some (.ok (r, w')))
    (hadm : src ≠ UInt256.ofNat I.source.val →
      ∀ k, allowanceSlot src (UInt256.ofNat I.source.val) ≠ balanceSlot k)
    (h : SolventAt I.codeOwner w.accounts) : SolventAt I.codeOwner w'.accounts := by
  have hmove := fun σ (hσ : SolventAt I.codeOwner σ)
    (hv : ¬ (slotWord I σ (balanceSlot src)).toNat < wad.toNat) => hσ.move src dst wad hv
  by_cases hlt : (slotWord I w.accounts (balanceSlot src)).toNat < wad.toNat
  · simp [transferFrom, hlt] at hrun
  by_cases hp : I.perm = true
  swap
  · by_cases hs : src = UInt256.ofNat I.source.val
    · subst hs; simp [transferFrom, hlt, exec_sstore, hp] at hrun
    · by_cases hmax : slotWord I w.accounts (allowanceSlot src (UInt256.ofNat I.source.val)) =
          UInt256.ofNat (UInt256.size - 1)
      · simp [transferFrom, hlt, hs, hmax, exec_sstore, hp] at hrun
      · by_cases hal : (slotWord I w.accounts (allowanceSlot src
            (UInt256.ofNat I.source.val))).toNat < wad.toNat
        · simp [transferFrom, hlt, hs, hmax, hal] at hrun
        · simp [transferFrom, hlt, hs, hmax, hal, exec_sstore, hp] at hrun
  by_cases hs : src = UInt256.ofNat I.source.val
  · subst hs
    simp [transferFrom, hlt, exec_sstore, exec_emit, hp] at hrun
    rw [← hrun.2]
    exact hmove _ h hlt
  by_cases hmax : slotWord I w.accounts (allowanceSlot src (UInt256.ofNat I.source.val)) =
      UInt256.ofNat (UInt256.size - 1)
  · simp [transferFrom, hlt, hs, hmax, exec_sstore, exec_emit, hp] at hrun
    rw [← hrun.2]
    exact hmove _ h hlt
  by_cases hal : (slotWord I w.accounts (allowanceSlot src
      (UInt256.ofNat I.source.val))).toNat < wad.toNat
  · simp [transferFrom, hlt, hs, hmax, hal] at hrun
  simp [transferFrom, hlt, hs, hmax, hal, exec_sstore, exec_emit, hp] at hrun
  rw [← hrun.2]
  have h₁ := h.storeWord_other (hadm hs) (slotWord I w.accounts
    (allowanceSlot src (UInt256.ofNat I.source.val)) - wad)
  have hv := slotWord_storeWord_ne (I := I) w.accounts (hadm hs src).symm
    (slotWord I w.accounts (allowanceSlot src (UInt256.ofNat I.source.val)) - wad)
  rw [← hv] at hlt
  exact hmove _ h₁ hlt

/-- **`deposit` and the fallback**: the caller is credited with the call value.  The account was
    solvent as `acc₀` before the value arrived, and its ether has risen by the value since. -/
theorem deposit_solvent {acc₀ acc : Account} (hrun : deposit.exec I w = some (.ok ((), w')))
    (h₀ : Solvent acc₀) (hacc : w.accounts[I.codeOwner]? = some acc)
    (hst : acc.storage = acc₀.storage)
    (hbal : acc.balance.toNat = acc₀.balance.toNat + I.weiValue.toNat) :
    SolventAt I.codeOwner w'.accounts := by
  by_cases hp : I.perm = true
  · simp [deposit, callvalue, exec_sstore, exec_emit, hp] at hrun
    rw [← hrun, storeWord_some hacc, slotWord_some hacc]
    intro acc' hacc'
    simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hacc'
    subst hacc'
    exact solvent_credit h₀ hst hbal _
  · simp [deposit, callvalue, exec_sstore, hp] at hrun

theorem depositArm_solvent {acc₀ acc : Account} {r : ByteArray}
    (hrun : depositArm.exec I w = some (.ok (r, w'))) (h₀ : Solvent acc₀)
    (hacc : w.accounts[I.codeOwner]? = some acc) (hst : acc.storage = acc₀.storage)
    (hbal : acc.balance.toNat = acc₀.balance.toNat + I.weiValue.toNat) :
    SolventAt I.codeOwner w'.accounts := by
  simp only [depositArm, M.exec_bind] at hrun
  cases hd : deposit.exec I w with
  | none => rw [hd] at hrun; cases hrun
  | some res =>
    rw [hd] at hrun
    rcases res with f | ⟨⟨⟩, v⟩
    · cases hrun
    · simp only [M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hrun
      rw [← hrun.2]
      exact deposit_solvent hd h₀ hacc hst hbal

/-! ### The getters change nothing -/

theorem totalSupply_world {r : UInt256} (hrun : totalSupply.exec I w = some (.ok (r, w'))) :
    w' = w := by
  simp [totalSupply, selfbalance] at hrun; exact hrun.2.symm

theorem decimals_world {r : UInt256} (hrun : decimals.exec I w = some (.ok (r, w'))) : w' = w := by
  simp [decimals] at hrun; exact hrun.2.symm

theorem balanceOf_world {owner r : UInt256}
    (hrun : (balanceOf owner).exec I w = some (.ok (r, w'))) : w' = w := by
  simp [balanceOf] at hrun; exact hrun.2.symm

theorem allowance_world {owner guy r : UInt256}
    (hrun : (allowance owner guy).exec I w = some (.ok (r, w'))) : w' = w := by
  simp [allowance] at hrun; exact hrun.2.symm

theorem stringReturn_world {slot : UInt256} {r : ByteArray}
    (hrun : (stringReturn slot).exec I w = some (.ok (r, w'))) : w' = w := by
  unfold stringReturn at hrun
  simp only [M.exec_bind, M.exec_read, M.exec_get] at hrun
  split at hrun
  · split at hrun
    · simp at hrun; exact hrun.2.symm
    · simp at hrun
  · simp at hrun

/-! ### `withdraw` -/

/-- The payer's account after a value transfer: the same storage and code, and the same balance
    (paying itself) or the value less. -/
theorem sendEth_payer {σ : AccountMap} {r s : AccountAddress} {v : UInt256} {acc : Account}
    (h : σ[s]? = some acc) :
    ∃ acc', (sendEth r s v true σ)[s]? = some acc' ∧ acc'.storage = acc.storage ∧
      acc'.code = acc.code ∧ (acc'.balance = acc.balance ∨ acc'.balance = acc.balance - v) := by
  by_cases hrs : r = s
  · subst hrs
    refine ⟨{ acc with balance := acc.balance + v - v }, ?_, rfl, rfl,
      Or.inl (UInt256.add_sub_cancel' _ _)⟩
    simp [sendEth, Std.ExtTreeMap.get?_eq_getElem?, h]
  · refine ⟨{ acc with balance := acc.balance - v }, ?_, rfl, rfl, Or.inr rfl⟩
    have hne : ¬ compare r s = .eq := fun he => hrs (Std.LawfulEqCmp.eq_of_compare he)
    unfold sendEth
    rcases hr : σ[r]? with _ | accr
    · by_cases hv : (v != UInt256.ofNat 0) = true
      · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, h, hr, hv]
      · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hv
        simp [Std.ExtTreeMap.get?_eq_getElem?, h, hr, hv]
    · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, h, hr]

/-- The payee's account after a value transfer from another account that has the value, with
    the balances adding up to less than `2 ^ 256`: the same storage and code, and the balance
    risen by the value, without wrapping. -/
theorem sendEth_payee {σ : AccountMap} {r s : AccountAddress} {v : UInt256} {acc : Account}
    (h : σ[r]? = some acc) (hne : s ≠ r) (hv : v ≤ balOf σ s) (hT : total σ < UInt256.size) :
    ∃ acc', (sendEth r s v true σ)[r]? = some acc' ∧ acc'.storage = acc.storage ∧
      acc'.code = acc.code ∧ acc'.balance.toNat = acc.balance.toNat + v.toNat := by
  have hle : acc.balance.toNat + v.toNat < UInt256.size := by
    cases hs : σ[s]? with
    | none =>
      rw [balOf_of_none hs] at hv
      rw [UInt256.eq_zero_of_le_zero hv]
      exact (balance_le_total h).trans_lt hT
    | some y =>
      rw [balOf_of_some hs] at hv
      have := two_le_total h hs hne.symm
      have hv' : v.toNat ≤ y.balance.toNat := hv
      omega
  refine ⟨{ acc with balance := acc.balance + v }, ?_, rfl, rfl,
    UInt256.toNat_add_of_lt hle⟩
  have hne' : ¬ compare s r = .eq := fun he => hne (Std.LawfulEqCmp.eq_of_compare he)
  have hne'' : ¬ compare r s = .eq := fun he => hne (Std.LawfulEqCmp.eq_of_compare he).symm
  unfold sendEth
  rcases hs : σ[s]? with _ | accs
  · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne'', h, hs]
  · simp only [ite_true, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert,
      ite_eq_right hne', ite_eq_right hne'', h, hs, Std.compare_self, ite_true]

/-- **Up to the call.**  `withdraw` debits the caller's balance slot, which holds at least
    `wad`.  The account is solvent after the debit, still with `wad` of its ether gone, and so
    after the value transfer of the call; and the sum of all balances is as it was. -/
theorem withdraw_debit {σ : AccountMap} {acc : Account} (hacc : σ[I.codeOwner]? = some acc)
    (h : Solvent acc) {wad : UInt256}
    (hv : ¬ (slotWord I σ (balanceSlot (UInt256.ofNat I.source.val))).toNat < wad.toNat)
    (r : AccountAddress) :
    let σ₁ := storeWord I.codeOwner σ (balanceSlot (UInt256.ofNat I.source.val))
      (slotWord I σ (balanceSlot (UInt256.ofNat I.source.val)) - wad)
    SolventAt I.codeOwner σ₁ ∧ SolventAt I.codeOwner (sendEth r I.codeOwner wad true σ₁)
      ∧ total σ₁ = total σ := by
  intro σ₁
  rw [slotWord_of hacc] at hv
  obtain ⟨h₁, -, h₂⟩ := solvent_debit h (UInt256.ofNat I.source.val) wad (Nat.le_of_not_lt hv)
  have hσ₁ : σ₁[I.codeOwner]? = some (storeAcc acc (balanceSlot (UInt256.ofNat I.source.val))
      (acc.storage.getD (balanceSlot (UInt256.ofNat I.source.val)) ⟨0⟩ - wad)) := by
    show (storeWord _ _ _ _)[I.codeOwner]? = _
    rw [storeWord_some hacc, slotWord_some hacc]; simp
  generalize storeAcc acc (balanceSlot (UInt256.ofNat I.source.val))
    (acc.storage.getD (balanceSlot (UInt256.ofNat I.source.val)) ⟨0⟩ - wad) = acc₂ at h₁ h₂ hσ₁
  refine ⟨fun acc' hacc' => ?_, fun acc' hacc' => ?_, total_storeWord _ _ _ _⟩
  · rw [hσ₁] at hacc'; cases hacc'; exact h₁
  · obtain ⟨acc'', h'', hst, -, hb⟩ := sendEth_payer (r := r) (v := wad) hσ₁
    rw [h''] at hacc'; cases hacc'
    rw [solvent_iff] at h₁ h₂ ⊢
    have htok : tokens acc' = tokens acc₂ := funext fun t => by unfold tokens; rw [hst]
    rw [htok]
    rcases hb with hb | hb <;> rw [hb]
    · exact h₁
    · exact h₂

/-- The gas `withdraw` gives its call. -/
def withdrawGas (wad : UInt256) : UInt256 :=
  if wad = ⟨0⟩ then UInt256.ofNat 2300 else UInt256.ofNat 0

/-- The account map after `withdraw wad` debits the caller. -/
def withdrawDebit (I : Env) (σ : AccountMap) (wad : UInt256) : AccountMap :=
  storeWord I.codeOwner σ (balanceSlot (UInt256.ofNat I.source.val))
    (slotWord I σ (balanceSlot (UInt256.ofNat I.source.val)) - wad)

/-- The message call `withdraw wad` makes from the world `w`, with the feed's entry `s`: to the
    caller, with `wad` and no data, on the debited account map. -/
def withdrawCall (I : Env) (w : World) (wad : UInt256) (s : Supply) : ThetaCall :=
  messageCall I { w with accounts := withdrawDebit I w.accounts wad } s (withdrawGas wad)
    I.codeOwner (.ofUInt256 (UInt256.ofNat I.source.val))
    (.ofUInt256 (UInt256.ofNat I.source.val)) wad wad ⟨0⟩ ⟨0⟩ I.perm

/-- **What a `withdraw` that returns did**: the caller's balance slot held `wad`, the call was
    made from the debited world, with the feed's next entry, and succeeded, the accounts are
    what it returned, and it is the one call recorded. -/
theorem withdraw_run {wad : UInt256} (hrun : (withdraw wad).exec I w = some (.ok ((), w'))) :
    ¬ (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat < wad.toNat ∧
      I.depth < 1024 ∧
      ∃ s rest, w.feed = s :: rest ∧ w'.accounts = (withdrawCall I w wad s).run.1 ∧
        w'.calls = w.calls ++ [Made.theta (withdrawCall I w wad s)] := by
  by_cases hlt : (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat <
      wad.toNat
  · simp [withdraw, hlt] at hrun
  refine ⟨hlt, ?_⟩
  by_cases hp : I.perm = true
  swap
  · simp [withdraw, hlt, exec_sstore, hp] at hrun
  simp only [withdraw, M.exec_bind, exec_caller, exec_sload, ite_eq_right hlt, M.exec_pure,
    exec_sstore, hp, ite_true] at hrun
  generalize hw₁ : ({ w with accounts := (storeWord I.codeOwner w.accounts
    (balanceSlot (UInt256.ofNat I.source.val))
    (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val)) - wad)) } : World) = w₁
    at hrun
  cases hc : (call (withdrawGas wad) (UInt256.ofNat I.source.val) wad ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩).exec I w₁
    with
  | none => simp [withdrawGas] at hc; simp [hc] at hrun
  | some res =>
    rcases res with f | ⟨x, w₂⟩
    · simp [withdrawGas] at hc; simp [hc] at hrun
    have hc' := hc
    simp only [withdrawGas] at hc'
    have hx : x ≠ ⟨0⟩ := fun hx => by simp [hc', hx] at hrun
    have hw' : w' = { w₂ with logs := w₂.logs.push ⟨I.codeOwner,
        #[withdrawalTopic, UInt256.ofNat I.source.val], wad.toByteArray⟩ } := by
      simp [hc', hx, exec_emit, hp] at hrun
      exact hrun.symm
    subst hw₁ hw'
    rcases call_cases hc with ⟨hx0, -, -⟩ | ⟨s, rest, hf, hm, ha, hcs⟩
    · exact absurd hx0 hx
    · exact ⟨hm.2, s, rest, hf, ha, hcs⟩

/-- **`withdraw`**: up to the call `withdraw_debit`; the call is whatever `Θ` returns, here
    assumed to keep solvency for each call recorded; after it nothing changes the accounts. -/
theorem withdraw_solvent {wad : UInt256}
    (hrun : (withdraw wad).exec I w = some (.ok ((), w')))
    (hcall : ∀ T, Made.theta T ∈ w'.calls → SolventAt I.codeOwner T.run.1) :
    SolventAt I.codeOwner w'.accounts := by
  obtain ⟨-, -, s, rest, -, ha, hcs⟩ := withdraw_run hrun
  rw [ha]
  exact hcall _ (by rw [hcs]; simp)

/-! ### The call `withdraw` makes, as `GoodTheta` asks of it -/

section WithdrawCall

variable {wad : UInt256} {s : Supply}

@[simp] theorem withdrawCall_σ : (withdrawCall I w wad s).σ = withdrawDebit I w.accounts wad := rfl
@[simp] theorem withdrawCall_s : (withdrawCall I w wad s).s = I.codeOwner := rfl
@[simp] theorem withdrawCall_v : (withdrawCall I w wad s).v = wad := rfl
@[simp] theorem withdrawCall_v' : (withdrawCall I w wad s).v' = wad := rfl

/-- The call goes to the caller. -/
@[simp] theorem withdrawCall_r : (withdrawCall I w wad s).r = I.source :=
  accountAddress_roundtrip _

/-- It has no data. -/
@[simp] theorem withdrawCall_d : (withdrawCall I w wad s).d = ByteArray.empty :=
  byteArray_readWithPadding_zero _ _

/-- A call entered from another account does not call back into itself. -/
theorem withdrawCall_r_ne (hne : I.source ≠ I.codeOwner) :
    (withdrawCall I w wad s).r ≠ I.codeOwner := by
  rw [withdrawCall_r]; exact hne

/-- The balances add up as they did before the debit. -/
theorem withdrawCall_total : total (withdrawCall I w wad s).σ = total w.accounts :=
  total_storeWord _ _ _ _

/-- The contract has `wad` after the debit: its ether covers the tokens it debited. -/
theorem withdrawCall_value {acc : Account} (hacc : w.accounts[I.codeOwner]? = some acc)
    (h : Solvent acc)
    (hv : ¬ (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat < wad.toNat) :
    (withdrawCall I w wad s).v ≤ balOf (withdrawCall I w wad s).σ (withdrawCall I w wad s).s := by
  rw [slotWord_of hacc] at hv
  obtain ⟨-, hb, -⟩ := solvent_debit h (UInt256.ofNat I.source.val) wad (Nat.le_of_not_lt hv)
  simp only [withdrawCall_v, withdrawCall_σ, withdrawCall_s, withdrawDebit]
  rw [balOf_of_some (by rw [getElem?_storeWord, hacc]; rfl), slotWord_some hacc]
  exact hb

/-- The account, with its code, before and after the call's value moves. -/
theorem withdrawCall_holds {code : ByteArray}
    (hH : Holds I.codeOwner (Weth code) w.accounts)
    (hv : ¬ (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat < wad.toNat) :
    let T := withdrawCall I w wad s
    Holds I.codeOwner (Weth code) T.σ ∧
      Holds I.codeOwner (Weth code)
        (sendEth T.r T.s T.v true T.σ) := by
  intro T
  obtain ⟨acc, hacc, hcode, h⟩ := hH
  obtain ⟨h₁, h₂, -⟩ := withdraw_debit hacc h hv I.source
  have hσ₁ : T.σ[I.codeOwner]? = some (storeAcc acc (balanceSlot (UInt256.ofNat I.source.val))
      (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val)) - wad)) := by
    show (storeWord _ _ _ _)[I.codeOwner]? = _
    rw [getElem?_storeWord, hacc]; rfl
  refine ⟨⟨_, hσ₁, by rw [storeAcc_code]; exact hcode, h₁ _ hσ₁⟩, ?_⟩
  obtain ⟨acc', h', -, hc', -⟩ := sendEth_payer (r := T.r) (v := T.v) hσ₁
  refine ⟨acc', h', by rw [hc', storeAcc_code]; exact hcode, h₂ acc' ?_⟩
  simpa [T] using! h'

end WithdrawCall

/-! ### The entry arms -/

theorem exec_bind_ok {α β : Type} {m : FeM α} {k : α → FeM β} {b : β}
    (h : (m >>= k).exec I w = some (.ok (b, w'))) :
    ∃ a w₁, m.exec I w = some (.ok (a, w₁)) ∧ (k a).exec I w₁ = some (.ok (b, w')) := by
  rw [M.exec_bind] at h
  rcases hm : m.exec I w with _ | f | ⟨a, w₁⟩ <;> rw [hm] at h
  · cases h
  · cases h
  · exact ⟨a, w₁, rfl, h⟩

theorem exec_nonPayable_ok {u : Unit} (h : nonPayable.exec I w = some (.ok (u, w'))) :
    I.weiValue = ⟨0⟩ ∧ w' = w := by
  rw [exec_nonPayable] at h
  by_cases hv : I.weiValue = ⟨0⟩ <;> simp [hv] at h
  exact ⟨hv, h.symm⟩

theorem nonPayable_bind_ok {β : Type} {k : Unit → FeM β} {b : β}
    (h : (nonPayable >>= k).exec I w = some (.ok (b, w'))) :
    I.weiValue = ⟨0⟩ ∧ (k ()).exec I w = some (.ok (b, w')) := by
  obtain ⟨_, w₁, h₁, k₁⟩ := exec_bind_ok h
  obtain ⟨hv, rfl⟩ := exec_nonPayable_ok h₁
  exact ⟨hv, k₁⟩

theorem guard_bind_ok {β γ : Type} {c : Prop} {inst : Decidable c} {e : ByteArray}
    {k₁ : γ → FeM β} {k₂ : PUnit → FeM β} {b : β}
    (h : (@ite _ c inst ((M.revert e : FeM γ) >>= k₁)
      ((pure PUnit.unit : FeM PUnit) >>= k₂)).exec I w = some (.ok (b, w'))) :
    ¬ c ∧ (k₂ PUnit.unit).exec I w = some (.ok (b, w')) := by
  by_cases hc : c <;> simp [hc] at h
  exact ⟨hc, h⟩

theorem pure_bind_ok {α β : Type} {m : FeM α} {f : α → β} {b : β}
    (h : (m >>= fun r => pure (f r)).exec I w = some (.ok (b, w'))) :
    ∃ r, m.exec I w = some (.ok (r, w')) := by
  obtain ⟨r, w₁, h₁, k₁⟩ := exec_bind_ok h
  simp at k₁
  exact ⟨r, k₁.2 ▸ h₁⟩

/-- The admission condition: the allowance slot `approve` or `transferFrom` writes is no key's
    balance slot. -/
structure Admits (I : Env) : Prop where
  approve : (approveSelector == I.calldata.extract 0 4) = true →
    ∀ k, allowanceSlot (UInt256.ofNat I.source.val) (word I.calldata 4) ≠ balanceSlot k
  transferFrom : (transferFromSelector == I.calldata.extract 0 4) = true →
    word I.calldata 4 ≠ UInt256.ofNat I.source.val →
    ∀ k, allowanceSlot (word I.calldata 4) (UInt256.ofNat I.source.val) ≠ balanceSlot k

/-- No value arrived: the account is the one solvent before. -/
theorem solvent_of_noValue {acc₀ acc : Account} (h₀ : Solvent acc₀)
    (hst : acc.storage = acc₀.storage)
    (hbal : acc.balance.toNat = acc₀.balance.toNat + I.weiValue.toNat) (hv : I.weiValue = ⟨0⟩) :
    Solvent acc := by
  rw [solvent_iff] at h₀ ⊢
  refine h₀.mono (fun k => by unfold tokens; rw [hst]) ?_
  rw [hbal, hv]; rfl

/-- **Every arm keeps solvency.**  A run of the runtime entry that returns, admitted, from an
    account that was solvent as `acc₀` before the call's value arrived and has gained the value
    since, ends solvent, if the call `withdraw` makes keeps solvency. -/
theorem runtime_solvent {acc₀ acc : Account} {out : ByteArray}
    (hrun : runtime.exec I w = some (.ok (out, w'))) (hadm : Admits I)
    (hacc : w.accounts[I.codeOwner]? = some acc) (h₀ : Solvent acc₀)
    (hst : acc.storage = acc₀.storage)
    (hbal : acc.balance.toNat = acc₀.balance.toNat + I.weiValue.toNat)
    (hcall : ∀ T, Made.theta T ∈ w'.calls → SolventAt I.codeOwner T.run.1) :
    SolventAt I.codeOwner w'.accounts := by
  have hs : I.weiValue = ⟨0⟩ → SolventAt I.codeOwner w.accounts := fun hv acc' h' => by
    rw [hacc] at h'; cases h'; exact solvent_of_noValue h₀ hst hbal hv
  unfold runtime at hrun
  obtain ⟨cd, w₀, hcd, hrun⟩ := exec_bind_ok hrun
  simp only [exec_calldata, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  by_cases h1 : I.calldata.size < 4
  · rw [ite_eq_left h1] at hrun
    exact depositArm_solvent hrun h₀ hacc hst hbal
  rw [ite_eq_right h1] at hrun
  by_cases h2 : (nameSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h2] at hrun
    -- name
    unfold nameArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    rw [stringReturn_world hrun]; exact hs hv
  rw [ite_eq_right h2] at hrun
  by_cases h3 : (approveSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h3] at hrun
    -- approve
    unfold approveArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    exact approve_solvent hr (hadm.approve h3) (hs hv)
  rw [ite_eq_right h3] at hrun
  by_cases h4 : (totalSupplySelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h4] at hrun
    -- totalSupply
    unfold totalSupplyArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [totalSupply_world hr]; exact hs hv
  rw [ite_eq_right h4] at hrun
  by_cases h5 : (transferFromSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h5] at hrun
    -- transferFrom
    unfold transferFromArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    exact transferFrom_solvent hr (hadm.transferFrom h5) (hs hv)
  rw [ite_eq_right h5] at hrun
  by_cases h6 : (withdrawSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h6] at hrun
    -- withdraw
    unfold withdrawArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨⟨⟩, hr⟩ := pure_bind_ok (f := fun _ => ByteArray.empty) hrun
    exact withdraw_solvent hr hcall
  rw [ite_eq_right h6] at hrun
  by_cases h7 : (decimalsSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h7] at hrun
    -- decimals
    unfold decimalsArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [decimals_world hr]; exact hs hv
  rw [ite_eq_right h7] at hrun
  by_cases h8 : (balanceOfSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h8] at hrun
    -- balanceOf
    unfold balanceOfArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [balanceOf_world hr]; exact hs hv
  rw [ite_eq_right h8] at hrun
  by_cases h9 : (symbolSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h9] at hrun
    -- symbol
    unfold symbolArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    rw [stringReturn_world hrun]; exact hs hv
  rw [ite_eq_right h9] at hrun
  by_cases h10 : (transferSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h10] at hrun
    -- transfer
    unfold transferArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨src, w₁, hc, hrun⟩ := exec_bind_ok hrun
    simp only [exec_caller, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    exact transferFrom_solvent hr (fun hne => absurd rfl hne) (hs hv)
  rw [ite_eq_right h10] at hrun
  by_cases h11 : (depositSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h11] at hrun
    exact depositArm_solvent hrun h₀ hacc hst hbal
  rw [ite_eq_right h11] at hrun
  by_cases h12 : (allowanceSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h12] at hrun
    -- allowance
    unfold allowanceArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [allowance_world hr]; exact hs hv
  rw [ite_eq_right h12] at hrun
  exact depositArm_solvent hrun h₀ hacc hst hbal

end Arms

/-! ## The run never stops from inside -/

theorem noStop_stringReturn (slot : UInt256) : (stringReturn slot).NoStop := by
  unfold stringReturn
  refine M.NoStop.bind M.NoStop.read fun I => M.NoStop.bind M.NoStop.get fun w => ?_
  dsimp only
  split
  · exact M.NoStop.ite _ (M.NoStop.pure _) (M.NoStop.panic _)
  · exact M.NoStop.revert _

theorem noStop_transferFrom (src dst wad : UInt256) : (transferFrom src dst wad).NoStop := by
  unfold transferFrom; dsimp only; no_stop

theorem noStop_ite {α : Type} {c : Prop} {inst : Decidable c} {a b : FeM α} (ha : a.NoStop)
    (hb : b.NoStop) : (@ite _ c inst a b).NoStop := by
  split <;> assumption

open Fe.M in
/-- `no_stop`, with the model's call, the context reads and the matches of the string getters. -/
macro "weth_no_stop" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact noStop_sload _
    | with_reducible exact noStop_sstore _ _
    | with_reducible exact noStop_emit _ _
    | with_reducible exact noStop_caller
    | with_reducible exact noStop_calldata
    | with_reducible exact noStop_nonPayable
    | with_reducible exact noStop_call _ _ _ _ _ _ _
    | with_reducible exact noStop_transferFrom _ _ _
    | with_reducible exact noStop_stringReturn _
    | with_reducible exact NoStop.pure _
    | with_reducible exact NoStop.revert _
    | with_reducible exact NoStop.panic _
    | with_reducible exact NoStop.fail_static
    | with_reducible exact NoStop.read
    | with_reducible exact NoStop.get
    | with_reducible exact NoStop.modify _
    | assumption
    | with_reducible apply noStop_ite
    | with_reducible apply NoStop.bind
    | intro (_ : _))

theorem noStop_approveArm (cd : ByteArray) : (approveArm cd).NoStop := by
  unfold approveArm approve; try dsimp only
  weth_no_stop

theorem noStop_transferFromArm (cd : ByteArray) : (transferFromArm cd).NoStop := by
  unfold transferFromArm; try dsimp only
  weth_no_stop

theorem noStop_transferArm (cd : ByteArray) : (transferArm cd).NoStop := by
  unfold transferArm; try dsimp only
  weth_no_stop

theorem noStop_withdrawArm (cd : ByteArray) : (withdrawArm cd).NoStop := by
  unfold withdrawArm withdraw; try dsimp only
  weth_no_stop

theorem noStop_depositArm : depositArm.NoStop := by
  unfold depositArm deposit callvalue; try dsimp only
  weth_no_stop

theorem noStop_getters (cd : ByteArray) :
    nameArm.NoStop ∧ totalSupplyArm.NoStop ∧ decimalsArm.NoStop ∧ (balanceOfArm cd).NoStop ∧
      symbolArm.NoStop ∧ (allowanceArm cd).NoStop := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nameArm; weth_no_stop
  · unfold totalSupplyArm totalSupply selfbalance; weth_no_stop
  · unfold decimalsArm decimals; weth_no_stop
  · unfold balanceOfArm balanceOf; try dsimp only
    weth_no_stop
  · unfold symbolArm; weth_no_stop
  · unfold allowanceArm allowance; try dsimp only
    weth_no_stop

/-- **The runtime entry never stops the run from inside**: every run that succeeds returns. -/
theorem noStop_runtime : runtime.NoStop := by
  have h1 := noStop_approveArm
  have h2 := noStop_transferFromArm
  have h3 := noStop_transferArm
  have h4 := noStop_withdrawArm
  have h5 := noStop_depositArm
  have h6 := fun cd => (noStop_getters cd).1
  have h7 := fun cd => (noStop_getters cd).2.1
  have h8 := fun cd => (noStop_getters cd).2.2.1
  have h9 := fun cd => (noStop_getters cd).2.2.2.1
  have h10 := fun cd => (noStop_getters cd).2.2.2.2.1
  have h11 := fun cd => (noStop_getters cd).2.2.2.2.2
  unfold runtime
  refine M.NoStop.bind noStop_calldata fun cd => ?_
  repeat' first
    | with_reducible exact h1 _ | with_reducible exact h2 _ | with_reducible exact h3 _
    | with_reducible exact h4 _ | with_reducible exact h5 | with_reducible exact h6 cd
    | with_reducible exact h7 cd | with_reducible exact h8 cd | with_reducible exact h9 _
    | with_reducible exact h10 cd | with_reducible exact h11 _
    | with_reducible apply noStop_ite

theorem Succeeds.of_noStop {m : FeM ByteArray} (hm : m.NoStop) {I : Env} {w w' : World}
    {out : ByteArray} (h : Succeeds (m.exec I w) out w') : m.exec I w = some (.ok (out, w')) :=
  h.resolve_right (hm I w out w')

/-! ## The entry -/

/-- **How the frame was entered**, as `ModelKeeps` states it: from `σpre`, where the contract has
    an account, by moving `v` to `a` from another account that has it, with the balances adding
    up to less than `2 ^ 256`.  The account then has the same storage and code, and `v` more
    ether, without wrapping.  `Holds` of `σpre` says the account exists; without one, `sendEth`
    would create an account at `a` with `v` and no code. -/
theorem entry_account {a src : AccountAddress} {v : UInt256} {σpre σ : AccountMap}
    {acc₀ : Account} (hσ : σ = sendEth a src v true σpre) (hne : src ≠ a)
    (hv : v ≤ balOf σpre src) (hT : total σpre < UInt256.size) (h₀ : σpre[a]? = some acc₀) :
    ∃ acc, σ[a]? = some acc ∧ acc.storage = acc₀.storage ∧ acc.code = acc₀.code ∧
      acc.balance.toNat = acc₀.balance.toNat + v.toNat := by
  subst hσ
  exact sendEth_payee h₀ hne hv hT

/-! ## The calls a run records -/

theorem keepsCalls_stringReturn (slot : UInt256) : KeepsCalls (stringReturn slot) := by
  unfold stringReturn
  refine KeepsCalls.bind KeepsCalls.read fun I => KeepsCalls.bind KeepsCalls.get fun w => ?_
  dsimp only
  split
  · exact KeepsCalls.ite (KeepsCalls.pure _) (KeepsCalls.panic _)
  · exact KeepsCalls.revert _

theorem keepsCalls_transferFrom (src dst wad : UInt256) :
    KeepsCalls (transferFrom src dst wad) := by
  unfold transferFrom; dsimp only; keeps_calls

/-- `keeps_calls`, with the string getters, `transferFrom` and conditionals on any decidable
    proposition. -/
macro "weth_keeps_calls" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact keepsCalls_sload _
    | with_reducible exact keepsCalls_sstore _ _
    | with_reducible exact keepsCalls_emit _ _
    | with_reducible exact keepsCalls_caller
    | with_reducible exact keepsCalls_callvalue
    | with_reducible exact keepsCalls_calldata
    | with_reducible exact keepsCalls_selfbalance
    | with_reducible exact keepsCalls_nonPayable
    | with_reducible exact keepsCalls_stringReturn _
    | with_reducible exact keepsCalls_transferFrom _ _ _
    | with_reducible exact KeepsCalls.pure _
    | with_reducible exact KeepsCalls.revert _
    | with_reducible exact KeepsCalls.panic _
    | with_reducible exact KeepsCalls.fail_static
    | with_reducible apply KeepsCalls.ite
    | with_reducible apply KeepsCalls.bind
    | intro (_ : _))

/-- Every arm but `withdraw` records no call. -/
theorem keepsCalls_arms (cd : ByteArray) :
    KeepsCalls nameArm ∧ KeepsCalls (approveArm cd) ∧ KeepsCalls totalSupplyArm ∧
      KeepsCalls (transferFromArm cd) ∧ KeepsCalls decimalsArm ∧ KeepsCalls (balanceOfArm cd) ∧
      KeepsCalls symbolArm ∧ KeepsCalls (transferArm cd) ∧ KeepsCalls depositArm ∧
      KeepsCalls (allowanceArm cd) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nameArm; weth_keeps_calls
  · unfold approveArm approve; dsimp only; weth_keeps_calls
  · unfold totalSupplyArm totalSupply; weth_keeps_calls
  · unfold transferFromArm; dsimp only; weth_keeps_calls
  · unfold decimalsArm decimals; weth_keeps_calls
  · unfold balanceOfArm balanceOf; dsimp only; weth_keeps_calls
  · unfold symbolArm; weth_keeps_calls
  · unfold transferArm; dsimp only; weth_keeps_calls
  · unfold depositArm deposit; weth_keeps_calls
  · unfold allowanceArm allowance; dsimp only; weth_keeps_calls

/-- **The calls a run of the runtime entry records**: none, or exactly the call `withdraw`
    makes, after the checks it passed. -/
theorem runtime_calls {I : Env} {w w' : World} {out : ByteArray}
    (hrun : runtime.exec I w = some (.ok (out, w'))) :
    w'.calls = w.calls ∨
      ((withdrawSelector == I.calldata.extract 0 4) = true ∧ I.weiValue = ⟨0⟩ ∧
        ¬ (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat <
          (word I.calldata 4).toNat ∧ I.depth < 1024 ∧
        ∃ s rest, w.feed = s :: rest ∧
          w'.accounts = (withdrawCall I w (word I.calldata 4) s).run.1 ∧
          w'.calls = w.calls ++ [Made.theta (withdrawCall I w (word I.calldata 4) s)]) := by
  have hk := keepsCalls_arms I.calldata
  unfold runtime at hrun
  obtain ⟨cd, w₀, hcd, hrun⟩ := exec_bind_ok hrun
  simp only [exec_calldata, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  by_cases h1 : I.calldata.size < 4
  · rw [ite_eq_left h1] at hrun; exact Or.inl ((hk.2.2.2.2.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h1] at hrun
  by_cases h2 : (nameSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h2] at hrun; exact Or.inl ((hk.1 I w).1 _ _ hrun)
  rw [ite_eq_right h2] at hrun
  by_cases h3 : (approveSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h3] at hrun; exact Or.inl ((hk.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h3] at hrun
  by_cases h4 : (totalSupplySelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h4] at hrun; exact Or.inl ((hk.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h4] at hrun
  by_cases h5 : (transferFromSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h5] at hrun; exact Or.inl ((hk.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h5] at hrun
  by_cases h6 : (withdrawSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h6] at hrun
    unfold withdrawArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨⟨⟩, hr⟩ := pure_bind_ok (f := fun _ => ByteArray.empty) hrun
    exact Or.inr ⟨h6, hv, withdraw_run hr⟩
  rw [ite_eq_right h6] at hrun
  by_cases h7 : (decimalsSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h7] at hrun; exact Or.inl ((hk.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h7] at hrun
  by_cases h8 : (balanceOfSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h8] at hrun; exact Or.inl ((hk.2.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h8] at hrun
  by_cases h9 : (symbolSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h9] at hrun; exact Or.inl ((hk.2.2.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h9] at hrun
  by_cases h10 : (transferSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h10] at hrun; exact Or.inl ((hk.2.2.2.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h10] at hrun
  by_cases h11 : (depositSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h11] at hrun; exact Or.inl ((hk.2.2.2.2.2.2.2.2.1 I w).1 _ _ hrun)
  rw [ite_eq_right h11] at hrun
  by_cases h12 : (allowanceSelector == I.calldata.extract 0 4) = true
  · rw [ite_eq_left h12] at hrun; exact Or.inl ((hk.2.2.2.2.2.2.2.2.2 I w).1 _ _ hrun)
  rw [ite_eq_right h12] at hrun
  exact Or.inl ((hk.2.2.2.2.2.2.2.2.1 I w).1 _ _ hrun)

/-- **What the record says, from a world that has recorded nothing**: every call recorded is the
    one `withdraw` makes, with the feed's first entry, and the run ends with the accounts it
    returned.  A condition every recorded call satisfies (`∀ c ∈ w'.calls, Made.Ok Q c`) holds of
    `T` as `Q.theta T`, by `Made.Ok` at `Made.theta T`. -/
theorem runtime_recorded {I : Env} {w w' : World} {out : ByteArray}
    (hrun : runtime.exec I w = some (.ok (out, w'))) (hw : w.calls = []) {T : ThetaCall}
    (hT : Made.theta T ∈ w'.calls) :
    (withdrawSelector == I.calldata.extract 0 4) = true ∧ I.weiValue = ⟨0⟩ ∧
      ¬ (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat <
        (word I.calldata 4).toNat ∧ I.depth < 1024 ∧
      ∃ s rest, w.feed = s :: rest ∧ T = withdrawCall I w (word I.calldata 4) s ∧
        w'.accounts = T.run.1 := by
  rcases runtime_calls hrun with h | ⟨h1, h2, h3, h4, s, rest, hf, ha, hcs⟩
  · rw [h, hw] at hT; cases hT
  · rw [hcs, hw] at hT
    obtain rfl := Made.theta.inj (List.mem_singleton.mp hT)
    exact ⟨h1, h2, h3, h4, s, rest, hf, rfl, ha⟩

/-! ## The run, in the terms of `ModelKeeps` -/

/-- **A run of the runtime entry keeps the contract's account**, in the terms `ModelKeeps` gives:
    entered from `σpre`, where `Weth code` holds, by moving `I.weiValue` from another account that
    has it, with the balances adding up to less than `2 ^ 256`, admitted, a run that succeeds
    ends with the account running `code` and solvent, if its code is still what it was and the
    call it records keeps it solvent. -/
theorem runtime_keeps {code : ByteArray} {I : Env} {σpre σ : AccountMap} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w' : World}
    (hσ : σ = sendEth I.codeOwner I.source I.weiValue true σpre)
    (hne : I.source ≠ I.codeOwner) (hv : I.weiValue ≤ balOf σpre I.source)
    (hT : total σpre < UInt256.size) (hpre : Holds I.codeOwner (Weth code) σpre)
    (hadm : Admits I) (hrun : Succeeds (runtime.exec I (World.init σ A feed)) out w')
    (hcall : ∀ T, Made.theta T ∈ w'.calls → SolventAt I.codeOwner T.run.1) :
    ∀ acc acc', σ[I.codeOwner]? = some acc → w'.accounts[I.codeOwner]? = some acc' →
      acc'.code = acc.code → Weth code acc' := by
  intro acc acc' hacc hacc' hcode
  obtain ⟨acc₀, h₀, hc₀, hs₀⟩ := hpre
  obtain ⟨acc₁, h₁, hst, hc₁, hbal⟩ := entry_account hσ hne hv hT h₀
  rw [hacc] at h₁; cases h₁
  refine ⟨hcode.trans (hc₁.trans hc₀), ?_⟩
  exact runtime_solvent (Succeeds.of_noStop noStop_runtime hrun) hadm hacc hs₀ hst hbal hcall
    acc' hacc'

/-- **The recorded call, as `GoodTheta` asks of it**: entered as in `runtime_keeps`, the call a
    run of the runtime entry records is one level deeper, has no data, goes to another account
    than `a` (so it runs no code `Trusted` must admit, and needs no `Enters`), moves `wad`, which
    the contract has, from a map whose balances add up as they did on entry, where the account
    runs `code` and is solvent before and after the value moves; and the run ends with the
    accounts the call returned. -/
theorem recorded_call {code : ByteArray} {I : Env} {σpre σ : AccountMap} {A : Substate}
    {feed : List Supply} {out : ByteArray} {w' : World}
    (hσ : σ = sendEth I.codeOwner I.source I.weiValue true σpre)
    (hne : I.source ≠ I.codeOwner) (hv : I.weiValue ≤ balOf σpre I.source)
    (hT : total σpre < UInt256.size) (hpre : Holds I.codeOwner (Weth code) σpre)
    (hrun : runtime.exec I (World.init σ A feed) = some (.ok (out, w'))) {T : ThetaCall}
    (hrec : Made.theta T ∈ w'.calls) :
    T.e.val = I.depth.val + 1 ∧ T.d.size < UInt256.size ∧ T.r ≠ I.codeOwner ∧ T.v = T.v' ∧
      T.v ≤ balOf T.σ T.s ∧ total T.σ < UInt256.size ∧ Holds I.codeOwner (Weth code) T.σ ∧
      Holds I.codeOwner (Weth code) (sendEth T.r T.s T.v true T.σ) ∧ w'.accounts = T.run.1 := by
  obtain ⟨-, hw0, hbal, hd, s, rest, -, rfl, ha⟩ := runtime_recorded hrun rfl hrec
  obtain ⟨acc₀, h₀, hc₀, hs₀⟩ := hpre
  obtain ⟨acc, hacc, hst, hc, hb⟩ := entry_account hσ hne hv hT h₀
  have hs : Solvent acc := solvent_of_noValue hs₀ hst hb hw0
  have hH : Holds I.codeOwner (Weth code) (World.init σ A feed).accounts :=
    ⟨acc, hacc, hc.trans hc₀, hs⟩
  obtain ⟨hH₁, hH₂⟩ := withdrawCall_holds (s := s) hH hbal
  refine ⟨succ_depth_val hd, by simp [UInt256.size], withdrawCall_r_ne hne, rfl,
    withdrawCall_value hacc hs hbal, ?_, hH₁, hH₂, ha⟩
  rw [withdrawCall_total]
  show total σ < UInt256.size
  rw [hσ, total_sendEth hv hT]
  exact hT

/-! ## The constructor -/

section Init

variable {I : Env} {w w' : World}

theorem SolventAt'.clear {a : AccountAddress} {σ : AccountMap} (h : SolventAt' a σ)
    (base idx : UInt256) (n : ℕ) : SolventAt' a (clearDataWordsForwardFrom a σ base idx n) := by
  induction n generalizing σ idx with
  | zero => exact h
  | succ n ih => exact ih (h.storeWord (Or.inr rfl)) _

theorem storeString_ok {slot : UInt256} {bytes : ByteArray} {u : Unit}
    (hrun : (storeString slot bytes).exec I w = some (.ok (u, w'))) :
    w'.accounts = strWriteMap I w.accounts slot bytes := by
  unfold storeString at hrun
  by_cases hb : strHeadBad (slotWord I w.accounts slot)
  · simp [hb] at hrun
  by_cases hp : I.perm = true
  · simp [hb, hp] at hrun; rw [← hrun]
  · simp [hb, hp] at hrun

theorem SolventAt'.strWrite {σ : AccountMap} (h : SolventAt' I.codeOwner σ) {slot : UInt256}
    (hslot : ∀ k, slot ≠ balanceSlot k) (bytes : ByteArray) :
    SolventAt' I.codeOwner (strWriteMap I σ slot bytes) :=
  (h.storeWord (Or.inl hslot)).clear _ _ _

/-- **The constructor keeps solvency**, if no key's balance slot is one of the slots of `name`,
    `symbol` and `decimals`.  It writes the zeros that clear a string's old data words anywhere,
    which only lowers balances. -/
theorem init_solvent (hrun : init.exec I w = some (.ok ((), w')))
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (h : SolventAt' I.codeOwner w.accounts) : SolventAt' I.codeOwner w'.accounts := by
  unfold init at hrun
  obtain ⟨_, w₁, h₁, r₁⟩ := exec_bind_ok hrun
  obtain ⟨-, rfl⟩ := exec_nonPayable_ok h₁
  obtain ⟨_, w₂, h₂, r₂⟩ := exec_bind_ok r₁
  obtain ⟨_, w₃, h₃, r₃⟩ := exec_bind_ok r₂
  obtain ⟨_, w₄, h₄, r₄⟩ := exec_bind_ok r₃
  simp only [exec_sload, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h₄
  obtain ⟨-, rfl⟩ := h₄
  have hw₂ := (h.strWrite (fun k => (hslots k).1) nameBytes)
  rw [← storeString_ok h₂] at hw₂
  have hw₃ := (hw₂.strWrite (fun k => (hslots k).2.1) symbolBytes)
  rw [← storeString_ok h₃] at hw₃
  by_cases hp : I.perm = true
  · rw [exec_sstore, ite_eq_left hp] at r₄
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at r₄
    rw [← r₄.2]
    exact hw₃.storeWord (Or.inl fun k => (hslots k).2.2)
  · rw [exec_sstore, ite_eq_right hp] at r₄; cases r₄

/-- From the empty storage a creation starts with, the constructor leaves a solvent account. -/
theorem init_solvent_of_empty (hrun : init.exec I w = some (.ok ((), w')))
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hempty : (w.accounts.getD I.codeOwner default).storage = default) :
    Solvent (w'.accounts.getD I.codeOwner default) :=
  init_solvent hrun hslots (solvent_of_empty hempty)

end Init

end FeProofs.WETH9
