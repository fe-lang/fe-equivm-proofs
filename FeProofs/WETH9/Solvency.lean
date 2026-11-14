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
  whatever `Θ` returns (`call_keeps`, with the callee keeping solvency as a hypothesis); after it
  nothing changes the accounts (`withdraw_solvent`).

`runtime_solvent` puts the arms together: a run of the runtime entry that returns, admitted
(`Admits`), from an account that was solvent before the call's value arrived and has gained the
value since, ends solvent, if `withdraw`'s call keeps solvency (`CalleeKeeps`).

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
    have hv : val = ⟨0⟩ := by simpa using hv
    rw [Std.ExtTreeMap.getD_erase]
    by_cases ht : t = slot
    · rw [if_pos (hc.mpr ht), if_pos ht, hv]
    · rw [if_neg (mt hc.mp ht), if_neg ht]
  · rw [Std.ExtTreeMap.getD_insert]
    by_cases ht : t = slot
    · rw [if_pos (hc.mpr ht), if_pos ht]
    · rw [if_neg (mt hc.mp ht), if_neg ht]

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
  rw [tokens_storeAcc, if_neg (hslot k).symm]

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
        have := h₂ (balanceSlot dst); rw [if_pos hsd] at this; exact this
      have hlt : (acc.storage.getD (balanceSlot src) ⟨0⟩).toNat < UInt256.size :=
        (acc.storage.getD (balanceSlot src) ⟨0⟩).val.isLt
      unfold tokens at hv this
      rw [UInt256.toNat_add_of_lt (by omega), this]
      omega
    refine h.mono (fun k => ?_) (by simp [acc₂])
    rw [tokens_storeAcc, hback, h₂]
    by_cases hk : balanceSlot k = balanceSlot src
    · rw [if_pos (hk.trans hsd.symm), hk]; rfl
    · rw [if_neg (fun he => hk (he.trans hsd)), if_neg hk]
  · obtain ⟨hB, h₂s⟩ := h.debit src hv (g' := tokens acc₂)
      (by rw [h₂, if_pos rfl]; omega) (fun t ht _ => by rw [h₂, if_neg ht])
    have hy : (acc₂.storage.getD (balanceSlot dst) ⟨0⟩).toNat = tokens acc (balanceSlot dst) := by
      have := h₂ (balanceSlot dst); rw [if_neg hsd] at this; exact this
    have hpair := h.pair (Ne.symm hsd)
    have hbal : acc.balance.toNat < UInt256.size := acc.balance.val.isLt
    have hadd : (acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v).toNat =
        tokens acc₂ (balanceSlot dst) + v.toNat := by
      rw [UInt256.toNat_add_of_lt (by rw [hy]; omega)]; rfl
    have h₃ := h₂s.credit dst (g' := tokens (storeAcc acc₂ (balanceSlot dst)
        (acc₂.storage.getD (balanceSlot dst) ⟨0⟩ + v)))
      (by rw [tokens_storeAcc, if_pos rfl, hadd]) (fun t ht _ => by rw [tokens_storeAcc, if_neg ht])
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
    (by rw [tokens_storeAcc, if_pos rfl, hx]; omega)
    (fun t ht _ => by rw [tokens_storeAcc, if_neg ht])
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
    (by rw [tokens_storeAcc, if_pos rfl, hadd])
    (fun t ht _ => by rw [tokens_storeAcc, if_neg ht, htok])
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
    exact u256_inj (by rw [slotWord_of h', slotWord_of hacc, tokens_storeAcc, if_neg h])

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

/-- The payer's account after a value transfer: the same storage, and the same balance (paying
    itself) or the value less. -/
theorem sendEth_payer {σ : AccountMap} {r s : AccountAddress} {v : UInt256} {acc : Account}
    (h : σ[s]? = some acc) :
    ∃ acc', (sendEth r s v true σ)[s]? = some acc' ∧ acc'.storage = acc.storage ∧
      (acc'.balance = acc.balance ∨ acc'.balance = acc.balance - v) := by
  by_cases hrs : r = s
  · subst hrs
    refine ⟨{ acc with balance := acc.balance + v - v }, ?_, rfl,
      Or.inl (UInt256.add_sub_cancel' _ _)⟩
    simp [sendEth, Std.ExtTreeMap.get?_eq_getElem?, h]
  · refine ⟨{ acc with balance := acc.balance - v }, ?_, rfl, Or.inr rfl⟩
    have hne : ¬ compare r s = .eq := fun he => hrs (Std.LawfulEqCmp.eq_of_compare he)
    unfold sendEth
    rcases hr : σ[r]? with _ | accr
    · by_cases hv : (v != UInt256.ofNat 0) = true
      · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, h, hr, hv]
      · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hv
        simp [Std.ExtTreeMap.get?_eq_getElem?, h, hr, hv]
    · simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, h, hr]

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
  · obtain ⟨acc'', h'', hst, hb⟩ := sendEth_payer (r := r) (v := wad) hσ₁
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

/-- What `withdraw wad` needs of its call: started from the account map after the debit, the
    callee keeps the account at `I.codeOwner` solvent, if it is before and after the value moves
    and the balances add up as they did. -/
def CalleeKeeps (I : Env) (w : World) (wad : UInt256) : Prop :=
  ∀ s rest, w.feed = s :: rest →
    let src := UInt256.ofNat I.source.val
    let T := messageCall I { w with accounts := (storeWord I.codeOwner w.accounts
        (balanceSlot src) (slotWord I w.accounts (balanceSlot src) - wad)) } s
      (withdrawGas wad) I.codeOwner (.ofUInt256 src) (.ofUInt256 src) wad wad ⟨0⟩ ⟨0⟩ I.perm
    SolventAt I.codeOwner T.σ → SolventAt I.codeOwner (sendEth T.r T.s T.v true T.σ) →
      total T.σ = total w.accounts → SolventAt I.codeOwner T.run.1

/-- **`withdraw`**: up to the call `withdraw_debit`; the call is whatever `Θ` returns, here
    assumed to keep solvency, given it before and after its value moves, with the balances
    adding up as they did; after it nothing changes the accounts. -/
theorem withdraw_solvent {wad : UInt256} {acc : Account}
    (hrun : (withdraw wad).exec I w = some (.ok ((), w')))
    (hacc : w.accounts[I.codeOwner]? = some acc) (h : Solvent acc)
    (hcallee : CalleeKeeps I w wad) :
    SolventAt I.codeOwner w'.accounts := by
  by_cases hlt : (slotWord I w.accounts (balanceSlot (UInt256.ofNat I.source.val))).toNat <
      wad.toNat
  · simp [withdraw, hlt] at hrun
  by_cases hp : I.perm = true
  swap
  · simp [withdraw, hlt, exec_sstore, hp] at hrun
  simp only [withdraw, M.exec_bind, exec_caller, exec_sload, if_neg hlt, M.exec_pure,
    exec_sstore, hp, if_true] at hrun
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
    have hw' : w'.accounts = w₂.accounts := by
      simp only [withdrawGas] at hc
      by_cases hx : x = ⟨0⟩ <;> simp [hc, hx, exec_emit, hp] at hrun
      rw [← hrun]
    rw [hw']
    obtain ⟨h₁, h₂, ht⟩ := withdraw_debit hacc h hlt (.ofUInt256 (UInt256.ofNat I.source.val))
    subst hw₁
    refine call_keeps hc h₁ fun s rest hf _ => hcallee s rest hf h₁ h₂ ht
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
    (hcallee : CalleeKeeps I w (word I.calldata 4)) :
    SolventAt I.codeOwner w'.accounts := by
  have hs : I.weiValue = ⟨0⟩ → SolventAt I.codeOwner w.accounts := fun hv acc' h' => by
    rw [hacc] at h'; cases h'; exact solvent_of_noValue h₀ hst hbal hv
  unfold runtime at hrun
  obtain ⟨cd, w₀, hcd, hrun⟩ := exec_bind_ok hrun
  simp only [exec_calldata, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  by_cases h1 : I.calldata.size < 4
  · rw [if_pos h1] at hrun
    exact depositArm_solvent hrun h₀ hacc hst hbal
  rw [if_neg h1] at hrun
  by_cases h2 : (nameSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h2] at hrun
    -- name
    unfold nameArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    rw [stringReturn_world hrun]; exact hs hv
  rw [if_neg h2] at hrun
  by_cases h3 : (approveSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h3] at hrun
    -- approve
    unfold approveArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    exact approve_solvent hr (hadm.approve h3) (hs hv)
  rw [if_neg h3] at hrun
  by_cases h4 : (totalSupplySelector == I.calldata.extract 0 4) = true
  · rw [if_pos h4] at hrun
    -- totalSupply
    unfold totalSupplyArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [totalSupply_world hr]; exact hs hv
  rw [if_neg h4] at hrun
  by_cases h5 : (transferFromSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h5] at hrun
    -- transferFrom
    unfold transferFromArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    exact transferFrom_solvent hr (hadm.transferFrom h5) (hs hv)
  rw [if_neg h5] at hrun
  by_cases h6 : (withdrawSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h6] at hrun
    -- withdraw
    unfold withdrawArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨⟨⟩, hr⟩ := pure_bind_ok (f := fun _ => ByteArray.empty) hrun
    exact withdraw_solvent hr hacc (solvent_of_noValue h₀ hst hbal hv) hcallee
  rw [if_neg h6] at hrun
  by_cases h7 : (decimalsSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h7] at hrun
    -- decimals
    unfold decimalsArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [decimals_world hr]; exact hs hv
  rw [if_neg h7] at hrun
  by_cases h8 : (balanceOfSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h8] at hrun
    -- balanceOf
    unfold balanceOfArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [balanceOf_world hr]; exact hs hv
  rw [if_neg h8] at hrun
  by_cases h9 : (symbolSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h9] at hrun
    -- symbol
    unfold symbolArm at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    rw [stringReturn_world hrun]; exact hs hv
  rw [if_neg h9] at hrun
  by_cases h10 : (transferSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h10] at hrun
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
  rw [if_neg h10] at hrun
  by_cases h11 : (depositSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h11] at hrun
    exact depositArm_solvent hrun h₀ hacc hst hbal
  rw [if_neg h11] at hrun
  by_cases h12 : (allowanceSelector == I.calldata.extract 0 4) = true
  · rw [if_pos h12] at hrun
    -- allowance
    unfold allowanceArm at hrun
    dsimp only at hrun
    obtain ⟨hv, hrun⟩ := nonPayable_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨-, hrun⟩ := guard_bind_ok hrun
    obtain ⟨r, hr⟩ := pure_bind_ok hrun
    rw [allowance_world hr]; exact hs hv
  rw [if_neg h12] at hrun
  exact depositArm_solvent hrun h₀ hacc hst hbal

end Arms

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
  · rw [exec_sstore, if_pos hp] at r₄
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at r₄
    rw [← r₄.2]
    exact hw₃.storeWord (Or.inl fun k => (hslots k).2.2)
  · rw [exec_sstore, if_neg hp] at r₄; cases r₄

/-- From the empty storage a creation starts with, the constructor leaves a solvent account. -/
theorem init_solvent_of_empty (hrun : init.exec I w = some (.ok ((), w')))
    (hslots : ∀ k, nameSlot ≠ balanceSlot k ∧ symbolSlot ≠ balanceSlot k ∧
      decimalsSlot ≠ balanceSlot k)
    (hempty : (w.accounts.getD I.codeOwner default).storage = default) :
    Solvent (w'.accounts.getD I.codeOwner default) :=
  init_solvent hrun hslots (solvent_of_empty hempty)

end Init

end FeProofs.WETH9
