import FeProofs.ERC20.Model
import FeProofs.ERC20.Selectors
import Reasoning.PackedStorage
import Reasoning.EVMWord

/-!
# FeERC20: the model conserves the sum of balances

A property of the hand-written model alone: the constructor makes the balances of a finite list
of holders add up to the recorded supply, and every run of the runtime entry that ends
successfully keeps them so.  The holders' balance slots must not collide, with each other or with
the supply slot, a call that moves tokens must move them between holders in the list, and an
allowance slot a call writes must be neither a holder's balance slot nor the supply slot.  These
conditions are about the keys in use, never about all keys: hashed slots of all 2^160 addresses
almost surely do collide, and the 2^320 allowance slots surely do.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.ERC20

/-! ## The invariant -/

/-- The word at `slot` of the storage of the account at `c`, zero if there is none.  It is
    `slotWord` of a call that runs the code of `c`. -/
def storageAt (c : AccountAddress) (σ : AccountMap) (slot : UInt256) : UInt256 :=
  σ.get? c |>.option ⟨0⟩ (fun acc => acc.storage.getD slot ⟨0⟩)

/-- The balance of `a` in the token at `c`. -/
def balance (c : AccountAddress) (σ : AccountMap) (a : UInt256) : UInt256 :=
  storageAt c σ (Model.balanceSlot a)

/-- The sum of the balances of the holders `S`, as a natural number. -/
def balanceSum (c : AccountAddress) (σ : AccountMap) (S : List UInt256) : ℕ :=
  (S.map fun a => (balance c σ a).toNat).sum

/-- The total supply the token at `c` records. -/
def supply (c : AccountAddress) (σ : AccountMap) : UInt256 :=
  storageAt c σ Model.totalSupplySlot

/-- The balances of the holders `S` in the token at `c` add up to its recorded supply. -/
def Conserved (c : AccountAddress) (σ : AccountMap) (S : List UInt256) : Prop :=
  balanceSum c σ S = (supply c σ).toNat

/-- The balance slots of the holders `S` are pairwise distinct and none is the supply slot. -/
structure CollisionFree (S : List UInt256) : Prop where
  nodup : S.Nodup
  inj : ∀ a ∈ S, ∀ b ∈ S, Model.balanceSlot a = Model.balanceSlot b → a = b
  supply : ∀ a ∈ S, Model.balanceSlot a ≠ Model.totalSupplySlot

/-- The slot `s` is neither the balance slot of a holder in `S` nor the supply slot. -/
def Untracked (S : List UInt256) (s : UInt256) : Prop :=
  (∀ b ∈ S, Model.balanceSlot b ≠ s) ∧ s ≠ Model.totalSupplySlot

/-- What the call `I` needs of the holders `S`, by the entry point its selector picks.
    `transfer(to, value)` moves tokens from the caller to `to`, and `transferFrom(from, to,
    value)` from `from` to `to`: both ends must be holders.  `transferFrom` writes the allowance
    of the caller over `from`'s tokens, and `approve(spender, value)` the allowance of `spender`
    over the caller's: that slot must be untracked.  The getters need nothing. -/
structure Covers (S : List UInt256) (I : ExecutionEnv) : Prop where
  transfer : selIs I Model.transferSelector →
    UInt256.ofNat I.source.val ∈ S ∧ word I.calldata 4 ∈ S
  transferFrom : selIs I Model.transferFromSelector →
    word I.calldata 4 ∈ S ∧ word I.calldata 36 ∈ S
      ∧ Untracked S (Model.allowanceSlot (word I.calldata 4) (UInt256.ofNat I.source.val))
  approve : selIs I Model.approveSelector →
    Untracked S (Model.allowanceSlot (UInt256.ofNat I.source.val) (word I.calldata 4))

/-! ## Stores -/

section Stores

variable {c : AccountAddress}

theorem storageAt_store_ne (σ : AccountMap) (r s v : UInt256) (h : r ≠ s) :
    storageAt c (storeWord c σ s v) r = storageAt c σ r :=
  sstoreAccountMap_storage_getD_ne σ c r s v h

theorem storageAt_store_self (σ : AccountMap) {acc : Account} (ha : σ.get? c = some acc)
    (s v : UInt256) : storageAt c (storeWord c σ s v) s = v :=
  sstoreAccountMap_storage_getD_self_zero_present σ c s v ha

/-- Without an account at `c`, a store there changes nothing. -/
theorem storeWord_absent {σ : AccountMap} (ha : σ.get? c = none) (s v : UInt256) :
    storeWord c σ s v = σ := by
  unfold storeWord; rw [ha]; rfl

theorem storeWord_present {σ : AccountMap} {acc : Account} (ha : σ.get? c = some acc)
    (s v : UInt256) : ∃ acc', (storeWord c σ s v).get? c = some acc' :=
  sstoreAccountMap_get?_owner_some_of_some σ c s v ha

/-- A store to a slot that no holder in `S` uses leaves their sum unchanged. -/
theorem balanceSum_store_other (σ : AccountMap) (S : List UInt256) (s v : UInt256)
    (h : ∀ b ∈ S, Model.balanceSlot b ≠ s) :
    balanceSum c (storeWord c σ s v) S = balanceSum c σ S := by
  unfold balanceSum
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [balance]
  rw [storageAt_store_ne σ _ s v (h b hb)]

/-- A store to the balance of a holder in `S` changes the sum by the change of that balance. -/
theorem balanceSum_store (σ : AccountMap) {acc : Account} (ha : σ.get? c = some acc)
    (S : List UInt256) (hnd : S.Nodup)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, Model.balanceSlot a = Model.balanceSlot b → a = b)
    (a v : UInt256) (hmem : a ∈ S) :
    balanceSum c (storeWord c σ (Model.balanceSlot a) v) S + (balance c σ a).toNat
      = balanceSum c σ S + v.toNat := by
  induction S with
  | nil => cases hmem
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxs : xs.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hax : a = x
    · subst hax
      have hother : ∀ b ∈ xs, Model.balanceSlot b ≠ Model.balanceSlot a := fun b hb hEq =>
        hx (by rw [← hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hEq]; exact hb)
      have hrest := balanceSum_store_other (c := c) σ xs (Model.balanceSlot a) v hother
      simp only [balanceSum, List.map_cons, List.sum_cons, balance] at hrest ⊢
      rw [storageAt_store_self σ ha, hrest]
      omega
    · have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left hax
      have hne : Model.balanceSlot x ≠ Model.balanceSlot a := fun hEq =>
        hax (hinj a hmem x List.mem_cons_self hEq.symm)
      have ih' := ih hxs (fun p hp q hq => hinj p (List.mem_cons_of_mem _ hp) q
        (List.mem_cons_of_mem _ hq)) hmem'
      simp only [balanceSum, List.map_cons, List.sum_cons, balance] at ih' ⊢
      rw [storageAt_store_ne σ _ _ v hne]
      omega

/-- A store to an untracked slot keeps the invariant. -/
theorem Conserved.store_untracked {σ : AccountMap} {S : List UInt256} {s : UInt256}
    (hu : Untracked S s) (v : UInt256) (h : Conserved c σ S) :
    Conserved c (storeWord c σ s v) S := by
  unfold Conserved supply at *
  rw [balanceSum_store_other σ S s v hu.1, storageAt_store_ne σ _ s v hu.2.symm]
  exact h

/-- Moving `value` from the balance of `src` to that of `dst`, both holders, keeps the
    invariant, when the first balance covers it and the second does not overflow. -/
theorem Conserved.move {σ : AccountMap} {S : List UInt256} {src dst value : UInt256}
    (hS : CollisionFree S) (hsrc : src ∈ S) (hdst : dst ∈ S)
    (hle : value.toNat ≤ (balance c σ src).toNat)
    (hover : (balance c (storeWord c σ (Model.balanceSlot src)
      (UInt256.sub (balance c σ src) value)) dst).toNat + value.toNat < UInt256.size)
    (h : Conserved c σ S) :
    Conserved c (storeWord c (storeWord c σ (Model.balanceSlot src)
      (UInt256.sub (balance c σ src) value)) (Model.balanceSlot dst)
      (balance c (storeWord c σ (Model.balanceSlot src)
        (UInt256.sub (balance c σ src) value)) dst + value)) S := by
  cases ha : σ.get? c with
  | none => rwa [storeWord_absent ha, storeWord_absent ha]
  | some acc =>
  set bs := balance c σ src with hbs
  set σ1 := storeWord c σ (Model.balanceSlot src) (UInt256.sub bs value) with hσ1
  set bd := balance c σ1 dst with hbd
  obtain ⟨acc1, ha1⟩ := storeWord_present ha (Model.balanceSlot src) (UInt256.sub bs value)
  have h1 : balanceSum c σ1 S + bs.toNat = balanceSum c σ S + (UInt256.sub bs value).toNat :=
    balanceSum_store σ ha S hS.nodup hS.inj src (UInt256.sub bs value) hsrc
  have h2 : balanceSum c (storeWord c σ1 (Model.balanceSlot dst) (bd + value)) S + bd.toNat
      = balanceSum c σ1 S + (bd + value).toNat :=
    balanceSum_store σ1 ha1 S hS.nodup hS.inj dst (bd + value) hdst
  have hsub : (UInt256.sub bs value).toNat = bs.toNat - value.toNat := usub_toNat hle
  have hadd : (bd + value).toNat = bd.toNat + value.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hover]
  have hsup : supply c (storeWord c σ1 (Model.balanceSlot dst) (bd + value)) = supply c σ := by
    unfold supply
    rw [storageAt_store_ne _ _ _ _ (hS.supply dst hdst).symm,
      storageAt_store_ne _ _ _ _ (hS.supply src hsrc).symm]
  rw [hsub] at h1
  rw [hadd] at h2
  unfold Conserved at h ⊢
  rw [hsup, ← h]
  omega

end Stores

/-! ## Runs that keep a property of the accounts -/

/-- Every run of `m` under `I` that returns, from a world whose accounts satisfy `P`, ends in a
    world whose accounts satisfy `P`. -/
def Keeps (I : ExecutionEnv) (P : AccountMap → Prop) {α : Type} (m : FeM α) : Prop :=
  ∀ w a w', P w.accounts → m.exec I w = some (.ok (a, w')) → P w'.accounts

section Keeps

variable {I : ExecutionEnv} {P : AccountMap → Prop} {α β : Type}

theorem Keeps.pure (a : α) : Keeps I P (pure a : FeM α) := by
  intro w a' w' hP h; simp at h; rw [← h.2]; exact hP

theorem Keeps.revert (data : ByteArray) : Keeps I P (M.revert data : FeM α) := by
  intro w a w' _ h; simp at h

theorem Keeps.bind {m : FeM α} {k : α → FeM β} (hm : Keeps I P m)
    (hk : ∀ a, Keeps I P (k a)) :
    Keeps I P (m >>= k) := by
  intro w b w' hP h
  rw [M.exec_bind] at h
  cases hr : m.exec I w with
  | none => rw [hr] at h; cases h
  | some r =>
    cases r with
    | error f => rw [hr] at h; cases h
    | ok p => rw [hr] at h; exact hk p.1 p.2 b w' (hm w p.1 p.2 hP hr) h

theorem Keeps.ite {c : Prop} [Decidable c] {a b : FeM α} (ha : c → Keeps I P a)
    (hb : ¬ c → Keeps I P b) : Keeps I P (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- The calldata the entry reads is the call's. -/
theorem Keeps.calldata_bind {k : ByteArray → FeM α} (h : Keeps I P (k I.calldata)) :
    Keeps I P (calldata >>= k) := by
  intro w a w' hP hr
  simp only [M.exec_bind, exec_calldata] at hr
  exact h w a w' hP hr

theorem keeps_sload (slot : UInt256) : Keeps I P (sload slot) := by
  intro w a w' hP h; simp at h; rw [← h.2]; exact hP

theorem keeps_nonPayable : Keeps I P nonPayable := by
  intro w a w' hP h
  rw [exec_nonPayable] at h
  split at h <;> simp at h
  rw [← h]; exact hP

/-- Prove `Keeps` for a computation built from binds, conditionals, reads of storage and
    reverts.  Unfold the definitions it should look into first. -/
macro "keeps_accounts" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact keeps_sload _
    | with_reducible exact keeps_nonPayable
    | with_reducible exact Keeps.pure _
    | with_reducible exact Keeps.revert _
    | with_reducible assumption
    | with_reducible apply Keeps.ite
    | with_reducible apply Keeps.bind
    | with_reducible intro _)

end Keeps

/-! ## The entry points -/

section Entries

variable {I : ExecutionEnv} {S : List UInt256}

/-- A successful `transfer` between holders keeps the invariant. -/
theorem transfer_keeps {dst value : UInt256} (hS : CollisionFree S)
    (hsender : UInt256.ofNat I.source.val ∈ S) (hdst : dst ∈ S) :
    Keeps I (Conserved I.codeOwner · S) (Model.transfer dst value) := by
  intro w r w' hcons hrun
  set sender := UInt256.ofNat I.source.val with hsdef
  set bs := slotWord I w.accounts (Model.balanceSlot sender) with hbs
  by_cases hlt : bs.toNat < value.toNat
  · simp [Model.transfer, ← hsdef, ← hbs, hlt] at hrun
  by_cases hperm : I.perm = true
  swap
  · simp [Model.transfer, checkedSub, exec_sstore, ← hsdef, ← hbs, hlt, hperm] at hrun
  set σ1 := storeWord I.codeOwner w.accounts (Model.balanceSlot sender) (UInt256.sub bs value)
    with hσ1
  set bd := slotWord I σ1 (Model.balanceSlot dst) with hbd
  by_cases hover : UInt256.size ≤ bd.toNat + value.toNat
  · simp [Model.transfer, checkedSub, checkedAdd, exec_sstore, ← hsdef, ← hbs, hlt, hperm,
      ← hσ1, ← hbd, hover] at hrun
  simp [Model.transfer, checkedSub, checkedAdd, exec_sstore, exec_emit, ← hsdef, ← hbs, hlt,
    hperm, ← hσ1, ← hbd, hover] at hrun
  obtain ⟨-, rfl⟩ := hrun
  exact Conserved.move hS hsender hdst (Nat.le_of_not_lt hlt) (Nat.lt_of_not_le hover) hcons

/-- A successful `transferFrom` between holders keeps the invariant, when the allowance slot
    it writes is untracked. -/
theorem transferFrom_keeps {src dst value : UInt256} (hS : CollisionFree S) (hsrc : src ∈ S)
    (hdst : dst ∈ S) (hu : Untracked S (Model.allowanceSlot src (UInt256.ofNat I.source.val))) :
    Keeps I (Conserved I.codeOwner · S) (Model.transferFrom src dst value) := by
  intro w r w' hcons hrun
  set spender := UInt256.ofNat I.source.val with hsdef
  set al := slotWord I w.accounts (Model.allowanceSlot src spender) with hal
  by_cases hla : al.toNat < value.toNat
  · simp [Model.transferFrom, ← hsdef, ← hal, hla] at hrun
  set bs := slotWord I w.accounts (Model.balanceSlot src) with hbs
  by_cases hlb : bs.toNat < value.toNat
  · simp [Model.transferFrom, ← hsdef, ← hal, hla, ← hbs, hlb] at hrun
  by_cases hperm : I.perm = true
  swap
  · simp [Model.transferFrom, checkedSub, exec_sstore, ← hsdef, ← hal, hla, ← hbs, hlb,
      hperm] at hrun
  set σa := storeWord I.codeOwner w.accounts (Model.allowanceSlot src spender)
    (UInt256.sub al value) with hσa
  set bs' := slotWord I σa (Model.balanceSlot src) with hbs'
  by_cases hlb' : bs'.toNat < value.toNat
  · simp [Model.transferFrom, checkedSub, exec_sstore, ← hsdef, ← hal, hla, ← hbs, hlb,
      hperm, ← hσa, ← hbs', hlb'] at hrun
  set σ1 := storeWord I.codeOwner σa (Model.balanceSlot src) (UInt256.sub bs' value) with hσ1
  set bd := slotWord I σ1 (Model.balanceSlot dst) with hbd
  by_cases hover : UInt256.size ≤ bd.toNat + value.toNat
  · simp [Model.transferFrom, checkedSub, checkedAdd, exec_sstore, ← hsdef, ← hal, hla,
      ← hbs, hlb, hperm, ← hσa, ← hbs', hlb', ← hσ1, ← hbd, hover] at hrun
  simp [Model.transferFrom, checkedSub, checkedAdd, exec_sstore, exec_emit, ← hsdef, ← hal,
    hla, ← hbs, hlb, hperm, ← hσa, ← hbs', hlb', ← hσ1, ← hbd, hover] at hrun
  obtain ⟨-, rfl⟩ := hrun
  exact Conserved.move hS hsrc hdst (Nat.le_of_not_lt hlb') (Nat.lt_of_not_le hover)
    (hcons.store_untracked hu _)

/-- A successful `approve` keeps the invariant, when the allowance slot it writes is
    untracked. -/
theorem approve_keeps {spender value : UInt256}
    (hu : Untracked S (Model.allowanceSlot (UInt256.ofNat I.source.val) spender)) :
    Keeps I (Conserved I.codeOwner · S) (Model.approve spender value) := by
  intro w r w' hcons hrun
  by_cases hperm : I.perm = true
  · simp [Model.approve, exec_sstore, exec_emit, hperm] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hcons.store_untracked hu _
  · simp [Model.approve, exec_sstore, hperm] at hrun

theorem transferArm_keeps {cd : ByteArray} (hS : CollisionFree S)
    (hsender : UInt256.ofNat I.source.val ∈ S) (hdst : word cd 4 ∈ S) :
    Keeps I (Conserved I.codeOwner · S) (Model.transferArm cd) := by
  have := transfer_keeps (value := word cd 36) hS hsender hdst
  unfold Model.transferArm; keeps_accounts

theorem transferFromArm_keeps {cd : ByteArray} (hS : CollisionFree S) (hsrc : word cd 4 ∈ S)
    (hdst : word cd 36 ∈ S)
    (hu : Untracked S (Model.allowanceSlot (word cd 4) (UInt256.ofNat I.source.val))) :
    Keeps I (Conserved I.codeOwner · S) (Model.transferFromArm cd) := by
  have := transferFrom_keeps (value := word cd 68) hS hsrc hdst hu
  unfold Model.transferFromArm; keeps_accounts

theorem approveArm_keeps {cd : ByteArray}
    (hu : Untracked S (Model.allowanceSlot (UInt256.ofNat I.source.val) (word cd 4))) :
    Keeps I (Conserved I.codeOwner · S) (Model.approveArm cd) := by
  have := approve_keeps (value := word cd 36) hu
  unfold Model.approveArm; keeps_accounts

/-- The getters change no account. -/
theorem balanceOfArm_keeps {P : AccountMap → Prop} (cd : ByteArray) :
    Keeps I P (Model.balanceOfArm cd) := by
  unfold Model.balanceOfArm Model.balanceOf; keeps_accounts

theorem allowanceArm_keeps {P : AccountMap → Prop} (cd : ByteArray) :
    Keeps I P (Model.allowanceArm cd) := by
  unfold Model.allowanceArm Model.allowance; keeps_accounts

theorem totalSupplyArm_keeps {P : AccountMap → Prop} : Keeps I P Model.totalSupplyArm := by
  unfold Model.totalSupplyArm Model.totalSupply; keeps_accounts

/-- Every successful run of the runtime entry keeps the invariant, on a call that the holders
    cover. -/
theorem runtime_keeps (hS : CollisionFree S) (hcall : Covers S I) :
    Keeps I (Conserved I.codeOwner · S) Model.runtime := by
  unfold Model.runtime
  refine Keeps.calldata_bind (Keeps.ite (fun _ => Keeps.revert _) fun _ => ?_)
  refine Keeps.ite (fun h => approveArm_keeps (hcall.approve h)) fun _ => ?_
  refine Keeps.ite (fun _ => totalSupplyArm_keeps) fun _ => ?_
  refine Keeps.ite (fun h => ?_) fun _ => ?_
  · obtain ⟨hsrc, hdst, hu⟩ := hcall.transferFrom h
    exact transferFromArm_keeps hS hsrc hdst hu
  refine Keeps.ite (fun _ => balanceOfArm_keeps _) fun _ => ?_
  refine Keeps.ite (fun h => transferArm_keeps hS (hcall.transfer h).1 (hcall.transfer h).2)
    fun _ => ?_
  exact Keeps.ite (fun _ => allowanceArm_keeps _) fun _ => Keeps.revert _

theorem runtime_noStop : Model.runtime.NoStop := by
  unfold Model.runtime Model.approveArm Model.approve Model.totalSupplyArm Model.totalSupply
    Model.transferFromArm Model.transferFrom Model.balanceOfArm Model.balanceOf
    Model.transferArm Model.transfer Model.allowanceArm Model.allowance
  no_stop

theorem init_noStop (args : ByteArray) : (Model.init args).NoStop := by
  unfold Model.init Model.initBody
  no_stop

end Entries

/-! ## The capstones -/

/-- Every run of the runtime entry that returns or stops, on a call that the holders `S` cover,
    from a world where their balances add up to the supply, ends in a world where they do. -/
theorem runtime_conserves {I : ExecutionEnv} {S : List UInt256} {w w' : World}
    {out : ByteArray} (hS : CollisionFree S) (hcall : Covers S I)
    (hcons : Conserved I.codeOwner w.accounts S)
    (hrun : Succeeds (Model.runtime.exec I w) out w') :
    Conserved I.codeOwner w'.accounts S := by
  rcases hrun with hrun | hrun
  · exact runtime_keeps hS hcall w out w' hcons hrun
  · exact absurd hrun (runtime_noStop I w out w')

/-- The constructor makes the balances of the holders `S` add up to the supply, when the
    deployer is one of them and each starts with none. -/
theorem init_conserves {I : ExecutionEnv} {S : List UInt256} {w w' : World} {args : ByteArray}
    (hS : CollisionFree S) (hdeployer : UInt256.ofNat I.source.val ∈ S)
    (hzero : ∀ a ∈ S, balance I.codeOwner w.accounts a = ⟨0⟩)
    (hrun : (Model.init args).exec I w = some (.ok ((), w'))) :
    Conserved I.codeOwner w'.accounts S := by
  set c := I.codeOwner
  have hsum : balanceSum c w.accounts S = 0 := by
    unfold balanceSum
    rw [List.map_congr_left (g := fun _ => 0) fun a ha => by rw [hzero a ha]; rfl]
    simp
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · simp [Model.init, exec_nonPayable, hwv] at hrun
  by_cases hshort : args.size < 32
  · simp [Model.init, exec_nonPayable, hwv, hshort] at hrun
  by_cases hperm : I.perm = true
  swap
  · simp [Model.init, Model.initBody, exec_nonPayable, exec_sstore, hwv, hshort, hperm] at hrun
  simp [Model.init, Model.initBody, exec_nonPayable, exec_sstore, exec_emit, hwv, hshort,
    hperm] at hrun
  obtain rfl := hrun
  set sender := UInt256.ofNat I.source.val
  set v := word args 0
  unfold Conserved supply
  cases ha : w.accounts.get? c with
  | none =>
    rw [storeWord_absent ha, storeWord_absent ha, hsum]
    unfold storageAt; rw [ha]; rfl
  | some acc =>
  obtain ⟨acc1, ha1⟩ := storeWord_present ha (Model.balanceSlot sender) v
  have h1 := balanceSum_store w.accounts ha S hS.nodup hS.inj sender v hdeployer
  rw [hzero sender hdeployer, hsum] at h1
  rw [balanceSum_store_other _ S _ _ hS.supply, storageAt_store_self _ ha1]
  simpa using h1

end FeProofs.ERC20
