import FeProofs.ERC20.Model
import Reasoning.PackedStorage
import Reasoning.EVMWord

/-!
# FeERC20: transfers conserve the sum of balances

A property of the model alone.  The sum is taken over a finite list of holders whose balance
slots do not collide, with each other or with the total-supply slot.  That condition is about the
keys in use, never about all keys: hashed slots of all 2^160 addresses almost surely do collide.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Fe Fe.EVM

namespace FeProofs.ERC20

variable {I : ExecutionEnv}

/-- The balance of `a` in the account map `σ`. -/
def balance (I : ExecutionEnv) (σ : AccountMap) (a : UInt256) : UInt256 :=
  slotWord I σ (Model.balanceSlot a)

/-- The sum of the balances of the holders `S`, as a natural number. -/
def balanceSum (I : ExecutionEnv) (σ : AccountMap) (S : List UInt256) : ℕ :=
  (S.map fun a => (balance I σ a).toNat).sum

/-- The balance slots of the holders `S` are pairwise distinct and none is the supply slot. -/
structure CollisionFree (S : List UInt256) : Prop where
  nodup : S.Nodup
  inj : ∀ a ∈ S, ∀ b ∈ S, Model.balanceSlot a = Model.balanceSlot b → a = b
  supply : ∀ a ∈ S, Model.balanceSlot a ≠ Model.totalSupplySlot

theorem slotWord_store_ne (σ : AccountMap) (r s v : UInt256) (h : r ≠ s) :
    slotWord I (storeWord I.codeOwner σ s v) r = slotWord I σ r :=
  solcSlotWord_sstore_ne σ I r s v h

theorem slotWord_store_self (σ : AccountMap) {acc : Account}
    (ha : σ.get? I.codeOwner = some acc) (s v : UInt256) :
    slotWord I (storeWord I.codeOwner σ s v) s = v :=
  solcSlotWord_sstore_present σ I ha s v

/-- A store to a slot that no holder in `S` uses leaves their sum unchanged. -/
theorem balanceSum_store_other (σ : AccountMap) (S : List UInt256) (s v : UInt256)
    (h : ∀ b ∈ S, Model.balanceSlot b ≠ s) :
    balanceSum I (storeWord I.codeOwner σ s v) S = balanceSum I σ S := by
  unfold balanceSum
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [balance]
  rw [slotWord_store_ne σ _ s v (h b hb)]

/-- A store to the balance of a holder in `S` changes the sum by the change of that balance. -/
theorem balanceSum_store (σ : AccountMap) {acc : Account} (ha : σ.get? I.codeOwner = some acc)
    (S : List UInt256) (hnd : S.Nodup)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, Model.balanceSlot a = Model.balanceSlot b → a = b)
    (a v : UInt256) (hmem : a ∈ S) :
    balanceSum I (storeWord I.codeOwner σ (Model.balanceSlot a) v) S + (balance I σ a).toNat
      = balanceSum I σ S + v.toNat := by
  induction S with
  | nil => cases hmem
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxs : xs.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hax : a = x
    · subst hax
      have hother : ∀ b ∈ xs, Model.balanceSlot b ≠ Model.balanceSlot a := fun b hb hEq =>
        hx (by rw [← hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hEq]; exact hb)
      have hrest := balanceSum_store_other (I := I) σ xs (Model.balanceSlot a) v hother
      simp only [balanceSum, List.map_cons, List.sum_cons, balance] at hrest ⊢
      rw [slotWord_store_self σ ha, hrest]
      omega
    · have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left hax
      have hne : Model.balanceSlot x ≠ Model.balanceSlot a := fun hEq =>
        hax (hinj a hmem x List.mem_cons_self hEq.symm)
      have ih' := ih hxs (fun p hp q hq => hinj p (List.mem_cons_of_mem _ hp) q
        (List.mem_cons_of_mem _ hq)) hmem'
      simp only [balanceSum, List.map_cons, List.sum_cons, balance] at ih' ⊢
      rw [slotWord_store_ne σ _ _ v hne]
      omega

/-- The total supply recorded in `σ`. -/
def supply (I : ExecutionEnv) (σ : AccountMap) : UInt256 := slotWord I σ Model.totalSupplySlot

/-- The holders' balances add up to the recorded supply. -/
def Conserved (I : ExecutionEnv) (σ : AccountMap) (S : List UInt256) : Prop :=
  balanceSum I σ S = (supply I σ).toNat

/-- A successful `transfer` between holders in `S` keeps the sum of balances equal to the supply. -/
theorem transfer_conserves {w w' : World} {acc : Account} {S : List UInt256} {dst value : UInt256}
    {r : Bool}
    (hacc : w.accounts.get? I.codeOwner = some acc) (hS : CollisionFree S)
    (hsender : UInt256.ofNat I.source.val ∈ S) (hdst : dst ∈ S)
    (hcons : Conserved I w.accounts S)
    (hrun : (Model.transfer dst value).exec I w = some (.ok (r, w'))) :
    Conserved I w'.accounts S := by
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
  obtain ⟨acc1, hacc1⟩ := sstoreAccountMap_get?_owner_some_of_some w.accounts I.codeOwner
    (Model.balanceSlot sender) (UInt256.sub bs value) hacc
  have h1 := balanceSum_store (I := I) w.accounts hacc S hS.nodup hS.inj sender
    (UInt256.sub bs value) hsender
  have h2 := balanceSum_store (I := I) σ1 hacc1 S hS.nodup hS.inj dst (bd + value) hdst
  have hsub : (UInt256.sub bs value).toNat = bs.toNat - value.toNat :=
    usub_toNat (Nat.le_of_not_lt hlt)
  have hadd : (bd + value).toNat = bd.toNat + value.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (Nat.lt_of_not_le hover)]
  have hsup : supply I (storeWord I.codeOwner σ1 (Model.balanceSlot dst) (bd + value))
      = supply I w.accounts := by
    unfold supply
    rw [slotWord_store_ne _ _ _ _ (hS.supply dst hdst).symm,
      slotWord_store_ne _ _ _ _ (hS.supply sender hsender).symm]
  have h1' : balanceSum I σ1 S + bs.toNat
      = balanceSum I w.accounts S + (bs.toNat - value.toNat) := by rw [← hsub]; exact h1
  have h2' : balanceSum I (storeWord I.codeOwner σ1 (Model.balanceSlot dst) (bd + value)) S
      + bd.toNat = balanceSum I σ1 S + (bd.toNat + value.toNat) := by rw [← hadd]; exact h2
  have hle : value.toNat ≤ bs.toNat := Nat.le_of_not_lt hlt
  unfold Conserved at hcons ⊢
  show balanceSum I (storeWord I.codeOwner σ1 (Model.balanceSlot dst) (bd + value)) S = _
  rw [hsup, ← hcons]
  omega

end FeProofs.ERC20
