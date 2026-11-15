import Fe.Sonatina.Run
import FeProofs.Deposit.Exported

/-!
# The SHA-256 calls of FeDeposit

Every hash the deposit contract computes, in the exported code and in the machine IR, is
`gas()` followed by `STATICCALL` of the SHA-256 precompile (address 2) on 64 bytes of memory,
with 32 bytes of output; a call that fails or returns fewer than 32 bytes reverts with no data.
Both sides run the model library's `Fe.EVM.gas` and `Fe.EVM.staticcall`, from the same feed,
the same accounts and the same 64 input bytes, so they make the same message call `shaT`, with
the same result `shaR`: nothing about SHA-256 itself is needed.  `staticcall_sha` states the
call in that form, for both sides to reach; a proof then names `shaR …` once for both.
-/

namespace FeProofs.Deposit.Sonatina

open Ethereum Ethereum.EVM Ethereum.EVM.Invariant Fe Fe.EVM Reasoning.Theory

/-- The message call a hash of the 64 bytes `d` makes from accounts `σ`, with the gas argument
    `g` and the feed's entry `s` for the call. -/
def shaT (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply) (d : ByteArray) :
    ThetaCall where
  σ := σ
  σ₀ := s.orig
  A := s.substate
  s := I.codeOwner
  o := I.sender
  r := AccountAddress.ofUInt256 (UInt256.ofNat 2)
  c := toExecute σ (AccountAddress.ofUInt256 (UInt256.ofNat 2))
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
def shaR (I : ExecutionEnv) (σ : AccountMap) (g : UInt256) (s : Supply) (d : ByteArray) :
    AccountMap × UInt256 × Substate × Bool × ByteArray :=
  if I.depth < 1024 then (shaT I σ g s d).run else (σ, ⟨0⟩, s.substate, false, .empty)

/-- The world after the call, from `w`: the result's accounts, the logs it appended, its output
    as the return data and its first 32 bytes at `r`, the feed's rest, and the call recorded. -/
def shaWorld (I : ExecutionEnv) (w : World) (g : UInt256) (s : Supply) (rest : List Supply)
    (d : ByteArray) (r : Nat) : World :=
  { w with
    accounts := (shaR I w.accounts g s d).1
    logs := w.logs ++ appended s.substate (shaR I w.accounts g s d).2.2.1
    memory := (shaR I w.accounts g s d).2.2.2.2.write 0 w.memory r
      (min (UInt256.ofNat 32) (UInt256.ofNat (shaR I w.accounts g s d).2.2.2.2.size)).toNat
    returnData := (shaR I w.accounts g s d).2.2.2.2
    feed := rest
    calls := if I.depth < 1024 then w.calls ++ [Made.theta (shaT I w.accounts g s d)]
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

/-- A static call of the precompile at address 2 on `n` bytes at `p`, its first 32 bytes of
    output at `r`, on a feed with an entry: the call `shaT` with the result `shaR`. -/
theorem staticcall_sha {I : ExecutionEnv} {w : World} {s : Supply} {rest : List Supply}
    (hfeed : w.feed = s :: rest) (g p n r : UInt256) :
    (Fe.EVM.staticcall g (UInt256.ofNat 2) p n r (UInt256.ofNat 32)).exec I w =
      some (.ok (if (shaR I w.accounts g s (w.memory.readWithPadding p.toNat n.toNat)).2.2.2.1
          then ⟨1⟩ else ⟨0⟩,
        shaWorld I w g s rest (w.memory.readWithPadding p.toNat n.toNat) r.toNat)) := by
  simp only [Fe.EVM.staticcall, Fe.EVM.message, Fe.EVM.next, hfeed, Fe.M.exec_bind,
    Fe.M.exec_read, Fe.M.exec_get, Fe.M.exec_set, Fe.M.exec_pure, zero_le_word, true_and]
  unfold shaWorld shaR
  by_cases hd : I.depth < 1024 <;> simp only [hd, if_true, if_false] <;> rfl

/-- A static call on an empty feed does not terminate. -/
theorem staticcall_nil {I : ExecutionEnv} {w : World} (hfeed : w.feed = [])
    (g a p n r k : UInt256) : (Fe.EVM.staticcall g a p n r k).exec I w = none := by
  simp [Fe.EVM.staticcall, Fe.EVM.message, Fe.EVM.next, hfeed]

end FeProofs.Deposit.Sonatina
