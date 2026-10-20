import Reasoning.EVMWord
import Reasoning.Stepping
import Reasoning.ExternalCall
import FeProofs.Common.Memory

/-!
# External calls

`staticCallBridge` couples an EVM `STATICCALL` step with the Stele `callViaEVM` it performs; the
`callOutput_*` lemmas read the memory the call's output was copied into; Fe checks a call's return
data with `RETURNDATASIZE < 32`, and `lt32_size_word`/`lt32_size_word_ne` are that comparison's
outcomes.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs

theorem lt32_size_word {n : ℕ} (hn : 32 ≤ n) (hb : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) = UInt256.ofNat 0 := by
  have hw : ¬ (UInt256.ofNat n < UInt256.ofNat 32) := by
    rw [ofNat_lt_ofNat hb (by decide)]; omega
  simp only [UInt256.lt, decide_eq_false hw]; decide

theorem lt32_size_word_ne {n : ℕ} (hn : n < 32) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 32) ≠ UInt256.ofNat 0 := by
  have hw : UInt256.ofNat n < UInt256.ofNat 32 :=
    (ofNat_lt_ofNat (lt_trans hn (by decide)) (by decide)).mpr hn
  simp only [UInt256.lt, decide_eq_true hw]; decide

/-- `address(2)` as the spec evaluates it. -/
abbrev precompile2 : AccountAddress := .ofNat 2

theorem precompile2_eq : EVM.address precompile2 = AccountAddress.ofUInt256 (UInt256.ofNat 2) := by
  decide

theorem staticCallBridge {σ : AccountMap} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {evm : EVM.State} {code mem rdata : ByteArray}
    {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.STATICCALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.solcStaticcallDepthLimit h hdec hd hov
    refine ⟨{ evm with substate :=
        (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
      σ, false, ByteArray.empty, _, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩, hr, by decide⟩
    exact callViaEVM.callNotMade rfl rfl
      (fun hgood ↦ hgood.2 (by simpa only [hs.env] using hd))
  · have hdl : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, AIn, gasCall, k', C', ⟨gasLeft, A', hΘ⟩, hr, hout⟩ :=
      RD.solcStaticcall h hdec hdl hov
    refine ⟨{ evm with accountMap := σ', substate := A' },
      σ', z, out, _, k', C', ?_, ⟨hs.world, hs.env, rfl⟩, hr, hout⟩
    apply callViaEVM.callMade (perm := false) (g' := gasLeft) wordOfInt_zero.symm
      ⟨gasCall, AIn, ?_⟩ rfl (Fin.zero_le _) (by simpa only [hs.env] using hd)
    simpa only [hs.env, ← hs.accounts, hs.world, accountAddress_roundtrip, Bool.false_and] using hΘ

/-- After a call returning at least a word into `[off, off + 32)` of memory that already covers
    that window, `MLOAD(off)` is the first returned word. -/
theorem callOutput_load (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (callOutputMem mem out off ⟨32⟩) = calldataWord out 0 := by
  have hsize := callOutput32_size mem out off hb hin
  unfold memLoad
  rw [if_neg (by rw [hsize]; omega), callOutput32_read_word mem out off hb hs (by omega),
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- `MLOAD` of the word a successful call wrote at `off`. -/
theorem callOutput_loadAt (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (callOutputMem mem out off (UInt256.ofNat 32)) = calldataWord out 0 :=
  callOutput_load mem out off hb hs hin

theorem callOutput_sizeAt (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hin : off.toNat + 32 ≤ mem.size) :
    (callOutputMem mem out off (UInt256.ofNat 32)).size = mem.size :=
  callOutput32_size mem out off hb hin

theorem callOutput_memLoad64' (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hoff : 96 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (callOutputMem mem out off ⟨32⟩) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold callOutputMem
  rw [callOutputLen32 hb, Nat.min_eq_left hs]
  exact memLoad64_write out mem (by decide) (by omega) (by have := USize.le_size; omega) hoff
    (by omega)

/-- A successful call's output write keeps `MLOAD(0x40)`. -/
theorem callOutput_memLoad64 (mem out : ByteArray) (off : UInt256) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hoff : 96 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (callOutputMem mem out off (UInt256.ofNat 32)) =
      memLoad (UInt256.ofNat 64) mem :=
  callOutput_memLoad64' mem out off hb hs hoff hin

theorem callOutput_load32 (mem out : ByteArray) (hb : out.size < UInt256.size)
    (hs : 32 ≤ out.size) (hin : 32 ≤ mem.size) :
    memLoad (⟨0⟩ : UInt256) (callOutputMem mem out (⟨0⟩ : UInt256) (UInt256.ofNat 32)) =
      calldataWord out 0 :=
  callOutput_load mem out ⟨0⟩ hb hs (by simpa using hin)

theorem out32_len (out : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size) :
    (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = 32 := by
  have h := callOutputLen32 hob
  rw [Nat.min_eq_left hsz] at h
  exact h

/-- A returned word copied to `off` leaves a window it does not overlap unchanged. -/
theorem out32_extract (out base : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size)
    {off : UInt256} {i j : Nat} (hij : i ≤ j) (hj : j ≤ base.size)
    (hd : j ≤ off.toNat ∨ (off.toNat + 32 ≤ i ∧ off.toNat ≤ base.size)) (hgap : off.toNat < 2 ^ 32) :
    (callOutputMem base out off (UInt256.ofNat 32)).extract i j = base.extract i j := by
  unfold callOutputMem
  rw [out32_len out hob hsz]
  rcases hd with hd | ⟨hd, hb⟩
  · exact write_extract_below _ _ (by decide) (by omega) (small_gap _ _ hgap) hij hj hd
  · exact write_extract_preserved _ _ (by decide) (by omega) hb hij hj (Or.inr hd)

theorem out32_size (out base : ByteArray) (hob : out.size < UInt256.size) (hsz : 32 ≤ out.size)
    {off : UInt256} (hgap : off.toNat < 2 ^ 32) :
    base.size ≤ (callOutputMem base out off (UInt256.ofNat 32)).size := by
  unfold callOutputMem
  rw [out32_len out hob hsz]
  exact write_size_ge _ _ (by decide) (by omega) (small_gap _ _ hgap)

end FeProofs
