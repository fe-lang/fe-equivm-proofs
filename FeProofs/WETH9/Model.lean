import Fe.EVM.Calls
import Fe.EVM.Refine
import FeProofs.Common.SolString

/-!
# FeWETH9 model

Written by hand from `src/lib.fe` and `src/sol_string.fe`, in the shape of the exported arms but
without memory: one definition per `recv` arm (`transfer` and `transferFrom` share Fe's
`transfer_from`, `deposit` and the fallback Fe's `deposit`), an entry arm around each that
decodes its arguments and encodes its result, the runtime entry that dispatches on the selector,
and the constructor.

A string getter returns the ABI encoding of the bytes as EquiVM reads them (`strBytes`), and the
constructor writes a string as EquiVM's `strWriteMap` does: these are the forms the bytecode's
traces conclude with.  A failed `assert!` is `Panic(0x01)`, as Fe lowers it; a string head whose
length contradicts its short/long flag reverts with `Panic(0x22)`, and an allocation of `2 ^ 64`
bytes or more fails with `Panic(0x41)`.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM
open Stele (solidityDecodeBytesLengthHeader)

namespace FeProofs.WETH9.Model

/-! ## Storage of `Weth9Store` -/

def nameSlot : UInt256 := ⟨0⟩
def symbolSlot : UInt256 := ⟨1⟩
def decimalsSlot : UInt256 := ⟨2⟩
def balanceOfRoot : UInt256 := ⟨3⟩
def allowanceRoot : UInt256 := ⟨4⟩

/-- `store.balance_of[owner]` -/
def balanceSlot (owner : UInt256) : UInt256 := mapSlot owner balanceOfRoot

/-- `store.allowance[owner][guy]` -/
def allowanceSlot (owner guy : UInt256) : UInt256 := mapSlot guy (mapSlot owner allowanceRoot)

/-! ## Events -/

def approvalTopic : UInt256 :=
  uInt256OfByteArray (KEC "Approval(address,address,uint256)".toUTF8)

def transferTopic : UInt256 :=
  uInt256OfByteArray (KEC "Transfer(address,address,uint256)".toUTF8)

def depositTopic : UInt256 := uInt256OfByteArray (KEC "Deposit(address,uint256)".toUTF8)

def withdrawalTopic : UInt256 := uInt256OfByteArray (KEC "Withdrawal(address,uint256)".toUTF8)

/-! ## Strings -/

/-- `SolString::load` of the string at `slot`, encoded by `return_value`: the offset word `0x20`,
    the length word, then the bytes padded to words. -/
def stringReturn (slot : UInt256) : FeM ByteArray := do
  let I ← read
  let σ := (← get).accounts
  match solidityDecodeBytesLengthHeader (slotWord I σ slot) with
  | .ok L =>
    if 64 + 32 * ((L + 31) / 32) < 2 ^ 64 then
      return (UInt256.ofNat 32).toByteArray ++ ((UInt256.ofNat L).toByteArray ++
        (strBytes σ I slot L ++ zpad (32 * ((L + 31) / 32) - L)))
    else M.panic 0x41
  | _ => M.revert (panicData 0x22)

instance (S : UInt256) : Decidable (strHeadBad S) := by unfold strHeadBad; infer_instance

/-- `SolString::store` of a string shorter than a word at `slot`: the head, then the data words
    of the old value zeroed. -/
def storeString (slot : UInt256) (bytes : ByteArray) : FeM Unit := do
  let I ← read
  let σ := (← get).accounts
  if strHeadBad (slotWord I σ slot) then M.revert (panicData 0x22)
  else if I.perm then modify fun w => { w with accounts := strWriteMap I σ slot bytes }
  else M.fail .static

/-! ## `recv Weth9Msg` and the fallback -/

/-- `Approve { guy, wad } -> bool` -/
def approve (guy wad : UInt256) : FeM Bool := do
  let src ← caller
  sstore (allowanceSlot src guy) wad
  emit #[approvalTopic, src, guy] wad.toByteArray
  return true

/-- `TotalSupply -> u256`: the contract's balance. -/
def totalSupply : FeM UInt256 := selfbalance

/-- Fe's `transfer_from(src, dst, wad)`, with wrapping arithmetic. -/
def transferFrom (src dst wad : UInt256) : FeM Bool := do
  if (← sload (balanceSlot src)).toNat < wad.toNat then M.panic 0x01
  let sender ← caller
  if src ≠ sender then
    let allowed ← sload (allowanceSlot src sender)
    if allowed ≠ UInt256.ofNat (UInt256.size - 1) then
      if allowed.toNat < wad.toNat then M.panic 0x01
      sstore (allowanceSlot src sender) (allowed - wad)
  sstore (balanceSlot src) ((← sload (balanceSlot src)) - wad)
  sstore (balanceSlot dst) ((← sload (balanceSlot dst)) + wad)
  emit #[transferTopic, src, dst] wad.toByteArray
  return true

/-- `Withdraw { wad }`: send `wad` to the caller with the stipend's gas, and revert unless the
    call succeeds.  The call has no input and copies no output. -/
def withdraw (wad : UInt256) : FeM Unit := do
  let src ← caller
  let bal ← sload (balanceSlot src)
  if bal.toNat < wad.toNat then M.panic 0x01
  sstore (balanceSlot src) (bal - wad)
  let ok ← call (if wad = ⟨0⟩ then ⟨2300⟩ else ⟨0⟩) src wad ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩
  if ok = ⟨0⟩ then M.panic 0x01
  emit #[withdrawalTopic, src] wad.toByteArray

/-- `Decimals -> u8`: the low byte of slot 2. -/
def decimals : FeM UInt256 := do return UInt256.land (← sload decimalsSlot) (UInt256.ofNat 255)

/-- `BalanceOf { owner } -> u256` -/
def balanceOf (owner : UInt256) : FeM UInt256 := sload (balanceSlot owner)

/-- `Allowance { owner, guy } -> u256` -/
def allowance (owner guy : UInt256) : FeM UInt256 := sload (allowanceSlot owner guy)

/-- Fe's `deposit()`, the arm `Deposit` and the fallback: credit the caller with the call value,
    with wrapping arithmetic. -/
def deposit : FeM Unit := do
  let dst ← caller
  let wad ← callvalue
  sstore (balanceSlot dst) ((← sload (balanceSlot dst)) + wad)
  emit #[depositTopic, dst] wad.toByteArray

/-! ## Entry arms: reject call value, decode the arguments, run the arm, encode the result -/

def encodeBool (b : Bool) : ByteArray := UInt256.toByteArray (if b then ⟨1⟩ else ⟨0⟩)

def nameArm : FeM ByteArray := do
  nonPayable
  stringReturn nameSlot

def approveArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return encodeBool (← approve (word cd 4) (word cd 36))

def totalSupplyArm : FeM ByteArray := do
  nonPayable
  return (← totalSupply).toByteArray

def transferFromArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 3 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  if NotAddress (word cd 36) then M.revert ByteArray.empty
  return encodeBool (← transferFrom (word cd 4) (word cd 36) (word cd 68))

def withdrawArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  withdraw (word cd 4)
  return ByteArray.empty

def decimalsArm : FeM ByteArray := do
  nonPayable
  return (← decimals).toByteArray

def balanceOfArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return (← balanceOf (word cd 4)).toByteArray

def symbolArm : FeM ByteArray := do
  nonPayable
  stringReturn symbolSlot

def transferArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return encodeBool (← transferFrom (← caller) (word cd 4) (word cd 36))

/-- `Deposit` and the fallback: payable, and returning nothing. -/
def depositArm : FeM ByteArray := do
  deposit
  return ByteArray.empty

def allowanceArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  if NotAddress (word cd 36) then M.revert ByteArray.empty
  return (← allowance (word cd 4) (word cd 36)).toByteArray

/-! ## Selectors -/

def nameSelector : ByteArray := ⟨#[0x06, 0xfd, 0xde, 0x03]⟩
def approveSelector : ByteArray := ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
def totalSupplySelector : ByteArray := ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
def transferFromSelector : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
def withdrawSelector : ByteArray := ⟨#[0x2e, 0x1a, 0x7d, 0x4d]⟩
def decimalsSelector : ByteArray := ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩
def balanceOfSelector : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
def symbolSelector : ByteArray := ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩
def transferSelector : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
def depositSelector : ByteArray := ⟨#[0xd0, 0xe3, 0x0d, 0xb0]⟩
def allowanceSelector : ByteArray := ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- The runtime entry: calldata shorter than a selector, or with a selector of no arm, runs the
    fallback. -/
def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then depositArm
  else if nameSelector == cd.extract 0 4 then nameArm
  else if approveSelector == cd.extract 0 4 then approveArm cd
  else if totalSupplySelector == cd.extract 0 4 then totalSupplyArm
  else if transferFromSelector == cd.extract 0 4 then transferFromArm cd
  else if withdrawSelector == cd.extract 0 4 then withdrawArm cd
  else if decimalsSelector == cd.extract 0 4 then decimalsArm
  else if balanceOfSelector == cd.extract 0 4 then balanceOfArm cd
  else if symbolSelector == cd.extract 0 4 then symbolArm
  else if transferSelector == cd.extract 0 4 then transferArm cd
  else if depositSelector == cd.extract 0 4 then depositArm
  else if allowanceSelector == cd.extract 0 4 then allowanceArm cd
  else depositArm

/-! ## The constructor -/

/-- `"Wrapped Ether"` -/
def nameBytes : ByteArray := ⟨#[87, 114, 97, 112, 112, 101, 100, 32, 69, 116, 104, 101, 114]⟩

/-- `"WETH"` -/
def symbolBytes : ByteArray := ⟨#[87, 69, 84, 72]⟩

/-- `init()`: the two strings, then `decimals` written into the low byte of slot 2. -/
def init : FeM Unit := do
  nonPayable
  storeString nameSlot nameBytes
  storeString symbolSlot symbolBytes
  let w ← sload decimalsSlot
  sstore decimalsSlot
    (UInt256.lor (UInt256.ofNat 18) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) w))

def contract : ContractModel :=
  { init := fun _ => init >>= fun _ => pure ByteArray.empty, runtime := runtime }

end FeProofs.WETH9.Model
