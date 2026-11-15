import Fe.EVM.Refine
import EVM.Types

/-!
# FeERC20 model

Written by hand from `FeERC20.fe`, in the shape the exporter should print: one definition per
`recv` arm, an entry arm around each that decodes its arguments and encodes its result, and the
runtime entry that dispatches on the selector.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20.Model

/-! ## Storage roots of `TokenStore` -/

def balancesRoot : UInt256 := ⟨0⟩
def allowancesRoot : UInt256 := ⟨1⟩
def totalSupplySlot : UInt256 := ⟨2⟩

/-- `store.balances[owner]` -/
def balanceSlot (owner : UInt256) : UInt256 := mapSlot owner balancesRoot

/-- `store.allowances[owner][spender]` -/
def allowanceSlot (owner spender : UInt256) : UInt256 :=
  mapSlot spender (mapSlot owner allowancesRoot)

/-! ## Events -/

def transferTopic : UInt256 :=
  uInt256OfByteArray (KEC "Transfer(address,address,uint256)".toUTF8)

def approvalTopic : UInt256 :=
  uInt256OfByteArray (KEC "Approval(address,address,uint256)".toUTF8)

/-! ## `recv Erc20Msg` -/

/-- `Transfer { to, value } -> bool` -/
def transfer (dst value : UInt256) : FeM Bool := do
  let sender ← caller
  if (← sload (balanceSlot sender)).toNat < value.toNat then
    M.revert (assertData "ERC20: insufficient balance")
  sstore (balanceSlot sender) (← checkedSub (← sload (balanceSlot sender)) value)
  sstore (balanceSlot dst) (← checkedAdd (← sload (balanceSlot dst)) value)
  emit #[transferTopic, sender, dst] value.toByteArray
  return true

/-- `Approve { spender, value } -> bool` -/
def approve (spender value : UInt256) : FeM Bool := do
  let owner ← caller
  sstore (allowanceSlot owner spender) value
  emit #[approvalTopic, owner, spender] value.toByteArray
  return true

/-- `TransferFrom { from, to, value } -> bool` -/
def transferFrom (src dst value : UInt256) : FeM Bool := do
  let spender ← caller
  let currentAllowance ← sload (allowanceSlot src spender)
  if currentAllowance.toNat < value.toNat then
    M.revert (assertData "ERC20: insufficient allowance")
  if (← sload (balanceSlot src)).toNat < value.toNat then
    M.revert (assertData "ERC20: insufficient balance")
  sstore (allowanceSlot src spender) (← checkedSub currentAllowance value)
  sstore (balanceSlot src) (← checkedSub (← sload (balanceSlot src)) value)
  sstore (balanceSlot dst) (← checkedAdd (← sload (balanceSlot dst)) value)
  emit #[transferTopic, src, dst] value.toByteArray
  return true

/-- `BalanceOf { owner } -> u256` -/
def balanceOf (owner : UInt256) : FeM UInt256 := sload (balanceSlot owner)

/-- `Allowance { owner, spender } -> u256` -/
def allowance (owner spender : UInt256) : FeM UInt256 := sload (allowanceSlot owner spender)

/-- `TotalSupply -> u256` -/
def totalSupply : FeM UInt256 := sload totalSupplySlot

/-! ## Entry arms: reject call value, decode the arguments, run the arm, encode the result -/

def encodeBool (b : Bool) : ByteArray := UInt256.toByteArray (if b then ⟨1⟩ else ⟨0⟩)

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

def balanceOfArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return (← balanceOf (word cd 4)).toByteArray

def transferArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return encodeBool (← transfer (word cd 4) (word cd 36))

def allowanceArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  if NotAddress (word cd 36) then M.revert ByteArray.empty
  return (← allowance (word cd 4) (word cd 36)).toByteArray

/-! ## Selectors -/

def approveSelector : ByteArray := ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
def totalSupplySelector : ByteArray := ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
def transferFromSelector : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
def balanceOfSelector : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
def transferSelector : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
def allowanceSelector : ByteArray := ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- The runtime entry. -/
def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then M.revert ByteArray.empty
  else if approveSelector == cd.extract 0 4 then approveArm cd
  else if totalSupplySelector == cd.extract 0 4 then totalSupplyArm
  else if transferFromSelector == cd.extract 0 4 then transferFromArm cd
  else if balanceOfSelector == cd.extract 0 4 then balanceOfArm cd
  else if transferSelector == cd.extract 0 4 then transferArm cd
  else if allowanceSelector == cd.extract 0 4 then allowanceArm cd
  else M.revert ByteArray.empty

/-- `init(initial_supply: u256)` -/
def initBody (initialSupply : UInt256) : FeM Unit := do
  let sender ← caller
  sstore (balanceSlot sender) initialSupply
  sstore totalSupplySlot initialSupply
  emit #[transferTopic, ⟨0⟩, sender] initialSupply.toByteArray

def init (args : ByteArray) : FeM Unit := do
  nonPayable
  if args.size < 32 then M.revert ByteArray.empty
  initBody (word args 0)

def contract : ContractModel :=
  { init := fun args => init args >>= fun _ => pure ByteArray.empty, runtime := runtime }

end FeProofs.ERC20.Model

namespace FeProofs.ERC20

/-- The ABI-encoded constructor argument. -/
abbrev ctorTail (w : UInt256) : ByteArray := (EVM.Word.toBytesBE w).toByteArray

end FeProofs.ERC20
