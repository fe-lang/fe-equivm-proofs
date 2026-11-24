import Fe.EVM.Calls
import Fe.EVM.Refine
import Fe.IR.Json
import Fe.Sem.Contract

/-!
# fe-spec's interpreter on the EVM

fe-spec (`../fe-spec-evm`) defines what a Fe program means by an interpreter of the compiler's
normalized IR, parametric in a host: the primitive operations of the target, in the model monad
`Fe.M`.  `specHost` is that host on the world of an exported model, each operation the one of
`World.lean` or `Calls.lean` that exported code calls for it, with words as `Nat`s at the
interface and `UInt256`s inside.  An interpreter run and a run of the exported model then act on
the same `World` through the same primitives, so the differential tests (`Diff.lean`,
`Generate.lean`) compare them, and the bytecode, from one initial world and feed.

Memory is the model's: the interpreter allocates with `alloc`, and its runs reserve low memory
first, as the exported entries do (`entry`, `deploy`).  Memory is never compared: the
interpreter keeps locals in cells of its own, so what it allocates differs from the model.

Where `World.lean` and `Calls.lean` have no operation, the host is the EVM's: `msize()` is the
memory size rounded up to a word.  `selfdestruct` is not provided: `Calls.lean`'s halts, where
the host's returns to the interpreter, and exported code never calls it.
-/

namespace Fe.EVM

open Ethereum

/-- The host whose running code's own region, before any data appended to it, is `regionLen`
    bytes: the creation code's, whose constructor arguments follow it, or the runtime code's,
    whose immutable fields follow it.  `creations` are the creation codes of the contracts the
    running one may deploy, by name. -/
def specHost (regionLen : Nat) (creations : List (String × ByteArray)) :
    Fe.Host.Host Env World where
  alloc size := return (← alloc (.ofNat size)).toNat
  memRead addr len := return (← get).memory.readWithPadding addr len
  memWrite addr data := mstoreBytes (.ofNat addr) data
  sload slot := return (← sload (.ofNat slot)).toNat
  sstore slot value := sstore (.ofNat slot) (.ofNat value)
  tload slot := return (← tload (.ofNat slot)).toNat
  tstore slot value := tstore (.ofNat slot) (.ofNat value)
  callDataRead offset len := return (← read).calldata.readWithPadding offset len
  codeRead offset len := return (← read).code.readWithPadding offset len
  returnDataRead offset len := do
    let data := (← get).returnData
    if offset + len > data.size then Fe.M.fail .oob else return data.extract offset (offset + len)
  ctx
    | .address => return (← selfAddress).toNat
    | .caller => return (← caller).toNat
    | .callValue => return (← callvalue).toNat
    | .origin => return (← origin).toNat
    | .gasPrice => return (← gasprice).toNat
    | .coinBase => return (← coinbase).toNat
    | .timestamp => return (← timestamp).toNat
    | .number => return (← blockNumber).toNat
    | .prevRandao => return (← prevrandao).toNat
    | .gasLimit => return (← gaslimit).toNat
    | .chainId => return (← chainid).toNat
    | .baseFee => return (← basefee).toNat
    | .selfBalance => return (← selfbalance).toNat
    | .blobBaseFee => return (← blobbasefee).toNat
    | .gas => return (← gas).toNat
    | .callDataSize => return (← calldatasize).toNat
    | .codeSize => return (← codesize).toNat
    | .returnDataSize => return (← returndatasize).toNat
    | .msize => return ((← get).memory.size + 31) / 32 * 32
    | .currentCodeRegionLen => pure regionLen
  balance addr := return (← balance (.ofNat addr)).toNat
  blockHash number := return (← blockhash (.ofNat number)).toNat
  blobHash index := return (← blobhash (.ofNat index)).toNat
  extCodeSize addr := return (← extcodesize (.ofNat addr)).toNat
  extCodeHash addr := return (← extcodehash (.ofNat addr)).toNat
  keccak256 bytes := pure (fromByteArrayBigEndian (KEC bytes))
  log topics data := emit (topics.map .ofNat) data
  extCodeRead addr offset len := do
    let code := (← get).accounts.get? (AccountAddress.ofUInt256 (.ofNat addr))
      |>.option ByteArray.empty (·.code)
    return code.readWithPadding offset len
  messageCall kind args := do
    let w := args.map UInt256.ofNat
    match kind, w with
    | .call, #[g, a, v, ap, al, rp, rl] => return some (← call g a v ap al rp rl).toNat
    | .staticCall, #[g, a, ap, al, rp, rl] | .staticCallPrecompile, #[g, a, ap, al, rp, rl] =>
      return some (← staticcall g a ap al rp rl).toNat
    | .delegateCall, #[g, a, ap, al, rp, rl] => return some (← delegatecall g a ap al rp rl).toNat
    | _, _ => return none
  createAccount kind args := do
    match kind, args.map UInt256.ofNat with
    | .create, #[v, p, l] => return some (← create v p l).toNat
    | .create2, #[v, p, l, salt] => return some (← create2 v p l salt).toNat
    | _, _ => return none
  -- `Calls.lean`'s `selfdestruct` halts; exported code never self-destructs.
  selfDestruct _ := return none
  initCodeRegion name := do
    match creations.find? (·.1 == name) with
    | none => return none
    | some (_, creation) =>
      return some ((← initCodeOffset creation).toNat, (← initCodeLen creation).toNat)

/-- An interpreter run in the model monad, from reserved memory, each call of the entry code
    bounded by `fuel` steps: what it returns, or the error the specification gives up with. -/
def interp {α : Type} (fuel : Nat) (m : Fe.Sem.InterpM Env World α) :
    FeM (Except Fe.Sem.SpecError α) := do
  reserve
  return (← (m.run { fuel := some fuel }).run).map (·.1)

/-- The runtime entry of `prog`, whose runtime code is `regionLen` bytes. -/
def specRuntime (prog : Fe.IR.Program) (regionLen : Nat) (creations : List (String × ByteArray))
    (fuel : Nat) : FeM (Except Fe.Sem.SpecError Empty) :=
  interp fuel (Fe.Sem.runtime prog (specHost regionLen creations))

/-- The deployment entry of `prog`, whose creation code is `regionLen` bytes: the bytes of the
    immutable fields. -/
def specInit (prog : Fe.IR.Program) (regionLen : Nat) (creations : List (String × ByteArray))
    (fuel : Nat) : FeM (Except Fe.Sem.SpecError ByteArray) :=
  interp fuel (Fe.Sem.initEntry prog (specHost regionLen creations))

end Fe.EVM
