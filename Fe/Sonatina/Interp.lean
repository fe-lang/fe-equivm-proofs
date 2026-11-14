import Fe.Sonatina.Syntax
import Fe.EVM.Calls
import Fe.EVM.Refine

/-!
# An interpreter of Sonatina IR

`runFunc` runs a function of a module in the model monad `FeM`, over EVMLean's state: storage,
memory, calldata, logs, return data and message calls are the model library's own primitives
(`Fe/EVM/World.lean`, `Calls.lean`), so a run of the IR is compared with the bytecode as an
exported model is.  `Sidecar.model` is the contract model of an object: its `init` and
`runtime` sections, each run from its entry function.

The interpreter is fuel-bounded: each function call and each block entered takes one unit of
its own budget, and a run out of fuel does not terminate.  So does a run that reaches what the
semantics leaves undefined or this subset does not cover (`stuck`): an ill-typed operand, a
missing block, `unreachable`, a section entry that returns.  A run that does not terminate
agrees with no result of the bytecode, so a gap in the semantics makes a comparison fail, not
pass.

What the semantics fixes where Sonatina leaves a choice:
- `undef` and a struct field never written read as zero; a division by zero gives zero.
- `evm_malloc` gives fresh zero bytes at the end of memory, where `alloc` of the model library
  puts them.  The bytecode places allocations elsewhere; only return data, logs and accounts
  are compared, so the addresses do not matter unless the program makes them observable.
- `sym_addr` and `sym_size` read the symbol table of the compiled section, a fact of the
  layout the IR does not fix.
-/

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-- A value: an integer of `bits` bits, below `2 ^ bits`, or the fields of a struct. -/
inductive Val where
  | int (bits value : Nat)
  | agg (fields : List Val)
  deriving Repr, BEq, Inhabited

/-- The values a function has defined. -/
abbrev Env := Std.HashMap Nat Val

/-- How an instruction runs a callee: from its name and arguments to its results. -/
abbrev Callee := String → List Val → FeM (List Val)

/-- The offset and size of each symbol of the running section. -/
abbrev Symbols := String → Option (Nat × Nat)

/-- A run past what the semantics defines: it does not terminate. -/
def stuck {α : Type} : FeM α := Fe.M.diverge

/-- `n` modulo `2 ^ bits`. -/
def wrap (bits : Nat) (n : Int) : Nat := (n % (2 ^ bits : Int)).toNat

/-- The two's complement integer of a value of `bits` bits. -/
def signed (bits value : Nat) : Int :=
  if value < 2 ^ (bits - 1) then value else (value : Int) - 2 ^ bits

/-- `n` is a signed integer of `bits` bits. -/
def fitsSigned (bits : Nat) (n : Int) : Bool := -(2 ^ (bits - 1) : Int) ≤ n && n < 2 ^ (bits - 1)

def word (v : UInt256) : Val := .int 256 v.toNat

def bool (b : Bool) : Val := .int 1 (if b then 1 else 0)

def Val.zero : Ty → Val
  | .int bits => .int bits 0
  | .ptr _ => .int 256 0
  | .struct _ | .array _ _ | .unit => .agg []

def evalOperand (env : Env) : Operand → FeM Val
  | .var id => match env[id]? with
    | some v => pure v
    | none => stuck
  | .imm bits value => pure (.int bits value)
  | .undef ty => pure (Val.zero ty)

/-- An integer operand. -/
def evalInt (env : Env) (o : Operand) : FeM (Nat × Nat) := do
  match ← evalOperand env o with
  | .int bits value => pure (bits, value)
  | .agg _ => stuck

/-- An operand as an EVM word. -/
def evalWord (env : Env) (o : Operand) : FeM UInt256 := do
  return UInt256.ofNat (← evalInt env o).2

/-- Two integer operands of one width. -/
def evalPair (env : Env) (a b : Operand) : FeM (Nat × Nat × Nat) := do
  let (bits, x) ← evalInt env a
  let (bits', y) ← evalInt env b
  if bits == bits' then pure (bits, x, y) else stuck

def BinOp.eval (op : BinOp) (bits x y : Nat) : Nat :=
  let sx := signed bits x
  let sy := signed bits y
  let w := fun (a b : Nat) (f : UInt256 → UInt256 → UInt256) =>
    (f (UInt256.ofNat a) (UInt256.ofNat b)).toNat
  match op with
  | .add => wrap bits (x + y)
  | .sub => wrap bits (x - y : Int)
  | .mul => wrap bits (x * y)
  | .udiv | .evmUdiv => if y = 0 then 0 else x / y
  | .sdiv | .evmSdiv => if y = 0 then 0 else wrap bits (sx.tdiv sy)
  | .umod | .evmUmod => if y = 0 then 0 else x % y
  | .smod | .evmSmod => if y = 0 then 0 else wrap bits (sx.tmod sy)
  -- The shifts take the amount first.
  | .shl => if x ≥ bits then 0 else wrap bits (y <<< x)
  | .shr => if x ≥ bits then 0 else y >>> x
  | .sar => if x ≥ bits then (if sy < 0 then 2 ^ bits - 1 else 0) else wrap bits (sy / 2 ^ x)
  | .and => x &&& y
  | .or => x ||| y
  | .xor => x ^^^ y
  | .evmExp => w x y UInt256.exp
  | .evmByte => w x y UInt256.byteAt
  | .evmSignExtend => w x y UInt256.signextend

def CmpOp.eval (op : CmpOp) (bits x y : Nat) : Bool :=
  match op with
  | .lt => x < y
  | .gt => x > y
  | .le => x ≤ y
  | .ge => x ≥ y
  | .slt => signed bits x < signed bits y
  | .sgt => signed bits x > signed bits y
  | .sle => signed bits x ≤ signed bits y
  | .sge => signed bits x ≥ signed bits y
  | .eq => x == y
  | .ne => x != y

/-- The wrapped result and whether it wrapped. -/
def OvfOp.eval (op : OvfOp) (bits x y : Nat) : Nat × Bool :=
  let sx := signed bits x
  let sy := signed bits y
  match op with
  | .uaddo => (wrap bits (x + y), x + y ≥ 2 ^ bits)
  | .usubo => (wrap bits (x - y : Int), x < y)
  | .umulo => (wrap bits (x * y), x * y ≥ 2 ^ bits)
  | .saddo => (wrap bits (sx + sy), !fitsSigned bits (sx + sy))
  | .ssubo => (wrap bits (sx - sy), !fitsSigned bits (sx - sy))
  | .smulo => (wrap bits (sx * sy), !fitsSigned bits (sx * sy))

def CastOp.eval (op : CastOp) (bits x bits' : Nat) : Nat :=
  match op with
  | .sext => wrap bits' (signed bits x)
  | .zext | .trunc | .ptrToInt | .intToPtr | .bitcast => wrap bits' x

/-- An EVM instruction on its operands: the value it gives, if any. -/
def EvmOp.run (op : EvmOp) (args : List UInt256) : FeM (List Val) :=
  let one (m : FeM UInt256) : FeM (List Val) := do return [word (← m)]
  let none' (m : FeM Unit) : FeM (List Val) := do m; return []
  match op, args with
  | .address, [] => one Fe.EVM.selfAddress
  | .balance, [a] => one (Fe.EVM.balance a)
  | .origin, [] => one Fe.EVM.origin
  | .caller, [] => one Fe.EVM.caller
  | .callValue, [] => one Fe.EVM.callvalue
  | .calldataLoad, [o] => one (Fe.EVM.calldataload o)
  | .calldataSize, [] => one Fe.EVM.calldatasize
  | .calldataCopy, [d, o, l] => none' (Fe.EVM.calldatacopy d o l)
  | .codeSize, [] => one Fe.EVM.codesize
  | .codeCopy, [d, o, l] => none' (Fe.EVM.codecopy d o l)
  | .gasPrice, [] => one Fe.EVM.gasprice
  | .extCodeSize, [a] => one (Fe.EVM.extcodesize a)
  | .extCodeHash, [a] => one (Fe.EVM.extcodehash a)
  | .extCodeCopy, [a, d, o, l] => none' (Fe.EVM.extcodecopy a d o l)
  | .returnDataSize, [] => one Fe.EVM.returndatasize
  | .returnDataCopy, [d, o, l] => none' (Fe.EVM.returndatacopy d o l)
  | .blockHash, [n] => one (Fe.EVM.blockhash n)
  | .coinbase, [] => one Fe.EVM.coinbase
  | .timestamp, [] => one Fe.EVM.timestamp
  | .number, [] => one Fe.EVM.blockNumber
  | .prevRandao, [] => one Fe.EVM.prevrandao
  | .gasLimit, [] => one Fe.EVM.gaslimit
  | .chainId, [] => one Fe.EVM.chainid
  | .selfBalance, [] => one Fe.EVM.selfbalance
  | .baseFee, [] => one Fe.EVM.basefee
  | .blobHash, [i] => one (Fe.EVM.blobhash i)
  | .blobBaseFee, [] => one Fe.EVM.blobbasefee
  | .gas, [] => one Fe.EVM.gas
  | .codeLoad, [o] => one (Fe.EVM.cload o)
  | .sload, [k] => one (Fe.EVM.sload k)
  | .sstore, [k, v] => none' (Fe.EVM.sstore k v)
  | .tload, [k] => one (Fe.EVM.tload k)
  | .tstore, [k, v] => none' (Fe.EVM.tstore k v)
  | .keccak256, [p, l] => one (Fe.EVM.keccak256 p l)
  | .mcopy, [d, s, l] => none' (Fe.EVM.mcopy d s l)
  | .mstore8, [p, v] => none' (Fe.EVM.mstore8 p v)
  | .log _, p :: l :: topics => none' (Fe.EVM.logData p l topics.toArray)
  | .create, [v, p, l] => one (Fe.EVM.create v p l)
  | .create2, [v, p, l, s] => one (Fe.EVM.create2 v p l s)
  | .call, [g, a, v, ap, al, rp, rl] => one (Fe.EVM.call g a v ap al rp rl)
  | .staticCall, [g, a, ap, al, rp, rl] => one (Fe.EVM.staticcall g a ap al rp rl)
  | .delegateCall, [g, a, ap, al, rp, rl] => one (Fe.EVM.delegatecall g a ap al rp rl)
  | .addMod, [a, b, m] => pure [word (UInt256.addMod a b m)]
  | .mulMod, [a, b, m] => pure [word (UInt256.mulMod a b m)]
  | _, _ => stuck

/-- The hash of words, each as 32 big-endian bytes. -/
def keccakOfWords (words : List UInt256) : UInt256 :=
  .ofNat (fromByteArrayBigEndian (KEC (words.foldl (fun b w => b ++ w.toByteArray) .empty)))

/-- Run an instruction to the values it defines.  `call` runs a callee, `symbol` reads the
    symbol table of the running section. -/
def runInst (call : Callee) (symbol : Symbols) (env : Env) : Inst → FeM (List Val)
  | .bin op a b => do
    let (bits, x, y) ← evalPair env a b
    return [.int bits (op.eval bits x y)]
  | .cmp op a b => do
    let (bits, x, y) ← evalPair env a b
    return [bool (op.eval bits x y)]
  | .isZero a => do return [bool ((← evalInt env a).2 == 0)]
  | .not a => do
    let (bits, x) ← evalInt env a
    return [.int bits (2 ^ bits - 1 - x)]
  | .neg a => do
    let (bits, x) ← evalInt env a
    return [.int bits (wrap bits (-(x : Int)))]
  | .clz a => do
    let (bits, x) ← evalInt env a
    let top := (List.range bits).reverse.find? x.testBit
    return [.int bits (top.elim bits fun i => bits - 1 - i)]
  | .ctz a => do
    let (bits, x) ← evalInt env a
    return [.int bits (((List.range bits).find? x.testBit).getD bits)]
  | .ovf op a b => do
    let (bits, x, y) ← evalPair env a b
    let (r, o) := op.eval bits x y
    return [.int bits r, bool o]
  | .cast op a ty => do
    let (bits, x) ← evalInt env a
    return [.int ty.bits (op.eval bits x ty.bits)]
  | .select c a b => do
    let (_, c) ← evalInt env c
    return [← evalOperand env (if c != 0 then a else b)]
  | .evm op args => do op.run (← args.mapM (evalWord env))
  | .mload addr ty => do
    unless ty.bits == 256 do stuck
    return [word (← mload (← evalWord env addr))]
  | .mstore addr value ty => do
    unless ty.bits == 256 do stuck
    mstore (← evalWord env addr) (← evalWord env value)
    return []
  | .memzero dest len => do
    zeroMem (← evalWord env dest) (← evalWord env len)
    return []
  | .malloc size => do return [word (← alloc (← evalWord env size))]
  | .symAddr s => do
    let some (offset, _) := symbol s | stuck
    return [.int 256 offset]
  | .symSize s => do
    let some (_, size) := symbol s | stuck
    return [.int 256 size]
  | .insertValue agg index value => do
    let .agg fields ← evalOperand env agg | stuck
    let (_, i) ← evalInt env index
    let v ← evalOperand env value
    let fields := fields ++ List.replicate (i + 1 - fields.length) (.int 256 0)
    return [.agg (fields.set i v)]
  | .extractValue agg index => do
    let .agg fields ← evalOperand env agg | stuck
    let (_, i) ← evalInt env index
    return [fields.getD i (.int 256 0)]
  | .keccakWords words => do return [word (keccakOfWords (← words.mapM (evalWord env)))]
  | .call callee args => do call callee (← args.mapM (evalOperand env))

/-- Bind each value to its id. -/
def bind (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) : FeM Env :=
  if dsts.length == vals.length then
    pure ((dsts.zip vals).foldl (fun env ((id, _), v) => env.insert id v) env)
  else stuck

/-- Enter block `b` from block `prev`: each phi takes, at once, its operand for `prev`. -/
def enter (env : Env) (prev : Option Nat) (b : Block) : FeM Env := do
  let vals ← b.phis.mapM fun phi => do
    let some p := prev | stuck
    let some (o, _) := phi.incoming.find? (·.2 == p) | stuck
    evalOperand env o
  bind env (b.phis.map fun phi => (phi.dst, phi.ty)) vals

/-- Run `f` from block `id`, entered from `prev`, for at most `fuel` blocks. -/
def runBlocks (call : Callee) (symbol : Symbols) (f : Func) :
    Nat → Env → Option Nat → Nat → FeM (List Val)
  | 0, _, _, _ => stuck
  | fuel + 1, env, prev, id => do
    let some b := f.block? id | stuck
    let env ← enter env prev b
    let env ← b.body.foldlM (init := env) fun env s => do
      bind env s.dsts (← runInst call symbol env s.inst)
    match b.term with
    | .jump dest => runBlocks call symbol f fuel env (some id) dest
    | .br c nz z => do
      let (_, c) ← evalInt env c
      runBlocks call symbol f fuel env (some id) (if c != 0 then nz else z)
    | .brTable s default cases => do
      let v ← evalOperand env s
      let vals ← cases.mapM fun (o, dest) => return (← evalOperand env o, dest)
      match (vals.find? (·.1 == v)).map (·.2) <|> default with
      | some dest => runBlocks call symbol f fuel env (some id) dest
      | none => stuck
    | .ret values => values.mapM (evalOperand env)
    | .evmReturn a l => do
      let e ← returnData (← evalWord env a) (← evalWord env l)
      nomatch e
    | .evmRevert a l => do
      let e ← revertData (← evalWord env a) (← evalWord env l)
      nomatch e
    | .evmStop => do
      let e ← stopCall
      nomatch e
    | .evmInvalid => do
      let e ← trap
      nomatch e
    | .unreachable => stuck

/-- Run function `name` of `m` on `args`: at most `fuel` calls deep, each running at most `fuel`
    blocks. -/
def runFunc (m : Module) (symbol : Symbols) : Nat → Callee
  | 0, _, _ => stuck
  | fuel + 1, name, args => do
    let some f := m.func? name | stuck
    let some entry := f.blocks.head? | stuck
    let env ← bind {} f.params args
    runBlocks (fun g vs => runFunc m symbol fuel g vs) symbol f fuel env none entry.id

/-- The fuel a section runs with. -/
def defaultFuel : Nat := 1000000

/-- Run section `name` of the sidecar's object from its entry.  The entry ends the call itself:
    one that returns is stuck. -/
def Sidecar.runSection (s : Sidecar) (name : String) (fuel : Nat := defaultFuel) :
    FeM ByteArray := do
  let some obj := s.module.objects.find? (·.name == s.object) | stuck
  let some sec := obj.sections.find? (·.name == name) | stuck
  let some code := s.section? name | stuck
  let _ ← runFunc s.module (fun sym => code.symbols.lookup sym) fuel sec.entry []
  stuck

/-- The contract model the IR gives.  The constructor reads its arguments from the running
    code, as the init section does, and ends with the whole deployed code. -/
def Sidecar.model (s : Sidecar) (fuel : Nat := defaultFuel) : ContractModel where
  init _ := s.runSection "init" fuel
  runtime := s.runSection "runtime" fuel

end Fe.Sonatina
