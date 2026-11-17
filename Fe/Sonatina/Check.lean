import Fe.Sonatina.Hints
import Fe.Sonatina.Decode
import Fe.Sonatina.Plan

/-!
# Checking bytes against the machine IR

`checkWith plan s` decides that each section of the sidecar `s` is emitted from its machine IR
with the stores of the spill plan (`Func.instrument`), for the class of sections the checker
covers: memory spills but no frame spills, no dynamic frames, no dynamic stack pointer, no call
preserves, every value and immediate a word (as the EVM computes on words), and only the
instructions `pureWith`, `eventWith` and `exitOf` translate, and internal calls.  `check` and
`checkSpills` (`FrameSafe.lean`) are its instances for no plan and the walked plan.  The hints
and the plan are inputs: a wrong one makes the checker reject.

Memory spills: the spill stores are events like any other; the path knows words of memory
(`Path.held`), which a constant `MSTORE` writes and each statement keeps where its guard
protects them or the store does not meet them; a bytes `MLOAD` of a known word that is not the
IR's next event is a reload, of a value the plan has reload-live there; a block starts knowing the
words of its spilled values reload-live at its entry, and every arrival must know them.

A section may have several functions; each is checked block by block.  A function returns if
its entry block reaches a `ret` (`returning`).  Its return address is a value no value of the
function is (`Func.fresh`), at the bottom of the entry stack of every block it may return from,
whose entry stacks are then the whole of its frame (`Frame.exact`); its entry block is entered
with its arguments on top of it.  A call is a `JUMP` to the callee's entry block with its
arguments on top, and, if the callee returns, below them the address of a `JUMPDEST` where the
block's bytes go on with the callee's results on top; a call to a function that does not
return ends the block, whose terminator is `unreachable`.  A `ret` is a `JUMP` to the return
address with exactly the values below it.  The section's entry takes no arguments, returns
nowhere, and no block calls it.

The machine IR is the specification, so the checker also makes sure its run never gets stuck
where the bytes go on: each value is defined once, each read reads a value defined before it
(the block's entry stack, its phis, or an earlier statement of the block: `defined`), each
successor's phis have an operand from the block, a pure instruction defines one value, the
entry function takes no parameters and its entry block has no phis and no predecessor.  A block
may go to a successor whose code starts at its own offset, which the bytes reach in no step,
only down a chain that ends (`zeroRank`).

For each machine block `B`, it runs two symbolic executions into one language of words:
- the machine IR's instructions of `B`, as expressions over its values by value numbering
  (`Canon`): a pure value of `B` is the first value of `B` with the same operation on the same
  expressions, or a constant, and every other value is itself, so an expression is an
  operation on values and constants, however long the chain of operations it stands for;
- the bytes from `B`'s offset, starting from `B`'s planned entry stack: `PUSH`, `DUP`, `SWAP`,
  `POP` and `JUMPDEST` move expressions, a pure opcode builds one, named by the value of `B`
  with that operation if there is one (`Canon.intern`), every read or write of state
  must be the IR's next event with equal operands, and every jump either leaves for the
  successor the IR's terminator selects, with that successor's entry stack on top (its phis
  replaced by their operands from `B`), or continues in other code (an outlined unit).
A conditional jump splits the run: its condition must be the IR's branch condition, its
negation, or the comparison of a `br_table` scrutinee with a case.

The section entry's code stores the initial free pointer before the machine IR's first
instruction; the checker expects it as the entry block's first event, as the interpreter does
it before the entry function.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

/-- A word both the bytes and the machine IR compute: a value that is not pure, a constant, or
    a pure EVM operation of at most three words, its operands in stack order (top first). -/
inductive Expr where
  | atom (id : Nat)
  | const (value : Nat)
  | op0 (op : Operation)
  | op1 (op : Operation) (a : Expr)
  | op2 (op : Operation) (a b : Expr)
  | op3 (op : Operation) (a b c : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- An operation the bytes do on state, in the order of the IR's: its opcode, operands in stack
    order, and for a read the IR value it defines. -/
structure Event where
  op : Operation
  args : List Expr
  result : Option Nat
  /-- The words its statement must leave as they were: the statement's own words of the guard
      the instrumented model runs it under (`SpillPlan.guard`). -/
  keep : List Nat := []
  /-- Where its statement is in the block. -/
  pos : Nat := 0
  /-- The spilled value it stores at its word, if it is a spill store (`storedValue`). -/
  stores : Option Nat := none
  deriving DecidableEq, Repr

/-- The pure opcodes, which compute a word from their operands and the frame's environment. -/
def pureOps : List Operation :=
  [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT,
   .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .ADDRESS, .ORIGIN,
   .CALLER, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CODESIZE, .CHAINID, .TIMESTAMP, .NUMBER,
   .GASLIMIT, .BASEFEE, .COINBASE, .PREVRANDAO, .BLOCKHASH]

/-- The opcodes that read state: their result is an event's.  `GAS` reads the gas left, which
    the model takes from its feed; a message call's result is its success word, a creation's the
    new contract's address or zero. -/
def readOps : List Operation :=
  [.SLOAD, .MLOAD, .KECCAK256, .SELFBALANCE, .BALANCE, .EXTCODESIZE, .RETURNDATASIZE, .GAS, .CALL,
   .STATICCALL, .DELEGATECALL, .CREATE, .CREATE2, .TLOAD, .CLZ]

/-- The message calls and creations the checker matches: an event each, its result the success
    word or the new address. -/
def messageOps : List Operation := [.CALL, .STATICCALL, .DELEGATECALL, .CREATE, .CREATE2]

/-- The opcodes that write state. -/
def writeOps : List Operation :=
  [.SSTORE, .MSTORE, .MSTORE8, .CODECOPY, .CALLDATACOPY, .MCOPY, .LOG0, .LOG1, .LOG2, .LOG3,
   .LOG4, .RETURNDATACOPY, .TSTORE]

/-- The halting opcodes, with the operands they take. -/
def haltOps : List Operation := [.RETURN, .REVERT, .STOP, .INVALID]

/-- A pure arithmetic or logic opcode on words, operands top first, as `Xstep` computes it;
    `none` for `EXP`, which the checker does not fold, and the opcodes of the environment. -/
def evalOp : Operation → List UInt256 → Option UInt256
  | .ADD, [a, b] => some (a + b)
  | .SUB, [a, b] => some (UInt256.sub a b)
  | .MUL, [a, b] => some (UInt256.mul a b)
  | .DIV, [a, b] => some (UInt256.div a b)
  | .SDIV, [a, b] => some (UInt256.sdiv a b)
  | .MOD, [a, b] => some (UInt256.mod a b)
  | .SMOD, [a, b] => some (UInt256.smod a b)
  | .SIGNEXTEND, [a, b] => some (UInt256.signextend a b)
  | .ADDMOD, [a, b, c] => some (UInt256.addMod a b c)
  | .MULMOD, [a, b, c] => some (UInt256.mulMod a b c)
  | .SHL, [a, b] => some (UInt256.shiftLeft b a)
  | .SHR, [a, b] => some (UInt256.shiftRight b a)
  | .SAR, [a, b] => some (UInt256.sar a b)
  | .AND, [a, b] => some (UInt256.land a b)
  | .OR, [a, b] => some (UInt256.lor a b)
  | .XOR, [a, b] => some (UInt256.xor a b)
  | .LT, [a, b] => some (UInt256.lt a b)
  | .GT, [a, b] => some (UInt256.gt a b)
  | .SLT, [a, b] => some (UInt256.slt a b)
  | .SGT, [a, b] => some (UInt256.sgt a b)
  | .EQ, [a, b] => some (UInt256.eq a b)
  | .BYTE, [a, b] => some (UInt256.byteAt a b)
  | .ISZERO, [a] => some (UInt256.isZero a)
  | .NOT, [a] => some (UInt256.lnot a)
  | _, _ => none

/-- The word of a constant. -/
def constWord : Expr → Option UInt256
  | .const v => some (UInt256.ofNat v)
  | _ => none

/-- The constant an operation on constants gives, if it is arithmetic or logic. -/
def foldConst (op : Operation) (args : List Expr) : Option Expr := do
  return .const (← evalOp op (← args.mapM constWord)).toNat

/-- The rank of an expression's constructor, constants lowest. -/
def Expr.rank : Expr → Nat
  | .const _ => 0 | .atom _ => 1 | .op0 _ => 2 | .op1 .. => 3 | .op2 .. => 4 | .op3 .. => 5

/-- A total order on expressions, which orders the operands of a commutative operation. -/
def Expr.cmp : Expr → Expr → Ordering
  | .const a, .const b | .atom a, .atom b => compare a b
  | .op0 o, .op0 p => compare (serializeInstr o).toNat (serializeInstr p).toNat
  | .op1 o a, .op1 p a' => (compare (serializeInstr o).toNat (serializeInstr p).toNat).then
      (a.cmp a')
  | .op2 o a b, .op2 p a' b' => (compare (serializeInstr o).toNat (serializeInstr p).toNat).then
      ((a.cmp a').then (b.cmp b'))
  | .op3 o a b c, .op3 p a' b' c' =>
    (compare (serializeInstr o).toNat (serializeInstr p).toNat).then
      ((a.cmp a').then ((b.cmp b').then (c.cmp c')))
  | a, b => compare a.rank b.rank

/-- The commutative opcodes. -/
def commutative : List Operation := [.ADD, .MUL, .AND, .OR, .XOR, .EQ]

/-- An operation on two operands in one form: `GT` and `SGT` as `LT` and `SLT` on swapped
    operands, a commutative operation with the greater operand on top. -/
def normalize (op : Operation) (a b : Expr) : Expr :=
  if op == .GT then .op2 .LT b a
  else if op == .SGT then .op2 .SLT b a
  else if commutative.contains op && a.cmp b == .lt then .op2 op b a
  else .op2 op a b

/-- An operation on one operand in one form: three `ISZERO`s as one. -/
def unary : Operation → Expr → Expr
  | .ISZERO, .op1 .ISZERO (.op1 .ISZERO a) => .op1 .ISZERO a
  | op, a => .op1 op a

/-- An expression of an operation on operands, top first; on constants an arithmetic or logic
    operation is its result, as the bytes compute a constant the IR writes as one. -/
def mkOp (op : Operation) : List Expr → Option Expr
  | [] => some (.op0 op)
  | [a] => some ((foldConst op [a]).getD (unary op a))
  | [a, b] => some ((foldConst op [a, b]).getD (normalize op a b))
  | [a, b, c] => some (.op3 op a b c)
  | _ => none

/-- The opcode of a pure machine instruction. -/
def binOpcode : BinOp → Option Operation
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .shl => some .SHL
  | .shr => some .SHR | .sar => some .SAR | .and => some .AND | .or => some .OR
  | .xor => some .XOR | .evmUdiv => some .DIV | .evmSdiv => some .SDIV | .evmUmod => some .MOD
  | .evmSmod => some .SMOD | .evmExp => some .EXP | .evmByte => some .BYTE
  | .evmSignExtend => some .SIGNEXTEND
  | _ => none

def cmpOpcode : CmpOp → Option Operation
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT | .eq => some .EQ
  | _ => none

/-- The pure EVM instructions of the machine IR. -/
def evmPureOpcode : EvmOp → Option Operation
  | .address => some .ADDRESS | .origin => some .ORIGIN | .caller => some .CALLER
  | .callValue => some .CALLVALUE | .calldataLoad => some .CALLDATALOAD
  | .calldataSize => some .CALLDATASIZE | .codeSize => some .CODESIZE
  | .chainId => some .CHAINID | .timestamp => some .TIMESTAMP | .number => some .NUMBER
  | .gasLimit => some .GASLIMIT | .baseFee => some .BASEFEE | .coinbase => some .COINBASE
  | .prevRandao => some .PREVRANDAO | .blockHash => some .BLOCKHASH
  | .addMod => some .ADDMOD | .mulMod => some .MULMOD
  | _ => none

/-- The EVM instructions of the machine IR that read or write state. -/
def evmEventOpcode : EvmOp → Option Operation
  | .sload => some .SLOAD | .mload => some .MLOAD | .keccak256 => some .KECCAK256
  | .sstore => some .SSTORE | .mstore => some .MSTORE | .mstore8 => some .MSTORE8
  | .codeCopy => some .CODECOPY | .calldataCopy => some .CALLDATACOPY | .mcopy => some .MCOPY
  | .log 0 => some .LOG0 | .log 1 => some .LOG1 | .log 2 => some .LOG2 | .log 3 => some .LOG3
  | .log 4 => some .LOG4
  | .selfBalance => some .SELFBALANCE | .balance => some .BALANCE
  | .extCodeSize => some .EXTCODESIZE | .returnDataSize => some .RETURNDATASIZE
  | .returnDataCopy => some .RETURNDATACOPY | .gas => some .GAS
  | .tload => some .TLOAD | .tstore => some .TSTORE
  | .call => some .CALL | .staticCall => some .STATICCALL | .delegateCall => some .DELEGATECALL
  | .create => some .CREATE | .create2 => some .CREATE2
  | _ => none

/-- The instruction makes a message call or a creation the checker matches. -/
def _root_.Fe.Sonatina.Inst.messages : Inst → Bool
  | .evm .call _ | .evm .staticCall _ | .evm .delegateCall _ | .evm .create _
  | .evm .create2 _ => true
  | _ => false

/-- Some function of the module makes a message call or a creation. -/
def _root_.Fe.Sonatina.Module.hasCalls (m : Module) : Bool :=
  m.funcs.any fun f => f.blocks.any fun b => b.body.any (·.inst.messages)

/-- The machine IR of the sidecar's section `name` makes a message call or a creation. -/
def _root_.Fe.Sonatina.Sidecar.hasCalls (s : Sidecar) (name : String) : Bool :=
  match s.section? name with
  | some code => code.lowering.any (·.machine.hasCalls)
  | none => false

/-- The value a statement defines, if one, with its instruction. -/
def _root_.Fe.Sonatina.Stmt.def? (s : Stmt) : Option (Nat × Inst) :=
  match s.dsts with
  | [(id, _)] => some (id, s.inst)
  | _ => none

/-- A function another can call: where its code starts, how many arguments it takes and values
    it returns, and whether it returns at all. -/
structure Callee where
  offset : Nat
  params : Nat
  rets : Nat
  returns : Bool

/-- What the checker knows of the function a block is in: the value that stands for its return
    address, whether it returns (it has one only then), the blocks from which it may return,
    whose entry stacks are the whole of its frame, and the functions it may call. -/
structure Frame where
  retId : Nat
  returns : Bool
  exact : Nat → Bool
  callee : String → Option Callee

/-- The planned entry stack of a block, top first: where the function cannot return from the
    block, the lowering record keeps the return address at the bottom of the frame, below slots
    it does not list, and the checker leaves it out. -/
def Frame.slots (fr : Frame) (hint : BlockHint) : List Slot :=
  if fr.exact hint.block then hint.entryStack else hint.entryStack.filter (· != .funcReturn)

/-- The expressions of a block's values by value numbering (`Canon.ofDefs`): `vals` the
    expression of each value the block defines, `nodes` the value each operation names. -/
structure Canon where
  vals : List (Nat × Expr)
  nodes : List (Expr × Nat)

/-- What the checker knows of a function's memory spills: the plan's spilled values and their
    words, the values reload-live at each point (`Func.reloadLive`), the words each statement of
    each block must leave as they were (the instrumented model's guard, `SpillPlan.guard`), and
    the function's entry block. -/
structure FuncSpill where
  words : List (Nat × Nat)
  live : Live
  guard : Nat → List (List Nat)
  entry : Nat

/-- The spilled values block `S` starts with in memory, each with its word: those reload-live at
    its entry, at a word below `2 ^ 32`; none at the function's entry. -/
def FuncSpill.spillIn (sp : FuncSpill) (S : Nat) : List (Nat × Nat) :=
  if S == sp.entry then [] else (sp.live.at S 0).filterMap fun v =>
    (sp.words.lookup v).bind fun a => if a < 2 ^ 32 then some (v, a) else none

/-- What the checker knows of a machine block: its function, the statement defining each
    value of the block, the section's symbols, the function's frame, and the expressions of
    the block's values, `Canon.ofDefs symbols defs`. -/
structure Ctx where
  func : Func
  defs : List (Nat × Inst)
  symbols : List (String × Nat × Nat)
  frame : Frame
  canon : Canon
  /-- The block, and what the checker knows of its function's spills. -/
  block : Block
  spill : FuncSpill

/-- The value a statement defines purely or by an event, if one: a call's results are atoms. -/
def _root_.Fe.Sonatina.Stmt.local? (s : Stmt) : Option (Nat × Inst) :=
  if s.inst matches .call _ _ then none else s.def?

/-- The expression of an operand, given that of a value; an immediate must be a word. -/
def operandWith (expand : Nat → Option Expr) : Operand → Option Expr
  | .var id => expand id
  | .imm bits value => if bits == 256 && value < UInt256.size then some (.const value) else none
  | .undef _ => none

/-- The expression of a pure instruction. -/
def pureWith (expand : Nat → Option Expr) (symbols : List (String × Nat × Nat)) :
    Inst → Option Expr
  | .bin op a b => do mkOp (← binOpcode op) [← operandWith expand a, ← operandWith expand b]
  | .cmp op a b => do mkOp (← cmpOpcode op) [← operandWith expand a, ← operandWith expand b]
  | .isZero a => do mkOp .ISZERO [← operandWith expand a]
  | .not a => do mkOp .NOT [← operandWith expand a]
  | .evm op args => do mkOp (← evmPureOpcode op) (← args.mapM (operandWith expand))
  | .symAddr s => do return .const (← symbols.lookup s).1
  | .symSize s => do return .const (← symbols.lookup s).2
  | _ => none

/-- The event of an instruction that reads or writes state. -/
def eventWith (expand : Nat → Option Expr) : Inst → Option (Operation × List Expr)
  | .evm op args => do return (← evmEventOpcode op, ← args.mapM (operandWith expand))
  | .clz a => do return (.CLZ, [← operandWith expand a])
  | _ => none

/-- The expression of a value: the block's for one the block defines, else the value itself. -/
def Canon.expand (k : Canon) (id : Nat) : Option Expr := some ((k.vals.lookup id).getD (.atom id))

/-- An operation, as the value of the block it names if there is one. -/
def Canon.intern (k : Canon) (e : Expr) : Expr := ((k.nodes.lookup e).map .atom).getD e

/-- An expression a value is numbered by: an operation, but not `ISZERO`, whose operand stays
    in sight, as the bytes write the IR's `is_zero` of a boolean as three (`unary`). -/
def Expr.isOp : Expr → Bool
  | .atom _ | .const _ | .op1 .ISZERO _ => false
  | _ => true

/-- Number one more definition: a pure value is the first value with its operation on the
    same expressions (its node), or the constant the operation folds to; any other value is
    itself.  A value numbered already keeps its expression, as `List.lookup` finds a value's
    first definition. -/
def Canon.step (symbols : List (String × Nat × Nat)) (k : Canon) (d : Nat × Inst) : Canon :=
  if (k.vals.lookup d.1).isSome then k else
  match pureWith k.expand symbols d.2 with
  | none => ⟨(d.1, .atom d.1) :: k.vals, k.nodes⟩
  | some e => match k.nodes.lookup e with
    | some w => ⟨(d.1, .atom w) :: k.vals, k.nodes⟩
    | none => if e.isOp then ⟨(d.1, .atom d.1) :: k.vals, (e, d.1) :: k.nodes⟩
      else ⟨(d.1, e) :: k.vals, k.nodes⟩

/-- The expressions of the values of definitions, numbered in order. -/
def Canon.ofDefs (symbols : List (String × Nat × Nat)) (defs : List (Nat × Inst)) : Canon :=
  defs.foldl (Canon.step symbols) ⟨[], []⟩

/-- The context of block `b`: only its own values have expressions, so a value of another
    block is the word the run of the IR holds for it when `b` runs. -/
def Ctx.ofBlock (f : Func) (b : Block) (symbols : List (String × Nat × Nat)) (fr : Frame)
    (sp : FuncSpill) : Ctx :=
  let defs := b.body.filterMap Stmt.local?
  ⟨f, defs, symbols, fr, Canon.ofDefs symbols defs, b, sp⟩

def Ctx.expand (c : Ctx) : Nat → Option Expr := c.canon.expand

def Ctx.operand (c : Ctx) : Operand → Option Expr := operandWith c.expand

def Ctx.pureExpr (c : Ctx) : Inst → Option Expr := pureWith c.expand c.symbols

def Ctx.eventOf (c : Ctx) : Inst → Option (Operation × List Expr) := eventWith c.expand

/-- The event of a statement: none if it is pure, `none` itself if it is outside the class. -/
def Ctx.eventOfStmt (c : Ctx) (s : Stmt) : Option (Option Event) :=
  match c.pureExpr s.inst, c.eventOf s.inst with
  | some _, _ =>
    -- A pure instruction defines one value, an EVM one on as many operands as it pops.
    let arity := match s.inst with
      | .evm op args => (evmPureOpcode op).all fun o => δ o == some args.length
      | _ => true
    if s.dsts.length == 1 && arity then some none else none
  | none, some (op, args) =>
    -- An event pops as many operands as the IR gives it, and a read defines its word.
    if δ op != some args.length then none else
    match s.dsts, readOps.contains op with
    | [], false => some (some { op, args, result := none })
    | [(id, _)], true => some (some { op, args, result := some id })
    | _, _ => none
  | none, none => none

/-- The spilled value statement `s` of the block stores at its word, if it is a spill store. -/
def Ctx.storeOf (c : Ctx) (s : Stmt) : Option Nat :=
  (storedValue c.func c.spill.words c.block s).map (·.2)

/-- An event of statement `s` at position `k`, the guard's words `ps.headD []` its own. -/
def Ctx.annotate (c : Ctx) (ps : List (List Nat)) (k : Nat) (s : Stmt) (e : Event) : Event :=
  { e with keep := ps.headD [], pos := k, stores := c.storeOf s }

/-- The events of statements from position `k`, the guard's words of each the head of `ps`,
    in order, or `none` if a statement is outside the class: each is pure, or an event that
    defines at most one value. -/
def Ctx.events (c : Ctx) : List (List Nat) → Nat → List Stmt → Option (List Event)
  | _, _, [] => some []
  | ps, k, s :: rest => do
    let evs ← c.events ps.tail (k + 1) rest
    match ← c.eventOfStmt s with
    | some e => return c.annotate ps k s e :: evs
    | none => return evs

/-- A call of a block: the callee, its arguments' expressions, top first, the values it
    defines, and the block's events after it up to the next call. -/
structure CallSeg where
  callee : String
  args : List Expr
  dsts : List Nat
  events : List Event
  /-- The words the call must leave as they were, and where it is in the block. -/
  keep : List Nat
  pos : Nat
  deriving Repr

/-- The events of statements up to the first call, and each call with the events after it up to
    the next, or `none` if a statement is outside the class.  A call names a function of the
    section with as many arguments as it takes, and defines as many values as it returns, none
    if it does not return. -/
def Ctx.segments (c : Ctx) :
    List (List Nat) → Nat → List Stmt → Option (List Event × List CallSeg)
  | _, _, [] => some ([], [])
  | ps, k, s :: rest => do
    let (evs, calls) ← c.segments ps.tail (k + 1) rest
    match s.inst with
    | .call g args =>
      let ce ← c.frame.callee g
      let es ← args.mapM (c.operand)
      if es.length == ce.params && s.dsts.length == (if ce.returns then ce.rets else 0) then
        return ([], ⟨g, es, s.dsts.map (·.1), evs, ps.headD [], k⟩ :: calls)
      else none
    | _ =>
      match ← c.eventOfStmt s with
      | some e => return (c.annotate ps k s e :: evs, calls)
      | none => return (evs, calls)

/-- How a block ends, as the bytes must end it. -/
inductive Exit where
  /-- To a successor. -/
  | goto (succ : Nat)
  /-- A `br`: to `nz` if the condition is not zero, else to `z`. -/
  | br (cond : Expr) (nz z : Nat)
  /-- A `br_table`: to the case whose value the scrutinee equals, else to the default; the
      cases already ruled out. -/
  | table (scrutinee : Expr) (default : Nat) (cases : List (Nat × Nat)) (ruled : List Nat)
  /-- A halt by the opcode, on the operands. -/
  | halt (op : Operation) (args : List Expr)
  /-- A return to the function's return address with the values, top first. -/
  | ret (vals : List Expr)
  /-- None: the block ends in a call to a function that does not return. -/
  | unreach
  deriving Repr, Inhabited

def Ctx.exitOf (c : Ctx) : Term → Option Exit
  | .jump dest => some (.goto dest)
  | .br cond nz z => do return .br (← c.operand cond) nz z
  | .brTable s (some default) cases => do
    let cases ← cases.mapM fun (o, dest) => match o with
      | .imm 256 v => if v < UInt256.size then some (v, dest) else none
      | _ => none
    return .table (← c.operand s) default cases []
  | .evmReturn a l => do return .halt .RETURN [← c.operand a, ← c.operand l]
  | .evmRevert a l => do return .halt .REVERT [← c.operand a, ← c.operand l]
  | .evmStop => some (.halt .STOP [])
  | .evmInvalid => some (.halt .INVALID [])
  | .ret vals =>
    if c.frame.returns then do return .ret (← vals.mapM (c.operand)) else none
  | .unreachable => some .unreach
  | _ => none

/-- The expression of an entry slot. -/
def Ctx.slotExpr (c : Ctx) : Slot → Option Expr
  | .value id => c.expand id
  | .imm v => some (.const v)
  | .funcReturn => if c.frame.returns then some (.atom c.frame.retId) else none
  | .callReturn => none

/-- The planned entry stack of a block, as expressions. -/
def Ctx.entryStack (c : Ctx) (hint : BlockHint) : Option (List Expr) :=
  (c.frame.slots hint).mapM c.slotExpr

/-- What an entry slot of block `b` must be when `pred` jumps to it: a phi its operand from
    `pred`. -/
def Ctx.arrivalSlot (c : Ctx) (b : Block) (pred : Nat) : Slot → Option Expr
  | .value id =>
    match b.phis.find? (·.dst == id) with
    | some phi => do c.operand (← phi.incoming.find? (·.2 == pred)).1
    | none => c.expand id
  | .imm v => some (.const v)
  | .funcReturn => if c.frame.returns then some (.atom c.frame.retId) else none
  | .callReturn => none

/-- What the entry stack of `succ` must be when `pred` jumps to it: each phi of `succ` replaced
    by its operand from `pred`. -/
def Ctx.arrival (c : Ctx) (hints : List BlockHint) (pred succ : Nat) : Option (List Expr) := do
  let hint ← hints.find? (·.block == succ)
  let b ← c.func.block? succ
  (c.frame.slots hint).mapM (c.arrivalSlot b pred)

/-- A word of memory a path knows: its address, the expression of the word it holds, and the
    spilled value it holds if a spill store wrote it. -/
structure Held where
  word : Nat
  expr : Expr
  value : Option Nat

/-- A run of the bytes for one block, at `pc`: the events up to the next call, and the calls
    after them. -/
structure Path where
  pc : Nat
  stack : List Expr
  events : List Event
  exit : Exit
  calls : List CallSeg
  /-- The words of memory the path knows. -/
  held : List Held

/-- The position of the IR's next event or call in the block, or the terminator's. -/
def Path.gap (c : Ctx) (p : Path) : Nat :=
  match p.events, p.calls with
  | ev :: _, _ => ev.pos
  | [], cs :: _ => cs.pos
  | [], [] => c.block.body.length

/-- A bytes `MLOAD` from `p` is a reload: of a constant word, and not the IR's next event. -/
def Path.reloads (p : Path) : Bool :=
  match p.stack with
  | .const a :: _ => !(p.events.head?.any fun ev => ev.op == .MLOAD && ev.args == [.const a])
  | _ => false

/-- The words of `hs` a statement keeps: those among the words `keep` its guard protects. -/
def keepHeld (keep : List Nat) (hs : List Held) : List Held := hs.filter (keep.contains ·.word)

/-- The words the path knows after an event: those its statement keeps, and, for an `MSTORE` at
    a constant address below `2 ^ 32`, the word it writes and those it does not meet. -/
def Event.held (ev : Event) (hs : List Held) : List Held :=
  match ev.op, ev.args with
  | .MSTORE, [.const a, e] =>
    if a < 2 ^ 32 then
      ⟨a, e, ev.stores⟩ :: hs.filter fun h =>
        ev.keep.contains h.word || a + 32 ≤ h.word || h.word + 32 ≤ a
    else keepHeld ev.keep hs
  | _, _ => keepHeld ev.keep hs

/-- What the words of the spilled values `succ` starts with must hold when `pred` jumps to it:
    a phi its operand from `pred`, another value itself. -/
def Ctx.arrivalHeld (c : Ctx) (pred succ : Nat) : Option (List (Nat × Expr)) := do
  let sb ← c.func.block? succ
  (c.spill.spillIn succ).mapM fun (v, a) =>
    match sb.phis.find? (·.dst == v) with
    | some phi => do return (a, ← c.operand (← phi.incoming.find? (·.2 == pred)).1)
    | none => do return (a, ← c.expand v)

/-- The path knows, when `pred` jumps to `succ`, the words `succ` starts with. -/
def arrivesHeld (c : Ctx) (pred succ : Nat) (hs : List Held) : Bool :=
  match c.arrivalHeld pred succ with
  | some req => req.all fun (a, e) => hs.any fun h => h.word == a && h.expr == e
  | none => false

/-- The bytes' opcode at `pc`, its immediate, and the next pc, if the instruction lies in the
    code: what follows the code (a constructor's arguments) does not change it.  `tree` is the
    code's search tree, `codeTree code`, built once for a block. -/
def opAt (code : ByteArray) (tree : PcTree (Operation × Option Nat × Nat)) (pc : Nat) :
    Option (Operation × Option Nat × Nat) :=
  (tree.find pc).filter fun (_, _, next) => next ≤ code.size

/-- `true` if `t` is a valid jump destination of the code: one `D_J` finds.  `dests` is the
    code's `jumpdests code`, found once for a block. -/
def validJump (code : ByteArray) (dests : List Nat) (t : Nat) : Bool :=
  t < code.size && dests.contains t

/-- The number of the `DUP` or `SWAP`: `DUPn` copies the `n`-th item, `SWAPn` swaps the first
    with the `n + 1`-th. -/
def dupN : Operation → Option Nat
  | .Dup op => some ((serializeInstr (.Dup op)).toNat - 0x7f)
  | _ => none

def swapN : Operation → Option Nat
  | .Exchange op => some ((serializeInstr (.Exchange op)).toNat - 0x8f)
  | _ => none

/-- Arrival at `succ` from `pred` with `stack`: `succ`'s entry stack is on top, and is the
    whole of it where the function may return from `succ`, its return address at the bottom. -/
def arrives (c : Ctx) (hints : List BlockHint) (pred succ : Nat) (stack : List Expr) : Bool :=
  match c.arrival hints pred succ with
  | some expected =>
    if c.frame.exact succ then stack == expected
    else expected.length ≤ stack.length && stack.take expected.length == expected
  | none => false

/-- Where a conditional jump goes one way: to a successor of the block, on with the block's
    exit narrowed, or never, its condition a constant. -/
inductive Way where
  | succ (s : Nat)
  | exit (e : Exit)
  | never

/-- The case a condition compares the scrutinee `s` with. -/
def Expr.caseOf (s : Expr) : Expr → Option Nat
  | .op2 .EQ (.const k) s' | .op2 .EQ s' (.const k) => if s' == s then some k else none
  | _ => none

/-- What a jump's condition says of the block's exit when the jump is taken (`true`) or not:
    the successor it selects, the `br_table` with more cases ruled out, or that the jump never
    goes that way. -/
def Exit.way (e : Exit) (cond : Expr) (taken : Bool) : Option Way :=
  match e with
  | .br c nz z =>
    match c, cond with
    | .const kc, .const k =>
      if (k % UInt256.size != 0) == taken then
        some (.succ (if kc % UInt256.size != 0 then nz else z))
      else some .never
    | _, _ =>
      if cond == c then some (.succ (if taken then nz else z))
      else if cond == .op1 .ISZERO c then some (.succ (if taken then z else nz))
      else none
  | .table s default cases ruled =>
    match s.caseOf cond with
    | some k =>
      if taken then ((cases.lookup k).filter fun _ => !ruled.contains k).map .succ
      else some (.exit (.table s default cases (k :: ruled)))
    | none => none
  | _ => none

/-- The successor an exit has selected, if it has: a `goto`, or a `br_table` whose cases are
    all ruled out. -/
def Exit.selected : Exit → Option Nat
  | .goto s => some s
  | .table _ default cases ruled => if cases.all (ruled.contains ·.1) then some default else none
  | _ => none

/-- Run the bytes of block `b` from `p` for at most `fuel` steps; `true` if every path matches
    the IR.  `place` gives where the code of a block starts. -/
def run (code : ByteArray) (tree : PcTree (Operation × Option Nat × Nat)) (dests : List Nat)
    (c : Ctx) (hints : List BlockHint) (place : Nat → Option Nat)
    (b : Nat) : Nat → Path → Bool
  | 0, _ => false
  | fuel + 1, p =>
    -- Arrival at the selected successor, if the IR has selected one and its code starts here.
    if p.events.isEmpty && p.calls.isEmpty && (p.exit.selected.bind place) == some p.pc then
      match p.exit.selected with
      | some s => arrives c hints b s p.stack && arrivesHeld c b s p.held
      | none => false
    else
    match opAt code tree p.pc with
    | none => false
    | some (op, arg, next) =>
      let go (stack : List Expr) (events : List Event) :=
        run code tree dests c hints place b fuel { p with pc := next, stack, events }
      if op == .JUMPDEST then go p.stack p.events
      else if let some v := arg then
        go (.const v :: p.stack) p.events
      else if op == .PUSH0 then go (.const 0 :: p.stack) p.events
      else if op == .POP then
        match p.stack with
        | _ :: rest => go rest p.events
        | [] => false
      else if let some n := dupN op then
        match p.stack[n - 1]? with
        | some e => go (e :: p.stack) p.events
        | none => false
      else if let some n := swapN op then
        match p.stack[0]?, p.stack[n]? with
        | some a, some e => go ((p.stack.set 0 e).set n a) p.events
        | _, _ => false
      else if pureOps.contains op then
        match δ op with
        | some k =>
          match mkOp op (p.stack.take k) with
          | some e =>
            if p.stack.length < k then false else go (c.canon.intern e :: p.stack.drop k) p.events
          | none => false
        | none => false
      else if op == .MLOAD && p.reloads then
        -- A reload: the word a spill store wrote, of a value reload-live here.
        match p.stack with
        | .const a :: rest =>
          match p.held.find? (·.word == a) with
          | some h => (h.value.any fun v => (c.spill.live.at b (p.gap c)).contains v) &&
              go (h.expr :: rest) p.events
          | none => false
        | _ => false
      else if readOps.contains op || writeOps.contains op then
        match δ op, p.events with
        | some k, ev :: events =>
          if ev.op == op && p.stack.length ≥ k && p.stack.take k == ev.args then
            match ev.result, readOps.contains op with
            | some id, true =>
              run code tree dests c hints place b fuel
                ⟨next, .atom id :: p.stack.drop k, events, p.exit, p.calls, ev.held p.held⟩
            | none, false =>
              run code tree dests c hints place b fuel
                ⟨next, p.stack.drop k, events, p.exit, p.calls, ev.held p.held⟩
            | _, _ => false
          else false
        | _, _ => false
      else if haltOps.contains op then
        match p.exit with
        | .halt hop args =>
          let k := (δ op).getD 0
          p.events.isEmpty && p.calls.isEmpty && hop == op && p.stack.length ≥ k &&
            p.stack.take k == args
        | _ => false
      else if op == .JUMP then
        match p.stack with
        | .const t :: rest =>
          validJump code dests t &&
          match p.events, p.calls with
          -- The next call: the callee's arguments on top, then, if it returns, the address of
          -- the code the run goes on at with its results on top.
          | [], cs :: more =>
            match c.frame.callee cs.callee with
            | some ce =>
              ce.offset == t && cs.args.length ≤ rest.length &&
              rest.take cs.args.length == cs.args &&
              if ce.returns then
                (match rest.drop cs.args.length with
                  | .const k :: rest' => validJump code dests k &&
                    run code tree dests c hints place b fuel
                      ⟨k, cs.dsts.map .atom ++ rest', cs.events, p.exit, more,
                        keepHeld cs.keep p.held⟩
                  | _ => false)
              else more.isEmpty && cs.events.isEmpty && (p.exit matches .unreach)
            | none => false
          | _, _ =>
            if p.events.isEmpty && p.calls.isEmpty && (p.exit.selected.bind place) == some t then
              match p.exit.selected with
              | some s => arrives c hints b s rest && arrivesHeld c b s p.held
              | none => false
            -- Into code that is no block's: an outlined unit, which the run continues in.
            else if (hints.any (place ·.block == some t)) then false
            else run code tree dests c hints place b fuel { p with pc := t, stack := rest }
        -- A return: the return address on top of exactly the values.
        | .atom r :: rest =>
          p.events.isEmpty && p.calls.isEmpty && c.frame.returns && r == c.frame.retId &&
            match p.exit with
            | .ret vals => rest == vals
            | _ => false
        | _ => false
      else if op == .JUMPI then
        match p.stack with
        | .const t :: cond :: rest =>
          p.events.isEmpty && p.calls.isEmpty && validJump code dests t &&
          (match p.exit.way cond true with
            | some (.succ s) => place s == some t && arrives c hints b s rest &&
              arrivesHeld c b s p.held
            | some .never => true
            | _ => false) &&
          (match p.exit.way cond false with
            | some (.succ s) =>
              run code tree dests c hints place b fuel
                { p with pc := next, stack := rest, exit := .goto s }
            | some .never => true
            | some (.exit e) =>
              run code tree dests c hints place b fuel
                { p with pc := next, stack := rest, exit := e }
            | none => false)
        | _ => false
      else false

/-- The value an operand reads, if any. -/
def _root_.Fe.Sonatina.Operand.var? : Operand → Option Nat
  | .var id => some id
  | _ => none

/-- The operands of an instruction of the class. -/
def _root_.Fe.Sonatina.Inst.operands : Inst → List Operand
  | .bin _ a b | .cmp _ a b => [a, b]
  | .isZero a | .not a | .clz a => [a]
  | .evm _ args | .call _ args => args
  | _ => []

/-- The operands of a terminator. -/
def _root_.Fe.Sonatina.Term.operands : Term → List Operand
  | .br c _ _ => [c]
  | .brTable s _ cases => s :: cases.map (·.1)
  | .evmReturn a l | .evmRevert a l => [a, l]
  | .ret vals => vals
  | _ => []

/-- Every operand reads a value of `defs`. -/
def reads (defs : List Nat) (ops : List Operand) : Bool :=
  ops.all fun o => o.var?.all defs.contains

/-- The values defined after the statements, from `defs` before them, if each statement reads
    only values defined before it and defines only values not defined before it. -/
def definedAfter (defs : List Nat) : List Stmt → Option (List Nat)
  | [] => some defs
  | s :: rest =>
    if reads defs s.inst.operands && s.dsts.all (!defs.contains ·.1) then
      definedAfter (defs ++ s.dsts.map (·.1)) rest
    else none

/-- An entry slot of block `sb` holds a value of `defs` or a phi of `sb`. -/
def slotDefined (defs : List Nat) (sb : Block) : Slot → Bool
  | .value id => defs.contains id || sb.phis.any (·.dst == id)
  | _ => true

/-- Block `b` reads only values defined before each read: its entry stack's values `entry`,
    its phis, or those its statements define earlier; it defines none of those again (an entry
    value it defined would be the last run's); and each phi of each successor has an operand
    from `b`, so defined and not `undef`, and each value of its entry stack is a phi or defined
    by `b`.  The
    machine IR runs a read of an undefined value nowhere. -/
def defined (f : Func) (hints : List BlockHint) (sp : FuncSpill) (b : Block)
    (entry : List Nat) : Bool :=
  match definedAfter (entry ++ b.phis.map (·.dst) ++ (sp.spillIn b.id).map (·.1)) b.body with
  | none => false
  | some defs => reads defs b.term.operands && b.term.succs.all fun succ =>
    match f.block? succ with
    | some sb => (sb.phis.all fun phi => match phi.incoming.find? (·.2 == b.id) with
      | some (.undef _, _) | none => false
      | some (o, _) => reads defs [o]) &&
      -- A value of the successor's entry stack not its phi is one `b` has defined.
      (hints.find? (·.block == succ)).all (fun h => h.entryStack.all (slotDefined defs sb)) &&
      -- So is a spilled value it starts with in memory.
      (sp.spillIn succ).all fun va => sb.phis.any (·.dst == va.1) || defs.contains va.1
    | none => false

/-- The successor a terminator goes to whatever the values, if any. -/
def _root_.Fe.Sonatina.Term.only : Term → Option Nat
  | .jump d | .brTable _ (some d) [] => some d
  | _ => none

/-- The height of block `b` in the chains of blocks that go to a successor whose code starts
    where theirs does, which the bytes may reach in no step, counted at most `n` deep. -/
def zeroRank (f : Func) (place : Nat → Option Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, b => match (f.block? b).bind (·.term.only) with
    | some s => if place s == place b then zeroRank f place n s + 1 else 0
    | none => 0

/-- No value occurs twice. -/
def nodup : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodup xs

/-- Whether the function's code does nothing to memory beyond its machine IR. -/
def inClass (f : FuncHint) : Bool :=
  f.spills.all (fun sp => !(sp.location matches .frame _)) && !f.frame.dynamicFrame &&
    !f.frame.lazyFrame && !f.frame.dynSpInit && f.frame.callPreserves == 0

/-- The blocks from which the function may return: those that end in `ret`, and those with a
    successor among them, found in as many rounds as the function has blocks. -/
def returning (f : Func) : List Nat :=
  (List.range f.blocks.length).foldl (fun S _ => f.blocks.filterMap fun b =>
    if (b.term matches .ret _) || b.term.succs.any S.contains then some b.id else none) []

/-- The blocks found are all of them: no other block ends in `ret` or goes to one of them. -/
def returningClosed (f : Func) : Bool :=
  f.blocks.all fun b => (returning f).contains b.id ||
    !(b.term matches .ret _) && !b.term.succs.any (returning f).contains

/-- Whether the function returns: it may from its entry block. -/
def returns (f : Func) : Bool := (f.blocks.head?.map ((returning f).contains ·.id)).getD false

/-- The values a function defines: its parameters, phis and statements' results. -/
def _root_.Fe.Sonatina.Func.defs (f : Func) : List Nat :=
  f.params.map (·.1) ++
    f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))

/-- A value no value of the function is: the one that stands for its return address. -/
def _root_.Fe.Sonatina.Func.fresh (f : Func) : Nat := f.defs.foldl max 0 + 1

/-- Where the code of block `b` of function `func` starts. -/
def placeIn (low : Lowering) (func : String) (b : Nat) : Option Nat :=
  Hints.place low 16 (.block func b)

/-- The functions of the section that blocks may call: every one but the section's entry. -/
def callees (low : Lowering) (entry : String) (g : String) : Option Callee := do
  if g == entry then none
  let _ ← low.funcs.find? (·.name == g)
  let f ← low.machine.func? g
  let eb ← f.blocks.head?
  return ⟨← placeIn low g eb.id, f.params.length, f.rets.length, returns f⟩

/-- The frame of function `f` of the section. -/
def frameOf (low : Lowering) (entry : String) (f : Func) : Frame :=
  ⟨f.fresh, returns f, fun b => returns f && (returning f).contains b, callees low entry⟩

/-- Block `b` of function `f` matches its bytes, from its offset and planned entry stack, the
    section entry's block's events led by the free pointer's store. -/
def checkBlock (code : CodeSection) (low : Lowering) (hint : FuncHint) (f : Func) (fr : Frame)
    (sp : FuncSpill) (isRoot : Bool) (entryBlock : Block) (place : Nat → Option Nat) (rank : Nat → Nat)
    (b : Block) : Except String Unit := do
  let c := Ctx.ofBlock f b code.symbols fr sp
  let some h := hint.blocks.find? (·.block == b.id) | throw s!"block{b.id} has no hint"
  let some pc := place b.id | throw s!"block{b.id} has no place"
  let some stack := c.entryStack h | throw s!"block{b.id}: an entry slot is not a value"
  let some (events, calls) := c.segments (sp.guard b.id) 0 b.body
    | throw s!"block{b.id}: an instruction outside the class"
  let some exit := c.exitOf b.term | throw s!"block{b.id}: a terminator outside the class"
  if isRoot && b.id == entryBlock.id then
    unless stack.isEmpty do throw "the entry block's entry stack is not empty"
  let entryValues := h.entryStack.filterMap fun | .value id => some id | _ => none
  unless defined f hint.blocks sp b entryValues do
    throw s!"block{b.id} reads a value not defined before"
  -- A successor whose code starts where `b`'s does may be reached in no step: it is lower.
  unless b.term.only.all fun s => place s != some pc || rank s < rank b.id do
    throw s!"block{b.id} reaches a successor at its own offset and no lower"
  -- The section entry's code stores the initial free pointer first.
  let events := match low.entryFreePtr, isRoot && b.id == entryBlock.id with
    | some ptr, true => { op := .MSTORE, args := [.const 0x40, .const ptr], result := none } :: events
    | _, _ => events
  let held := (sp.spillIn b.id).map fun (v, a) => ⟨a, .atom v, some v⟩
  unless run code.bytecode (codeTree code.bytecode) (jumpdests code.bytecode) c hint.blocks place
      b.id (2 * low.codeSize + 2)
      ⟨pc, stack, events, exit, calls, held⟩ do
    throw s!"block{b.id} at {pc} does not match its bytes"

/-- What function `hint` of the section must be, each with what its failure says: its values
    words and defined once; its entry block without phis or predecessors, entered with the
    arguments on top of the return address if it returns, at offset 0 with no arguments if it
    is the section's entry, which returns nowhere; the blocks it returns from those that end in
    `ret` and their predecessors, with the return address at the bottom of their entry stacks,
    and none in a function that does not return; each `ret` with as many values as it returns. -/
def funcChecks (low : Lowering) (entry : String) (hint : FuncHint) (f : Func)
    (entryBlock : Block) (p : FuncPlan) (L : Live) : List (Bool × String) :=
  let fr := frameOf low entry f
  [(inClass hint, s!"{hint.name} is outside the class"),
   (p.words.all (·.1 < f.fresh) && (p.isEmpty || f.liveClosed p L),
    s!"the spill plan of {hint.name} does not fit its machine IR"),
   (f.blocks.all (fun b =>
      b.phis.all (·.ty.bits == 256) && b.body.all (·.dsts.all (·.2.bits == 256))) &&
      f.params.all (·.2.bits == 256) && f.rets.all (·.bits == 256),
    s!"a value of {hint.name} is not a word"),
   (nodup f.defs, s!"a value of {hint.name} is defined twice"),
   (entryBlock.phis.isEmpty && f.blocks.all (!·.term.succs.contains entryBlock.id),
    s!"the entry block of {hint.name} has phis or predecessors"),
   (hint.name != entry || f.params.isEmpty && !fr.returns &&
      placeIn low hint.name entryBlock.id == some 0,
    "the entry function has parameters, returns, or does not start at offset 0"),
   (returningClosed f, s!"the blocks {hint.name} returns from are not closed"),
   (f.blocks.all fun b => match b.term with
      | .ret vals => vals.length == f.rets.length
      | _ => true,
    s!"a block of {hint.name} returns other than its results"),
   (hint.blocks.all fun h =>
      !h.entryStack.contains .callReturn &&
      if fr.exact h.block then h.entryStack.getLast? == some .funcReturn &&
        !h.entryStack.dropLast.contains .funcReturn
      else fr.returns || !h.entryStack.contains .funcReturn,
    s!"a block of {hint.name} has the return address out of place"),
   (hint.blocks.all (·.entryStack.all fun | .value id => id < f.fresh | _ => true),
    s!"a block of {hint.name} is entered with a value it has not"),
   ((hint.blocks.find? (·.block == entryBlock.id)).map (·.entryStack) ==
      some (f.params.map (.value ·.1) ++ if fr.returns then [.funcReturn] else []),
    s!"the entry block of {hint.name} is not entered with its arguments")]

/-- What the checker knows of the spills of function `f` named `name`, entered at `eb`, under the
    plan and its guard `G`. -/
def funcSpill (plan : SpillPlan) (G : Guard) (name : String) (f : Func) (eb : Block) :
    FuncSpill :=
  let p := (plan.lookup name).getD []
  ⟨p.words, if p.isEmpty then [] else f.reloadLive p, G.at name, eb.id⟩

/-- Function `hint` of the section is as `funcChecks` says and matches its bytes, block by
    block. -/
def checkFunc (code : CodeSection) (low : Lowering) (plan : SpillPlan) (G : Guard)
    (entry : String) (hint : FuncHint) : Except String Unit := do
  let some f := low.machine.func? hint.name | throw s!"no machine IR of {hint.name}"
  let some entryBlock := f.blocks.head? | throw s!"{hint.name} has no entry block"
  let sp := funcSpill plan G hint.name f entryBlock
  (funcChecks low entry hint f entryBlock ((plan.lookup hint.name).getD []) sp.live).forM
    fun (ok, msg) => unless ok do throw msg
  let place := placeIn low hint.name
  f.blocks.forM (checkBlock code low hint f (frameOf low entry f) sp (hint.name == entry)
    entryBlock place (zeroRank f place f.blocks.length))

/-- Every function of the section matches its bytes, the section's entry among them: its
    machine IR with the stores of the spill plan `plan` (`Module.instrument`), under the guard
    the instrumented model runs it under. -/
def checkSection (code : CodeSection) (entry : String) (plan : SpillPlan) :
    Except String Unit := do
  let some low := code.lowering | throw "no lowering record"
  unless code.bytecode.size < UInt256.size do throw "the code does not fit a word"
  unless low.funcs.any (·.name == entry) do throw "no hint of the entry function"
  let low := { low with machine := low.machine.instrument plan }
  low.funcs.forM (checkFunc code low plan (plan.guard low.machine) entry)

/-- The entry function of each section of the sidecar's object. -/
def entries (s : Sidecar) : List (String × String) :=
  ((s.objects.find? (·.name == s.object)).map (·.sections)).getD [] |>.map
    fun sec => (sec.name, sec.entry)

/-- The section `name` of the sidecar is checked against its entry function `entry`. -/
def checkEntry (s : Sidecar) (plan : String → SpillPlan) (name entry : String) :
    Except String Unit := do
  let some code := s.section? name | throw s!"no section {name}"
  match checkSection code entry (plan name) with
  | .ok () => pure ()
  | .error e => throw s!"{name}: {e}"

/-- Each of the sidecar's sections is checked under its spill plan, and it has an `init` and a
    `runtime`. -/
def checkAll (plan : String → SpillPlan) (s : Sidecar) : Except String Unit := do
  (entries s).forM fun (name, entry) => checkEntry s plan name entry
  unless (s.section? "init").isSome && (s.section? "runtime").isSome &&
      ((entries s).lookup "init").isSome && ((entries s).lookup "runtime").isSome do
    throw "no init or runtime section"

/-- The sidecar's sections are checked under the spill plans `plan`. -/
def checkWith (plan : String → SpillPlan) (s : Sidecar) : Bool := (checkAll plan s).isOk

end Fe.Sonatina.Check
