import Fe.Sonatina.Hints

/-!
# Checking bytes against the machine IR

`check s` decides that each section of the sidecar `s` is emitted from its machine IR, for the
class of sections the first checker covers: one function a section (no internal calls), no
memory spills, no dynamic frames, no dynamic stack pointer, no call preserves, every value and
immediate a word (as the EVM computes on words), and only the instructions `pureWith`,
`eventWith` and `exitOf` translate.  The hints are inputs: a wrong one makes `check` false.

The machine IR is the specification, so the checker also makes sure its run never gets stuck
where the bytes go on: each value is defined once, each read reads a value defined before it
(the block's entry stack, its phis, or an earlier statement of the block: `defined`), each
successor's phis have an operand from the block, a pure instruction defines one value, the
entry function takes no parameters and its entry block has no phis and no predecessor.  A block
may go to a successor whose code starts at its own offset, which the bytes reach in no step,
only down a chain that ends (`zeroRank`).

For each machine block `B`, it runs two symbolic executions into one language of words:
- the machine IR's instructions of `B`, as expressions over the values `B` does not compute
  purely (those of other blocks, its phis and its reads), each pure value of `B` expanded to
  its definition;
- the bytes from `B`'s offset, starting from `B`'s planned entry stack: `PUSH`, `DUP`, `SWAP`,
  `POP` and `JUMPDEST` move expressions, a pure opcode builds one, every read or write of state
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
  deriving DecidableEq, Repr

/-- The pure opcodes, which compute a word from their operands and the frame's environment. -/
def pureOps : List Operation :=
  [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT,
   .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .ADDRESS, .ORIGIN,
   .CALLER, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CODESIZE]

/-- The opcodes that read state: their result is an event's. -/
def readOps : List Operation := [.SLOAD, .MLOAD, .KECCAK256]

/-- The opcodes that write state. -/
def writeOps : List Operation :=
  [.SSTORE, .MSTORE, .MSTORE8, .CODECOPY, .CALLDATACOPY, .MCOPY, .LOG0, .LOG1, .LOG2, .LOG3,
   .LOG4]

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

/-- The opcode of a pure machine instruction.  `sar`, `evm_sdiv` and `evm_smod` are left out
    until their signed arithmetic is proved the EVM's. -/
def binOpcode : BinOp → Option Operation
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .shl => some .SHL
  | .shr => some .SHR | .and => some .AND | .or => some .OR | .xor => some .XOR
  | .evmUdiv => some .DIV | .evmUmod => some .MOD | .evmExp => some .EXP
  | .evmByte => some .BYTE | .evmSignExtend => some .SIGNEXTEND
  | _ => none

def cmpOpcode : CmpOp → Option Operation
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT | .eq => some .EQ
  | _ => none

/-- The pure EVM instructions of the machine IR. -/
def evmPureOpcode : EvmOp → Option Operation
  | .address => some .ADDRESS | .origin => some .ORIGIN | .caller => some .CALLER
  | .callValue => some .CALLVALUE | .calldataLoad => some .CALLDATALOAD
  | .calldataSize => some .CALLDATASIZE | .codeSize => some .CODESIZE
  | .addMod => some .ADDMOD | .mulMod => some .MULMOD
  | _ => none

/-- The EVM instructions of the machine IR that read or write state. -/
def evmEventOpcode : EvmOp → Option Operation
  | .sload => some .SLOAD | .mload => some .MLOAD | .keccak256 => some .KECCAK256
  | .sstore => some .SSTORE | .mstore => some .MSTORE | .mstore8 => some .MSTORE8
  | .codeCopy => some .CODECOPY | .calldataCopy => some .CALLDATACOPY | .mcopy => some .MCOPY
  | .log 0 => some .LOG0 | .log 1 => some .LOG1 | .log 2 => some .LOG2 | .log 3 => some .LOG3
  | .log 4 => some .LOG4
  | _ => none

/-- The value a statement defines, if one, with its instruction. -/
def _root_.Fe.Sonatina.Stmt.def? (s : Stmt) : Option (Nat × Inst) :=
  match s.dsts with
  | [(id, _)] => some (id, s.inst)
  | _ => none

/-- What the checker knows of a machine block: its function, the statement defining each
    value of the block, and the section's symbols. -/
structure Ctx where
  func : Func
  defs : List (Nat × Inst)
  symbols : List (String × Nat × Nat)

/-- The context of block `b`: only its own values are expanded, so a value of another block is
    the word the run of the IR holds for it when `b` runs. -/
def Ctx.ofBlock (f : Func) (b : Block) (symbols : List (String × Nat × Nat)) : Ctx :=
  ⟨f, b.body.filterMap Stmt.def?, symbols⟩

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
  | _ => none

/-- The expression of a value: its definition, if pure, expanded at most `depth` deep, else
    itself. -/
def Ctx.expand (c : Ctx) : Nat → Nat → Option Expr
  | 0, _ => none
  | depth + 1, id =>
    match c.defs.lookup id with
    | some inst => match pureWith (c.expand depth) c.symbols inst with
      | some e => some e
      | none => if (eventWith (c.expand depth) inst).isSome then some (.atom id) else none
    | none => some (.atom id)

def Ctx.operand (c : Ctx) (depth : Nat) : Operand → Option Expr := operandWith (c.expand depth)

def Ctx.pureExpr (c : Ctx) (depth : Nat) : Inst → Option Expr :=
  pureWith (c.expand depth) c.symbols

def Ctx.eventOf (c : Ctx) (depth : Nat) : Inst → Option (Operation × List Expr) :=
  eventWith (c.expand depth)

/-- The bound on the depth of an expression. -/
def depth : Nat := 64

/-- The event of a statement: none if it is pure, `none` itself if it is outside the class. -/
def Ctx.eventOfStmt (c : Ctx) (s : Stmt) : Option (Option Event) :=
  match c.pureExpr depth s.inst, c.eventOf depth s.inst with
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
    | [], false => some (some ⟨op, args, none⟩)
    | [(id, _)], true => some (some ⟨op, args, some id⟩)
    | _, _ => none
  | none, none => none

/-- The events of a block's statements, in order, or `none` if a statement is outside the class:
    each is pure, or an event that defines at most one value. -/
def Ctx.events (c : Ctx) (b : Block) : Option (List Event) :=
  b.body.filterMapM c.eventOfStmt

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
  deriving Repr, Inhabited

def Ctx.exitOf (c : Ctx) : Term → Option Exit
  | .jump dest => some (.goto dest)
  | .br cond nz z => do return .br (← c.operand depth cond) nz z
  | .brTable s (some default) cases => do
    let cases ← cases.mapM fun (o, dest) => match o with
      | .imm 256 v => if v < UInt256.size then some (v, dest) else none
      | _ => none
    return .table (← c.operand depth s) default cases []
  | .evmReturn a l => do return .halt .RETURN [← c.operand depth a, ← c.operand depth l]
  | .evmRevert a l => do return .halt .REVERT [← c.operand depth a, ← c.operand depth l]
  | .evmStop => some (.halt .STOP [])
  | .evmInvalid => some (.halt .INVALID [])
  | _ => none

/-- The planned entry stack of a block, as expressions. -/
def Ctx.entryStack (c : Ctx) (hint : BlockHint) : Option (List Expr) :=
  hint.entryStack.mapM fun
    | .value id => c.expand depth id
    | .imm v => some (.const v)
    | _ => none

/-- What the entry stack of `succ` must be when `pred` jumps to it: each phi of `succ` replaced
    by its operand from `pred`. -/
def Ctx.arrival (c : Ctx) (hints : List BlockHint) (pred succ : Nat) : Option (List Expr) := do
  let hint ← hints.find? (·.block == succ)
  let b ← c.func.block? succ
  hint.entryStack.mapM fun
    | .value id =>
      match b.phis.find? (·.dst == id) with
      | some phi => do c.operand depth (← phi.incoming.find? (·.2 == pred)).1
      | none => c.expand depth id
    | .imm v => some (.const v)
    | _ => none

/-- A run of the bytes for one block, at `pc`. -/
structure Path where
  pc : Nat
  stack : List Expr
  events : List Event
  exit : Exit

/-- The bytes' opcode at `pc`, its immediate, and the next pc, if the instruction lies in the
    code: what follows the code (a constructor's arguments) does not change it. -/
def opAt (code : ByteArray) (pc : Nat) : Option (Operation × Option Nat × Nat) :=
  (Hints.decodeAt code pc).filter fun (_, _, next) => next ≤ code.size

/-- `true` if `t` is a valid jump destination of the code. -/
def validJump (code : ByteArray) (t : Nat) : Bool :=
  t < code.size && (D_J code 0).contains (UInt256.ofNat t)

/-- The number of the `DUP` or `SWAP`: `DUPn` copies the `n`-th item, `SWAPn` swaps the first
    with the `n + 1`-th. -/
def dupN : Operation → Option Nat
  | .Dup op => some ((serializeInstr (.Dup op)).toNat - 0x7f)
  | _ => none

def swapN : Operation → Option Nat
  | .Exchange op => some ((serializeInstr (.Exchange op)).toNat - 0x8f)
  | _ => none

/-- Arrival at `succ` from `pred` with `stack`: `succ`'s entry stack is on top. -/
def arrives (c : Ctx) (hints : List BlockHint) (pred succ : Nat) (stack : List Expr) : Bool :=
  match c.arrival hints pred succ with
  | some expected => expected.length ≤ stack.length && stack.take expected.length == expected
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
def run (code : ByteArray) (c : Ctx) (hints : List BlockHint) (place : Nat → Option Nat)
    (b : Nat) : Nat → Path → Bool
  | 0, _ => false
  | fuel + 1, p =>
    -- Arrival at the selected successor, if the IR has selected one and its code starts here.
    if p.events.isEmpty && (p.exit.selected.bind place) == some p.pc then
      match p.exit.selected with
      | some s => arrives c hints b s p.stack
      | none => false
    else
    match opAt code p.pc with
    | none => false
    | some (op, arg, next) =>
      let go (stack : List Expr) (events : List Event) :=
        run code c hints place b fuel { p with pc := next, stack, events }
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
          | some e => if p.stack.length < k then false else go (e :: p.stack.drop k) p.events
          | none => false
        | none => false
      else if readOps.contains op || writeOps.contains op then
        match δ op, p.events with
        | some k, ev :: events =>
          if ev.op == op && p.stack.length ≥ k && p.stack.take k == ev.args then
            match ev.result, readOps.contains op with
            | some id, true => go (.atom id :: p.stack.drop k) events
            | none, false => go (p.stack.drop k) events
            | _, _ => false
          else false
        | _, _ => false
      else if haltOps.contains op then
        match p.exit with
        | .halt hop args =>
          let k := (δ op).getD 0
          p.events.isEmpty && hop == op && p.stack.length ≥ k && p.stack.take k == args
        | _ => false
      else if op == .JUMP then
        match p.stack with
        | .const t :: rest =>
          validJump code t &&
          if p.events.isEmpty && (p.exit.selected.bind place) == some t then
            match p.exit.selected with
            | some s => arrives c hints b s rest
            | none => false
          -- Into code that is no block's: an outlined unit, which the run continues in.
          else if (hints.any (place ·.block == some t)) then false
          else run code c hints place b fuel { p with pc := t, stack := rest }
        | _ => false
      else if op == .JUMPI then
        match p.stack with
        | .const t :: cond :: rest =>
          p.events.isEmpty && validJump code t &&
          (match p.exit.way cond true with
            | some (.succ s) => place s == some t && arrives c hints b s rest
            | some .never => true
            | _ => false) &&
          (match p.exit.way cond false with
            | some (.succ s) =>
              run code c hints place b fuel { p with pc := next, stack := rest, exit := .goto s }
            | some .never => true
            | some (.exit e) =>
              run code c hints place b fuel { p with pc := next, stack := rest, exit := e }
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
  | .isZero a | .not a => [a]
  | .evm _ args => args
  | _ => []

/-- The operands of a terminator. -/
def _root_.Fe.Sonatina.Term.operands : Term → List Operand
  | .br c _ _ => [c]
  | .brTable s _ cases => s :: cases.map (·.1)
  | .evmReturn a l | .evmRevert a l => [a, l]
  | _ => []

/-- The successors of a terminator. -/
def _root_.Fe.Sonatina.Term.succs : Term → List Nat
  | .jump d => [d]
  | .br _ nz z => [nz, z]
  | .brTable _ d cases => d.toList ++ cases.map (·.2)
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

/-- Block `b` reads only values defined before each read: its entry stack's values `entry`,
    its phis, or those its statements define earlier; it defines none of those again (an entry
    value it defined would be the last run's); and each phi of each successor has an operand
    from `b`, so defined.  The machine IR runs a read of an undefined value nowhere. -/
def defined (f : Func) (b : Block) (entry : List Nat) : Bool :=
  match definedAfter (entry ++ b.phis.map (·.dst)) b.body with
  | none => false
  | some defs => reads defs b.term.operands && b.term.succs.all fun succ =>
    match f.block? succ with
    | some sb => sb.phis.all fun phi => match phi.incoming.find? (·.2 == b.id) with
      | some (o, _) => reads defs [o]
      | none => false
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
  f.spills.isEmpty && !f.frame.dynamicFrame && !f.frame.lazyFrame && !f.frame.dynSpInit &&
    f.frame.callPreserves == 0

/-- Block `b` of the section's one function matches its bytes, from its offset and planned
    entry stack, the entry block's events led by the free pointer's store. -/
def checkBlock (code : CodeSection) (low : Lowering) (hint : FuncHint) (f : Func)
    (entryBlock : Block) (place : Nat → Option Nat) (rank : Nat → Nat) (b : Block) :
    Except String Unit := do
  let c := Ctx.ofBlock f b code.symbols
  let some h := hint.blocks.find? (·.block == b.id) | throw s!"block{b.id} has no hint"
  let some pc := place b.id | throw s!"block{b.id} has no place"
  let some stack := c.entryStack h | throw s!"block{b.id}: an entry slot is not a value"
  let some events := c.events b | throw s!"block{b.id}: an instruction outside the class"
  let some exit := c.exitOf b.term | throw s!"block{b.id}: a terminator outside the class"
  if b.id == entryBlock.id then
    unless stack.isEmpty do throw "the entry block's entry stack is not empty"
  let entryValues := h.entryStack.filterMap fun | .value id => some id | _ => none
  unless defined f b entryValues do throw s!"block{b.id} reads a value not defined before"
  -- A successor whose code starts where `b`'s does may be reached in no step: it is lower.
  unless b.term.only.all fun s => place s != some pc || rank s < rank b.id do
    throw s!"block{b.id} reaches a successor at its own offset and no lower"
  -- The section entry's code stores the initial free pointer first.
  let events := match low.entryFreePtr, b.id == entryBlock.id with
    | some ptr, true => ⟨.MSTORE, [.const 0x40, .const ptr], none⟩ :: events
    | _, _ => events
  unless run code.bytecode c hint.blocks place b.id (2 * low.codeSize + 2)
      ⟨pc, stack, events, exit⟩ do
    throw s!"block{b.id} at {pc} does not match its bytes"

/-- Every block of the section's one function matches its bytes, the entry block at offset 0
    with an empty entry stack. -/
def checkSection (code : CodeSection) (entry : String) : Except String Unit := do
  let some low := code.lowering | throw "no lowering record"
  unless code.bytecode.size < UInt256.size do throw "the code does not fit a word"
  let [hint] := low.funcs | throw "not one function"
  unless hint.name == entry && inClass hint do throw s!"{hint.name} is outside the class"
  let some f := low.machine.func? entry | throw "no machine IR of the entry"
  let some entryBlock := f.blocks.head? | throw "no entry block"
  unless f.blocks.all fun b =>
      b.phis.all (·.ty.bits == 256) && b.body.all (·.dsts.all (·.2.bits == 256)) do
    throw "a value is not a word"
  let defs := f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))
  unless nodup defs do throw "a value is defined twice"
  unless f.params.isEmpty && entryBlock.phis.isEmpty &&
      f.blocks.all (!·.term.succs.contains entryBlock.id) do
    throw "the entry function has parameters, or its entry block phis or predecessors"
  let place (b : Nat) := Hints.place low 16 (.block hint.name b)
  unless place entryBlock.id == some 0 do throw "the entry block is not at offset 0"
  let rank := zeroRank f place f.blocks.length
  f.blocks.forM (checkBlock code low hint f entryBlock place rank)

/-- The entry function of each section of the sidecar's object. -/
def entries (s : Sidecar) : List (String × String) :=
  ((s.module.objects.find? (·.name == s.object)).map (·.sections)).getD [] |>.map
    fun sec => (sec.name, sec.entry)

/-- Each of the sidecar's sections is checked, and it has an `init` and a `runtime`. -/
def checkAll (s : Sidecar) : Except String Unit := do
  for (name, entry) in entries s do
    let some code := s.section? name | throw s!"no section {name}"
    match checkSection code entry with
    | .ok () => pure ()
    | .error e => throw s!"{name}: {e}"
  unless (s.section? "init").isSome && (s.section? "runtime").isSome &&
      ((entries s).lookup "init").isSome && ((entries s).lookup "runtime").isSome do
    throw "no init or runtime section"

def check (s : Sidecar) : Bool := (checkAll s).isOk

end Fe.Sonatina.Check
