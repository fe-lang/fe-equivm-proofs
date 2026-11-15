import Ethereum.UInt256
import Lean.ToExpr

/-!
# Sonatina IR

The data of a Sonatina module as the EVM backend receives it after optimization: functions of
basic blocks in SSA form, and objects whose sections name an entry function and the sections
they embed.  `Fe/Sonatina/README.md` describes the subset and where it comes from.

Values are typed integers.  An operand of type `iN` is held as its unsigned value below `2 ^ N`;
signed instructions read it in two's complement.  A pointer is a 256-bit integer.  A value of a
struct type is the list of its fields.
-/

namespace Fe.Sonatina

open Ethereum

/-- A Sonatina type, as far as the interpreter needs it. -/
inductive Ty where
  /-- `i1` … `i256`. -/
  | int (bits : Nat)
  /-- `*T`: an address in memory, 256 bits on the EVM. -/
  | ptr (pointee : Ty)
  /-- A struct type declared by `type @name = {…}`. -/
  | struct (name : String)
  /-- `[T; n]`, a value of `n` elements like a struct's fields. -/
  | array (elem : Ty) (len : Nat)
  | unit
  /-- `objref<T>` and `constref<T>`: a reference to an object of type `T` in memory or to a
      constant.  The interpreter has no instruction on one; a machine IR keeps the struct types
      of its section IR, some with such fields, which no machine instruction uses. -/
  | objRef (pointee : Ty)
  | constRef (pointee : Ty)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- The bits a scalar of the type takes; a struct takes none of its own. -/
def Ty.bits : Ty → Nat
  | .int bits => bits
  | .ptr _ => 256
  | .struct _ | .array _ _ | .unit | .objRef _ | .constRef _ => 0

/-- An operand: a value the function defines, or an immediate. -/
inductive Operand where
  /-- The value `v<id>`. -/
  | var (id : Nat)
  /-- An immediate of `bits` bits, as its unsigned value. -/
  | imm (bits : Nat) (value : Nat)
  /-- `undef.T`. -/
  | undef (ty : Ty)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Two operands of one integer type to one of that type. -/
inductive BinOp where
  | add | sub | mul | udiv | sdiv | umod | smod | shl | shr | sar | and | or | xor
  /-- The EVM's own forms, which give zero for a zero divisor. -/
  | evmUdiv | evmSdiv | evmUmod | evmSmod
  | evmExp | evmByte | evmSignExtend
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Comparisons, to `i1`. -/
inductive CmpOp where
  | lt | gt | le | ge | slt | sgt | sle | sge | eq | ne
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Arithmetic that also reports, as an `i1`, whether the result wrapped. -/
inductive OvfOp where
  | uaddo | saddo | usubo | ssubo | umulo | smulo
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive CastOp where
  | zext | sext | trunc | ptrToInt | intToPtr | bitcast
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- The instructions that read or change the EVM state, other than memory and control. Each
    takes 256-bit operands; those that give a value give one. -/
inductive EvmOp where
  | address | balance | origin | caller | callValue | calldataLoad | calldataSize
  | calldataCopy | codeSize | codeCopy | gasPrice | extCodeSize | extCodeHash | extCodeCopy
  | returnDataSize | returnDataCopy | blockHash | coinbase | timestamp | number | prevRandao
  | gasLimit | chainId | selfBalance | baseFee | blobHash | blobBaseFee | gas | codeLoad
  /-- The machine IR's word load and store. -/
  | mload | mstore
  | sload | sstore | tload | tstore | keccak256 | mcopy | mstore8
  | log (topics : Nat)
  | create | create2 | call | staticCall | delegateCall
  | addMod | mulMod
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive Inst where
  | bin (op : BinOp) (lhs rhs : Operand)
  | cmp (op : CmpOp) (lhs rhs : Operand)
  | isZero (arg : Operand)
  | not (arg : Operand)
  | neg (arg : Operand)
  /-- The zero bits above the highest set bit, or below the lowest, as a value of the type. -/
  | clz (arg : Operand)
  | ctz (arg : Operand)
  | ovf (op : OvfOp) (lhs rhs : Operand)
  | cast (op : CastOp) (arg : Operand) (ty : Ty)
  | select (cond onTrue onFalse : Operand)
  | evm (op : EvmOp) (args : List Operand)
  /-- `mload addr T`: a value of type `T` read from memory. -/
  | mload (addr : Operand) (ty : Ty)
  /-- `mstore addr value T`. -/
  | mstore (addr value : Operand) (ty : Ty)
  | memzero (dest len : Operand)
  /-- `evm_malloc size`: fresh memory of `size` bytes. -/
  | malloc (size : Operand)
  /-- `alloca T`: fresh memory for a value of type `T`. -/
  | alloca (ty : Ty)
  /-- `sym_addr` and `sym_size` of a symbol as the IR writes it: `&embed`, `%func`, `$global`,
      or `.` for the running section. -/
  | symAddr (sym : String)
  | symSize (sym : String)
  | insertValue (agg index value : Operand)
  | extractValue (agg index : Operand)
  /-- `evm_keccak256_words w…`: the hash of the words, each as 32 big-endian bytes. -/
  | keccakWords (words : List Operand)
  | call (callee : String) (args : List Operand)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive Term where
  | jump (dest : Nat)
  /-- To `nz` if the condition is not zero, else to `z`. -/
  | br (cond : Operand) (nz z : Nat)
  /-- To the block of the first case whose value the scrutinee equals, else to the default. -/
  | brTable (scrutinee : Operand) (default : Option Nat) (cases : List (Operand × Nat))
  | ret (values : List Operand)
  | evmReturn (addr len : Operand)
  | evmRevert (addr len : Operand)
  | evmStop
  | evmInvalid
  | unreachable
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- `v<dst>.T = phi (operand block)…`. -/
structure Phi where
  dst : Nat
  ty : Ty
  incoming : List (Operand × Nat)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- An instruction and the values it defines, none, one, or two for `ovf`. -/
structure Stmt where
  dsts : List (Nat × Ty)
  inst : Inst
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Block where
  id : Nat
  phis : List Phi
  body : List Stmt
  term : Term
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- A function; its first block is the entry. -/
structure Func where
  name : String
  params : List (Nat × Ty)
  rets : List Ty
  blocks : List Block
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Section where
  name : String
  entry : String
  /-- The sections embedded in this one, as `(symbol, section)`, for `embed .s as &symbol`. -/
  embeds : List (String × String)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Object where
  name : String
  sections : List Section
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- The struct types and functions of a module; its objects are the sidecar's. -/
structure Module where
  structs : List (String × List Ty)
  funcs : List Func
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Module.func? (m : Module) (name : String) : Option Func := m.funcs.find? (·.name == name)

def Func.block? (f : Func) (id : Nat) : Option Block := f.blocks.find? (·.id == id)

/-- A slot of a block's entry stack. -/
inductive Slot where
  | value (id : Nat)
  | imm (value : Nat)
  /-- The address the function returns to. -/
  | funcReturn
  /-- The address an internal call returns to. -/
  | callReturn
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Where a value the stack does not always hold is kept. -/
inductive SpillLocation where
  | memory (addr : Nat)
  | frame (slot : Nat)
  | rematerialized
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- A block of the machine IR: the source blocks it comes from, where its code starts if it is
    laid out, the block it is emitted as if it is only a jump, and its entry stack, top first. -/
structure BlockHint where
  block : Nat
  sources : List Nat
  offset : Option Nat
  aliasOf : Option Nat
  entryStack : List Slot
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Where the late merges moved code: to a block of a function or unit, a function, a unit, or
    an instruction no IR names. -/
inductive CodeLabel where
  | block (func : String) (block : Nat)
  | func (name : String)
  | unit (name : String)
  | inst
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- What a function's code does with memory beyond its machine IR: a dynamic frame (stable
    objects in it, or a frame entered and left), the dynamic stack pointer initialized at entry
    or before calls, and scratch objects saved around calls (their number). -/
structure FrameHint where
  dynamicFrame : Bool
  lazyFrame : Bool
  dynSpInit : Bool
  callPreserves : Nat
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure FuncHint where
  name : String
  offset : Option Nat
  blocks : List BlockHint
  spills : List (Nat × SpillLocation)
  frame : FrameHint
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- How the backend lowered a section: the IR machine lowering read (`source`), the machine IR
    the code is emitted from (`machine`), and what connects the machine IR to the bytes. -/
structure Lowering where
  /-- `none` when the section IR uses what the subset does not read: only the machine IR is
      needed to check the bytes. -/
  source : Option Module
  machine : Module
  codeSize : Nat
  arenaBase : Nat
  dynBase : Nat
  entryFreePtr : Option Nat
  funcs : List FuncHint
  /-- The outlined code units: name, offset and size. -/
  units : List (String × Nat × Nat)
  /-- Code that went to the first label goes to the second. -/
  redirects : List (CodeLabel × CodeLabel)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- A section of compiled code: its bytes, the place and size of each symbol it defines, and
    how it was lowered. -/
structure CodeSection where
  name : String
  bytecode : ByteArray
  symbols : List (String × Nat × Nat)
  lowering : Option Lowering

/-- The sidecar of an object: the objects of the module the backend compiled it from, that
    module, and the object's sections. -/
structure Sidecar where
  object : String
  /-- Each section's entry function and embeds. -/
  objects : List Object
  /-- `none` when the module uses what the subset does not read: only each section's machine
      IR is needed to check the bytes. -/
  module : Option Module
  sections : List CodeSection

def Sidecar.section? (s : Sidecar) (name : String) : Option CodeSection :=
  s.sections.find? (·.name == name)

end Fe.Sonatina
