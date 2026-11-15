import Fe.Sonatina.Syntax
import Fe.EVM.Calls
import Fe.EVM.Refine
import Std.Data.TreeMap

/-!
# An interpreter of Sonatina IR

`runFunc` runs a function of a module in the model monad `FeM`, over EVMLean's state: storage,
memory, calldata, logs, return data and message calls are the model library's own primitives
(`Fe/EVM/World.lean`, `Calls.lean`), so a run of the IR is compared with the bytecode as an
exported model is.  `Sidecar.model` is the contract model of an object: its `init` and
`runtime` sections, each run from its entry function.

The runner is `runFuncG`, under a `Guard`: words of memory each statement must leave as they
were, else the run panics with `spillClobbered`.  The machine IR with its memory spills
(`Spill.lean`) runs under one; `runFunc`, `runBlocks` and `runBody` are the runner under the
guard that protects nothing, and `runFunc_eq`, `runBlocks_eq`, `runBody_cons_eq` and
`runBody_nil_eq` unfold them as one step of the IR.

The runner is a least fixpoint (`partial_fixpoint`): a run that loops for ever does not
terminate, whatever the bytecode's gas, so a certificate never fails for want of the model's
fuel.  A run does not terminate either when it reaches what the
semantics leaves undefined or this subset does not cover (`stuck`): an ill-typed operand, a
missing block, `unreachable`, a section entry that returns.  A run that does not terminate
agrees with no result of the bytecode, so a gap in the semantics makes a comparison fail, not
pass.

What the semantics fixes where Sonatina leaves a choice:
- `undef` and a struct field never written read as zero; a division by zero gives zero.
- `evm_malloc` gives fresh zero bytes at the end of memory, and above every range the module
  accesses at a constant address (`Module.fixedEnd`), which Sonatina keeps the memory it
  manages out of.  The bytecode places allocations elsewhere; only return data, logs and
  accounts are compared, so the addresses do not matter unless the program makes them
  observable.
- `sym_addr` and `sym_size` read the symbol table of the compiled section, a fact of the
  layout the IR does not fix.
-/

namespace Fe.Sonatina

open Ethereum Fe Fe.EVM

/-- A value: an integer of `bits` bits, below `2 ^ bits`, or the fields of a struct. -/
inductive Val where
  | int (bits value : Nat)
  | agg (fields : List Val)
  deriving Repr, Inhabited

/-- The values a function has defined. -/
abbrev Env := Std.TreeMap Nat Val

/-- What an instruction needs besides its operands: the offset and size of
    each symbol of the running section, and the address below which `evm_malloc` places
    nothing. -/
structure Ctx where
  symbol : String → Option (Nat × Nat)
  heap : Nat
  /-- The struct types of the module, for the size of an `alloca`. -/
  structs : List (String × List Ty)

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

/-- The value as one of the type its definition declares: an integer of another width is
    reduced to it, as the machine IR's `i256` comparison results are. -/
def Val.as (v : Val) (ty : Ty) : Val :=
  match v, ty with
  | .int _ value, .int _ | .int _ value, .ptr _ => .int ty.bits (value % 2 ^ ty.bits)
  | v, _ => v

def Val.zero : Ty → Val
  | .int bits => .int bits 0
  | .ptr _ => .int 256 0
  | .struct _ | .array _ _ | .unit | .objRef _ | .constRef _ => .agg []

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
  | .mload, [a] => one (Fe.EVM.mload a)
  | .mstore, [a, v] => none' (Fe.EVM.mstore a v)
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

/-- The memory an instruction accesses at a constant address with a constant length: where the
    access ends. -/
def Inst.fixedEnds : Inst → List (Option Nat)
  | .mload a _ | .mstore a _ _ => [constRange a (.imm 256 32)]
  | .memzero d l => [constRange d l]
  | .evm op args =>
    match op, args with
    | .mstore8, [p, _] => [constRange p (.imm 256 1)]
    | .mload, [a] | .mstore, [a, _] => [constRange a (.imm 256 32)]
    | .calldataCopy, [d, _, l] | .codeCopy, [d, _, l] | .returnDataCopy, [d, _, l]
    | .extCodeCopy, [_, d, _, l] | .keccak256, [d, l] | .create, [_, d, l]
    | .create2, [_, d, l, _] => [constRange d l]
    | .log _, p :: l :: _ => [constRange p l]
    | .mcopy, [d, s, l] => [constRange d l, constRange s l]
    | .call, [_, _, _, ap, al, rp, rl] | .staticCall, [_, _, ap, al, rp, rl]
    | .delegateCall, [_, _, ap, al, rp, rl] => [constRange ap al, constRange rp rl]
    | _, _ => []
  | _ => []
where
  constRange : Operand → Operand → Option Nat
    | .imm _ a, .imm _ l => some (a + l)
    | _, _ => none

/-- The word above the memory the module accesses at constant addresses with constant lengths.
    Sonatina keeps the memory it manages, `evm_malloc`'s among it, out of each such range
    (`scan_fixed_reservations`), and rejects an access at a constant address with another length
    unless it is the payload of the `evm_return` or `evm_revert` that follows. -/
def Module.fixedEnd (m : Module) : Nat :=
  let ends := m.funcs.flatMap fun f => f.blocks.flatMap fun b =>
    (b.body.flatMap (·.inst.fixedEnds)) ++ match b.term with
      | .evmReturn a l | .evmRevert a l => [Inst.fixedEnds.constRange a l]
      | _ => []
  ((ends.filterMap id).foldl max 0 + 31) / 32 * 32

/-- Fresh zero bytes at the end of memory and above `heap`: their address. -/
def allocate (heap size : Nat) : FeM Nat := do
  let w ← get
  let base := max w.memory.size heap
  unless base + size < UInt256.size do Fe.M.diverge
  let fresh : ByteArray := ⟨Array.replicate (base + size - w.memory.size) 0⟩
  set { w with memory := w.memory ++ fresh }
  return base

/-- Bytes enough for a value of the type, each scalar a word: more than Sonatina's layout
    gives, which is all an allocation needs. A struct nested past 16 levels takes none. -/
def Ty.size (structs : List (String × List Ty)) (ty : Ty) : Nat :=
  go 16 ty
where
  go : Nat → Ty → Nat
    | 0, _ => 0
    | _ + 1, .int _ | _ + 1, .ptr _ | _ + 1, .objRef _ | _ + 1, .constRef _ => 32
    | depth + 1, .array elem len => len * go depth elem
    | depth + 1, .struct name => ((structs.lookup name).getD []).foldl (· + go depth ·) 0
    | _ + 1, .unit => 0

/-- Run an instruction to the values it defines. -/
def runInst (c : Ctx) (env : Env) : Inst → FeM (List Val)
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
    -- The EVM's `CLZ`, an Osaka opcode: before Osaka the instruction is invalid.
    unless (← read).header.fork = .Osaka do
      let e ← trap
      nomatch e
    return [.int bits (if x = 0 then bits else bits - 1 - x.log2)]
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
  | .malloc size => do return [.int 256 (← allocate c.heap (← evalWord env size).toNat)]
  | .alloca ty => do return [.int 256 (← allocate c.heap (ty.size c.structs))]
  | .symAddr s => do
    let some (offset, _) := c.symbol s | stuck
    return [.int 256 offset]
  | .symSize s => do
    let some (_, size) := c.symbol s | stuck
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
  -- A call is the runner's (`runBody`).
  | .call _ _ => stuck

/-- Bind each value to its id. -/
def bind (env : Env) (dsts : List (Nat × Ty)) (vals : List Val) : FeM Env :=
  if dsts.length == vals.length then
    pure ((dsts.zip vals).foldl (fun env ((id, ty), v) => env.insert id (v.as ty)) env)
  else stuck

/-- Enter block `b` from block `prev`: each phi takes, at once, its operand for `prev`. -/
def enter (env : Env) (prev : Option Nat) (b : Block) : FeM Env := do
  let vals ← b.phis.mapM fun phi => do
    let some p := prev | stuck
    let some (o, _) := phi.incoming.find? (·.2 == p) | stuck
    evalOperand env o
  bind env (b.phis.map fun phi => (phi.dst, phi.ty)) vals

/-- What a run under a spill plan must leave as it is (`Spill.lean`): for each function and
    block, the words of memory each statement of the block may not change (`Guard.at`).  It is
    a table, built once per run.  The machine IR's run protects nothing (`Guard.none`). -/
abbrev Guard := List (String × List (Nat × List (List Nat)))

/-- The guard of the machine IR's run: nothing is protected. -/
def Guard.none : Guard := []

/-- The words each statement of block `b` of function `name` may not change. -/
def Guard.at (g : Guard) (name : String) (b : Nat) : List (List Nat) :=
  ((g.lookup name).bind (·.lookup b)).getD []

/-- The panic code of a run that changes a word it protects: no Fe panic's, as it is no word. -/
def spillClobbered : Nat := 2 ^ 256

/-- The bytes of the words of memory at the addresses. -/
def wordsAt (mem : ByteArray) (ws : List Nat) : List ByteArray := ws.map (mem.readWithPadding · 32)

/-- Run `x`, and panic with `spillClobbered` if it changed a byte of the words at `ws`.  With no
    words it is `x`. -/
def guarded {α : Type} : List Nat → FeM α → FeM α
  | [], x => x
  | ws, x => do
    let before := wordsAt (← get).memory ws
    let a ← x
    if wordsAt (← get).memory ws = before then pure a else Fe.M.panic spillClobbered

@[partial_fixpoint_monotone]
theorem monotone_guarded {α γ : Type} [Lean.Order.PartialOrder γ] (ws : List Nat)
    (x : γ → FeM α) (hx : Lean.Order.monotone x) :
    Lean.Order.monotone fun g => guarded ws (x g) := by
  cases ws with
  | nil => exact hx
  | cons w ws =>
    unfold guarded
    refine Lean.Order.monotone_bind _ _ _ (Lean.Order.monotone_const _) ?_
    refine Lean.Order.monotone_of_monotone_apply _ fun _ => ?_
    exact Lean.Order.monotone_bind _ _ _ hx (Lean.Order.monotone_const _)

/-- A guarded computation that returns has left the words it guards as they were. -/
theorem guarded_kept {α : Type} {ws : List Nat} {x : FeM α} {I : ExecutionEnv} {w w' : World}
    {a : α} (h : (guarded ws x).exec I w = some (.ok (a, w'))) :
    ∀ p ∈ ws, w'.memory.readWithPadding p 32 = w.memory.readWithPadding p 32 := by
  cases ws with
  | nil => intro p hp; cases hp
  | cons q qs =>
    unfold guarded at h
    simp only [Fe.M.exec_bind, Fe.M.exec_get] at h
    split at h
    · cases h
    · cases h
    · rename_i a' w₁ _
      split at h
      · next heq =>
        simp only [Fe.M.exec_pure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        intro p hp
        exact List.map_inj_left.mp heq p hp
      · simp at h

mutual

/-- Run statements, calling functions of `m`, under the guard `g`: each statement leaves the
    words `inh` its callers protect as they were, and those the head of `ps` names, the
    block's own for the statement; a call runs its callee with both protected. -/
def runBodyG (g : Guard) (m : Module) (c : Ctx) (inh : List Nat) (ps : List (List Nat))
    (env : Env) : List Stmt → FeM Env
  | [] => pure env
  | s :: rest => do
    let ws := inh ++ ps.headD []
    let vals ← guarded ws (match s.inst with
      | .call callee args => do runFuncG g m c ws callee (← args.mapM (evalOperand env))
      | inst => runInst c env inst)
    runBodyG g m c inh ps.tail (← bind env s.dsts vals) rest
partial_fixpoint

/-- Run `f` from block `id`, entered from `prev`, under the guard `g` with the words `inh`
    protected. -/
def runBlocksG (g : Guard) (m : Module) (c : Ctx) (inh : List Nat) (f : Func) (env : Env)
    (prev : Option Nat) (id : Nat) : FeM (List Val) := do
  let some b := f.block? id | stuck
  let env ← enter env prev b
  let env ← runBodyG g m c inh (g.at f.name id) env b.body
  match b.term with
  | .jump dest => runBlocksG g m c inh f env (some id) dest
  | .br cond nz z => do
    let (_, v) ← evalInt env cond
    runBlocksG g m c inh f env (some id) (if v != 0 then nz else z)
  | .brTable s default cases => do
    let (_, v) ← evalInt env s
    let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
    match (vals.find? (·.1 == v)).map (·.2) <|> default with
    | some dest => runBlocksG g m c inh f env (some id) dest
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
partial_fixpoint

/-- Run function `name` of `m` on `args`, under the guard `g` with the words `inh` protected:
    it returns only if it leaves them as they were. -/
def runFuncG (g : Guard) (m : Module) (c : Ctx) (inh : List Nat) (name : String)
    (args : List Val) : FeM (List Val) := guarded inh do
  let some f := m.func? name | stuck
  let some entry := f.blocks.head? | stuck
  let env ← bind {} f.params args
  runBlocksG g m c inh f env none entry.id
partial_fixpoint

end

/-- Run statements, calling functions of `m`: the machine IR's run, which protects nothing. -/
@[irreducible] def runBody (m : Module) (c : Ctx) (env : Env) (stmts : List Stmt) : FeM Env :=
  runBodyG .none m c [] [] env stmts

/-- Run `f` from block `id`, entered from `prev`. -/
@[irreducible] def runBlocks (m : Module) (c : Ctx) (f : Func) (env : Env) (prev : Option Nat)
    (id : Nat) : FeM (List Val) :=
  runBlocksG .none m c [] f env prev id

/-- Run function `name` of `m` on `args`. -/
@[irreducible] def runFunc (m : Module) (c : Ctx) (name : String) (args : List Val) :
    FeM (List Val) :=
  runFuncG .none m c [] name args

/-- The guarded run that protects nothing is the machine IR's. -/
theorem runFuncG_none (m : Module) (c : Ctx) (name : String) (args : List Val) :
    runFuncG .none m c [] name args = runFunc m c name args := by
  unfold runFunc; rfl

theorem runBody_nil_eq (m : Module) (c : Ctx) (env : Env) : runBody m c env [] = pure env := by
  unfold runBody; rw [runBodyG.eq_1]

theorem runBody_cons_eq (m : Module) (c : Ctx) (env : Env) (s : Stmt) (rest : List Stmt) :
    runBody m c env (s :: rest) = (do
      let vals ← match s.inst with
        | .call callee args => do runFunc m c callee (← args.mapM (evalOperand env))
        | inst => runInst c env inst
      runBody m c (← bind env s.dsts vals) rest) := by
  unfold runBody runFunc
  rw [runBodyG.eq_2]
  simp only [List.nil_append, List.headD_nil, List.tail_nil, guarded]
  rcases s with ⟨dsts, inst⟩
  cases inst <;> first | rfl | simp only [bind_assoc]

theorem runBlocks_eq (m : Module) (c : Ctx) (f : Func) (env : Env) (prev : Option Nat)
    (id : Nat) : runBlocks m c f env prev id = (do
      let some b := f.block? id | stuck
      let env ← enter env prev b
      let env ← runBody m c env b.body
      match b.term with
      | .jump dest => runBlocks m c f env (some id) dest
      | .br cond nz z => do
        let (_, v) ← evalInt env cond
        runBlocks m c f env (some id) (if v != 0 then nz else z)
      | .brTable s default cases => do
        let (_, v) ← evalInt env s
        let vals ← cases.mapM fun (o, dest) => return ((← evalInt env o).2, dest)
        match (vals.find? (·.1 == v)).map (·.2) <|> default with
        | some dest => runBlocks m c f env (some id) dest
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
      | .unreachable => stuck) := by
  unfold runBlocks runBody; rw [runBlocksG.eq_1]; rfl

theorem runFunc_eq (m : Module) (c : Ctx) (name : String) (args : List Val) :
    runFunc m c name args = (do
      let some f := m.func? name | stuck
      let some entry := f.blocks.head? | stuck
      let env ← bind {} f.params args
      runBlocks m c f env none entry.id) := by
  unfold runFunc runBlocks; rw [runFuncG.eq_1]; rfl

/-- Which IR of a sidecar runs: the module after optimization, which every section shares, or
    a section's own module after the backend's IR pipeline (`source`) or machine lowering. -/
inductive Level where
  | postOpt | source | machine
  deriving Repr, BEq, Inhabited

/-- The module section `code` runs at the level. -/
def Sidecar.moduleAt (s : Sidecar) (code : CodeSection) : Level → Option Module
  | .postOpt => s.module
  | .source => code.lowering.bind (·.source)
  | .machine => code.lowering.map (·.machine)

/-- Run section `name` of the sidecar's object from its entry, in the IR of the level, as
    `prep` prepares it: the module to run and the guard to run it under.  The entry ends the
    call itself: one that returns is stuck, as is a run at a level whose IR the sidecar does
    not have (`Sidecar.moduleAt`).  At the machine level the run starts with what the section
    entry's code does before the machine IR: it stores the initial free pointer the lowering
    record names.  The context is the level's module's, whatever `prep` makes of it. -/
def Sidecar.runSectionWith (s : Sidecar) (name : String) (level : Level)
    (prep : Module → Module × Guard) : FeM ByteArray := do
  let some obj := s.objects.find? (·.name == s.object) | stuck
  let some sec := obj.sections.find? (·.name == name) | stuck
  let some code := s.section? name | stuck
  let some m := s.moduleAt code level | stuck
  -- The section entry's code stores the initial free pointer before the machine IR's first
  -- instruction, which reads it.
  if level == .machine then
    if let some ptr := code.lowering.bind (·.entryFreePtr) then
      mstore (UInt256.ofNat 0x40) (UInt256.ofNat ptr)
  let _ ← runFuncG (prep m).2 (prep m).1 ⟨(code.symbols.lookup ·), m.fixedEnd, m.structs⟩ []
    sec.entry []
  stuck

/-- Run section `name` of the sidecar's object from its entry, in the IR of the level, as it
    is (`Sidecar.runSectionWith`). -/
def Sidecar.runSection (s : Sidecar) (name : String) (level : Level := .postOpt) :
    FeM ByteArray :=
  s.runSectionWith name level fun m => (m, .none)

/-- The contract model the IR of the level gives.  The constructor reads its arguments from
    the running code, as the init section does, and ends with the whole deployed code. -/
def Sidecar.model (s : Sidecar) (level : Level := .postOpt) : ContractModel where
  init _ := s.runSection "init" level
  runtime := s.runSection "runtime" level

end Fe.Sonatina
