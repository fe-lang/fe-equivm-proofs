import Fe.Sonatina.H.World

/-!
# The instructions of H (design §3.2, §3.4, §3.6, §3.7)

`stepInst` runs every instruction but the three the relation (`H/Sem.lean`) runs itself: the
allocations `alloca` and `evm_malloc`, whose address word and bytes are a choice (§3.3), and
`call`.  `stepTerm` runs a terminator.  Both are functions: everything but allocation is
deterministic in H.  `IRes.stuck` is a construct H does not define (an ill-typed operand, a
missing symbol, a run of the model library that does not terminate): the relation has no rule
for it, so a run that reaches one has no derivation, and the well-formedness predicate
(`H/Wf.lean`) rejects what it can see statically (§3.7, "static rejections").

**Pointers** (§3.2, decision 2): `gep`; `add` of a pointer and an integer in either order;
`sub (ptr b o) (int k)`; `or p 0`, `xor p 0`, `and p (2 ^ 256 - 1)` in either order;
`ptr_to_int` to `i256`; `int_to_ptr` from `i256`; `bitcast` to a pointer type; `select` and
`phi` keep the origin.  Every other operation with a pointer operand computes on the operand's
word (`State.word`) and gives an integer (`binVal`, `wordOp`).  Comparisons of pointers are on
their words, so those of different blocks depend on the address words chosen.

**Memory** (§3.4): every access of `len > 0` bytes resolves through `State.range` first, and an
access outside a block, or through an integer, is `ub` before anything else the instruction
does.  §3.4 does not order an access's `ub` against the instruction's other failures (a static
violation, a read past the return data); H resolves the memory ranges first (`Interpretation
I3` in `H/Sem.lean`).  `evm_mcopy` copies cells, fragments included, reading
the whole source first (§3.4, review 22 H2); copies from calldata, code, return data and
external code and a call's output write plain bytes; world operations read byte values (E3).

**`ub`** (§3.7) in this dialect: U1a/U1b (`State.range`), U2b (`State.load`), U2c
(`trunc_nuw`), U5a (`evm_mload_bytes` with `len > 32`).  U2a, U4a–U4c are about objects, enums
and annotations, which this dialect does not have or H does not read (U4a).

**Not in H** (§3.6): `evm_msize`, `get_function_ptr`, generic `udiv`/`sdiv`/`umod`/`smod`
(outside the subset on EVM), aggregates: each is `stuck`.  `unreachable` and `evm_invalid`
trap; EVM division is total, as the model library's `BinOp.eval` computes it.
-/

namespace Fe.Sonatina.H

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/-- How a run of handover IR ends (§7.2).  There is no divergence outcome: a run that does not
    end has no derivation. -/
inductive Outcome where
  /-- It returns or exits.  The world's memory field is irrelevant: `EndsAs` ignores it. -/
  | ends (r : Except (Exit World) (ByteArray × World))
  /-- It breaks a promise of the frontend (§3.7). -/
  | ub
  /-- Its heap requests reach `2 ^ 255` bytes (§3.3). -/
  | exhausted

/-- The values a function has defined. -/
abbrev HEnv := Std.TreeMap Nat Val

/-- What an instruction needs besides its operands: the offset and size of each symbol of the
    section, and the module's struct types, for the sizes of `alloca` and `gep`. -/
structure Ctx where
  symbol : String → Option (Nat × Nat)
  structs : List (String × List Ty)

/-- How an instruction ends. -/
inductive IRes where
  /-- It gives these values, in this state. -/
  | ok (vals : List Val) (st : State)
  /-- It ends the run (`Exit World`): a static violation, a read past the return data, a
      callee's stop. -/
  | exit (e : Exit World)
  | ub
  /-- H does not define it: no derivation. -/
  | stuck (why : String)

def evalOp (env : HEnv) : Operand → Option Val
  | .var id => env[id]?
  | .imm bits value => some (.int bits value)

/-- The generic divisions, outside the certified subset on EVM (§3.6). -/
def _root_.Fe.Sonatina.BinOp.generic : BinOp → Bool
  | .udiv | .sdiv | .umod | .smod => true
  | _ => false

/-- A binary operation with a pointer `ptr b o` and an integer `k`, the pointer first if
    `ptrFirst`, that keeps the pointer's origin (§3.2), if it is one. -/
def ptrBin (op : BinOp) (b o k : Nat) (ptrFirst : Bool) : Option Val :=
  match op with
  | .add => some (.ptr b ((o + k) % 2 ^ 256))
  | .sub => if ptrFirst then some (.ptr b ((o + (2 ^ 256 - k % 2 ^ 256)) % 2 ^ 256)) else none
  | .or | .xor => if k = 0 then some (.ptr b o) else none
  | .and => if k = 2 ^ 256 - 1 then some (.ptr b o) else none
  | _ => none

/-- A binary operation (§3.2): on integers of one width as the machine IR's interpreter computes
    it; with a pointer operand (both 256 bits), the origin-keeping forms of `ptrBin`, else on
    the words, to an integer.  `none` for operands of different widths and for the generic
    divisions. -/
def binVal (st : State) (op : BinOp) (x y : Val) : Option Val :=
  if op.generic || x.bits != y.bits then none
  else match x, y with
    | .int bits a, .int _ b => some (.int bits (op.eval bits a b))
    | .ptr b o, .int _ k => (ptrBin op b o k true).getD (.int 256 (op.eval 256 (st.word x) k))
    | .int _ k, .ptr b o => (ptrBin op b o k false).getD (.int 256 (op.eval 256 k (st.word y)))
    | .ptr .., .ptr .. => some (.int 256 (op.eval 256 (st.word x) (st.word y)))

/-- A cast (§3.2): `ptr_to_int` to `i256`, `int_to_ptr` and `bitcast` to a pointer type keep a
    pointer; an integer `int_to_ptr` or `bitcast` to a pointer type is the 256-bit integer of
    its value; every other cast is on the word, as `CastOp.eval` computes it, to an integer of
    the target's width.  A `bitcast` between integer types truncates or zero-extends, as
    Sonatina's interpreter (`Immediate::bitcast`) and machine lowering (`lower_bitcast`) do.
    `none` for a target that is not a scalar. -/
def castVal (st : State) (op : CastOp) (x : Val) (ty : Ty) : Option Val :=
  let bits := ty.bits
  if bits == 0 then none
  else match op, x, ty with
    | .ptrToInt, .ptr .., .int 256 => some x
    | .intToPtr, .ptr .., .ptr _ => some x
    | .bitcast, .ptr .., .ptr _ => some x
    | .intToPtr, .int _ v, .ptr _ | .bitcast, .int _ v, .ptr _ => some (.int 256 v)
    | op, x, _ => some (.int bits (op.eval x.bits (st.word x) bits))

/-- The offset a `gep` adds, from the type `ty` it steps through and its indices (§3.2):
    through a pointer or an array, the index times the element's size; through a struct, the
    sizes of the fields before the index.  `none` through a scalar, out of a struct's fields,
    or for a size `sizeOf` does not give.  Indices are read as unsigned words, as machine
    lowering reads a dynamic one (`lower_gep`). -/
def gepOffset (structs : List (String × List Ty)) (word : Val → Nat) : Ty → List Val → Option Nat
  | _, [] => some 0
  | .ptr elem, i :: rest | .array elem _, i :: rest => do
    let size ← sizeOf structs sizeFuel elem
    let off ← gepOffset structs word elem rest
    return word i * size + off
  | .struct name, i :: rest => do
    let fields ← structs.lookup name
    let k := word i
    let field ← fields[k]?
    let before ← (fields.take k).foldlM (fun acc t => (acc + ·) <$> sizeOf structs sizeFuel t) 0
    let off ← gepOffset structs word field rest
    return before + off
  | _, _ :: _ => none

/-- The EVM operations that touch no memory: the machine IR's interpreter runs them
    (`EvmOp.run`), and so does H. -/
def _root_.Fe.Sonatina.EvmOp.memFree : EvmOp → Bool
  | .mload | .mstore | .mstore8 | .keccak256 | .mcopy | .log _ | .calldataCopy | .codeCopy
  | .extCodeCopy | .returnDataCopy | .create | .create2 | .call | .staticCall | .delegateCall
  | .callCode | .msize => false
  | _ => true

/-- A value of the machine IR's interpreter as one of H: an integer. -/
def ofSonatina : Sonatina.Val → Option Val
  | .int bits v => some (.int bits v)
  | .agg _ => none

/-- Run a computation of the model library on the state's world: it ends the run, or `k`
    continues from its result. -/
def liftFe {α : Type} (I : ExecutionEnv) (st : State) (m : FeM α) (k : α → State → IRes) :
    IRes :=
  match m.exec I st.world with
  | none => .stuck "a run of the model library that does not terminate"
  | some (.error e) => .exit e
  | some (.ok (a, w)) => k a { st with world := w }

/-- A message call of H: its input read from `ar` (`al` bytes), its output written at `rr`, the
    ranges already resolved (§3.4); the model library's call between, as `fe` builds it from
    `messageCore`. -/
def callH (I : ExecutionEnv) (st : State) (ar : Range) (al : Nat) (rr : Range) (rl : UInt256)
    (fe : ByteArray → FeM (UInt256 × ByteArray)) : IRes :=
  liftFe I st (fe (st.bytes ar al)) fun (z, o) st =>
    .ok [.int 256 z.toNat] (st.writeBytes rr (o.extract 0 (retCount rl o)))

/-- An EVM operation of H on its operand values (§3.4, §3.6). -/
def evmH (I : ExecutionEnv) (st : State) (op : EvmOp) (args : List Val) : IRes :=
  let w := st.word
  let uw := st.uword
  let some' {α : Type} (o : Option α) (k : α → IRes) : IRes := match o with
    | some a => k a
    | none => .ub
  if op.memFree then
    liftFe I st (op.run (args.map uw)) fun vals st =>
      match vals.mapM ofSonatina with
      | some vs => .ok vs st
      | none => .stuck "an aggregate result"
  else match op, args with
  | .mload, [a] => some' (st.range a 32) fun
      | .at b o => some' (st.load b o (.int 256)) fun v => .ok [v] st
      | .empty => .ub
  | .mstore, [a, v] => some' (st.range a 32) fun r => .ok [] (st.write r v.cells)
  | .mstore8, [p, v] => some' (st.range p 1) fun r =>
      .ok [] (st.writeBytes r ⟨#[UInt8.ofNat (w v)]⟩)
  | .keccak256, [p, l] => some' (st.range p (w l)) fun r =>
      .ok [.int 256 (fromByteArrayBigEndian (KEC (st.bytes r (w l))) % 2 ^ 256)] st
  | .mcopy, [d, s, l] => some' (st.range d (w l)) fun rd => some' (st.range s (w l)) fun rs =>
      .ok [] (st.write rd (st.cells rs (w l)))
  | .log _, p :: l :: topics => some' (st.range p (w l)) fun r =>
      liftFe I st (emit (topics.map uw).toArray (st.bytes r (w l))) fun _ st => .ok [] st
  | .calldataCopy, [d, o, l] => some' (st.range d (w l)) fun r =>
      .ok [] (st.writeBytes r (I.calldata.readWithPadding (w o) (w l)))
  | .codeCopy, [d, o, l] => some' (st.range d (w l)) fun r =>
      .ok [] (st.writeBytes r (I.code.readWithPadding (w o) (w l)))
  | .extCodeCopy, [a, d, o, l] => some' (st.range d (w l)) fun r =>
      let code := st.world.accounts.get? (AccountAddress.ofUInt256 (uw a))
        |>.option ByteArray.empty (fun (acc : Account) => acc.code)
      .ok [] (st.writeBytes r (code.readWithPadding (w o) (w l)))
  | .returnDataCopy, [d, o, l] => some' (st.range d (w l)) fun r =>
      if w o + w l > st.world.returnData.size then .exit .oob
      else .ok [] (st.writeBytes r (st.world.returnData.readWithPadding (w o) (w l)))
  | .create, [v, p, l] => some' (st.range p (w l)) fun r =>
      liftFe I st (createCore none (uw v) (st.bytes r (w l))) fun a st => .ok [.int 256 a.toNat] st
  | .create2, [v, p, l, s] => some' (st.range p (w l)) fun r =>
      liftFe I st (createCore (some (uw s).toByteArray) (uw v) (st.bytes r (w l))) fun a st =>
        .ok [.int 256 a.toNat] st
  | .call, [g, a, v, ap, al, rp, rl] =>
    some' (st.range ap (w al)) fun ar => some' (st.range rp (w rl)) fun rr =>
      callH I st ar (w al) rr (uw rl) fun input => do
        let I ← read
        if I.perm = false ∧ uw v ≠ ⟨0⟩ then Fe.M.fail .static
        else
          let t := AccountAddress.ofUInt256 (uw a)
          messageCore (uw g) I.codeOwner t t (uw v) (uw v) input I.perm
  | .staticCall, [g, a, ap, al, rp, rl] =>
    some' (st.range ap (w al)) fun ar => some' (st.range rp (w rl)) fun rr =>
      callH I st ar (w al) rr (uw rl) fun input => do
        let I ← read
        let t := AccountAddress.ofUInt256 (uw a)
        messageCore (uw g) I.codeOwner t t (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) input false
  | .delegateCall, [g, a, ap, al, rp, rl] =>
    some' (st.range ap (w al)) fun ar => some' (st.range rp (w rl)) fun rr =>
      callH I st ar (w al) rr (uw rl) fun input => do
        let I ← read
        messageCore (uw g) I.source I.codeOwner (AccountAddress.ofUInt256 (uw a)) (⟨0⟩ : UInt256) I.weiValue
          input I.perm
  | .callCode, [g, a, v, ap, al, rp, rl] =>
    some' (st.range ap (w al)) fun ar => some' (st.range rp (w rl)) fun rr =>
      callH I st ar (w al) rr (uw rl) fun input => do
        let I ← read
        messageCore (uw g) I.codeOwner I.codeOwner (AccountAddress.ofUInt256 (uw a)) (uw v)
          (uw v) input I.perm
  | .msize, _ => .stuck "evm_msize is not in H (E4)"
  | _, _ => .stuck "an EVM operation with the wrong operands"

/-- Run an instruction other than `alloca`, `evm_malloc` and `call` (which the relation runs):
    the values it gives and the state after it, or how the run ends. -/
def stepInst (c : Ctx) (I : ExecutionEnv) (env : HEnv) (st : State) : HInst → IRes
  | .base i =>
    let op (o : Operand) (k : Val → IRes) : IRes := match evalOp env o with
      | some v => k v
      | none => .stuck "an operand with no value"
    let opt (o : Option Val) : IRes := match o with
      | some v => .ok [v] st
      | none => .stuck "ill-typed operands"
    let w := st.word
    match i with
    | .bin bop a b => op a fun x => op b fun y => opt (binVal st bop x y)
    | .cmp cop a b => op a fun x => op b fun y =>
      if x.bits == y.bits then .ok [.int 1 (if cop.eval x.bits (w x) (w y) then 1 else 0)] st
      else .stuck "ill-typed operands"
    | .isZero a => op a fun x => .ok [.int 1 (if w x == 0 then 1 else 0)] st
    | .not a => op a fun x => .ok [.int x.bits (2 ^ x.bits - 1 - w x)] st
    | .neg a => op a fun x => .ok [.int x.bits (wrap x.bits (-(w x : Int)))] st
    | .clz a => op a fun x =>
      if I.header.fork = .Osaka then
        .ok [.int x.bits (if w x = 0 then x.bits else x.bits - 1 - (w x).log2)] st
      else .exit .trap
    | .ctz a => op a fun x =>
      .ok [.int x.bits (((List.range x.bits).find? (w x).testBit).getD x.bits)] st
    | .ovf oop a b => op a fun x => op b fun y =>
      if x.bits == y.bits then
        let (r, f) := oop.eval x.bits (w x) (w y)
        .ok [.int x.bits r, .int 1 (if f then 1 else 0)] st
      else .stuck "ill-typed operands"
    | .sat sop a b ty => op a fun x => op b fun y => .ok [.int 256 (sop.eval ty.bits (w x) (w y))] st
    | .cast cop a ty => op a fun x => opt (castVal st cop x ty)
    | .select cnd a b => op cnd fun x => op (if w x != 0 then a else b) fun v => .ok [v] st
    | .evm eop args => match args.mapM (evalOp env) with
      | some vs => evmH I st eop vs
      | none => .stuck "an operand with no value"
    | .mload a ty => op a fun x =>
      if Ty.scalar ty then match st.range x 32 with
        | some (.at b o) => match st.load b o ty with
          | some v => .ok [v] st
          | none => .ub
        | _ => .ub
      else .stuck "a load of a type that is not a scalar"
    | .mstore a v ty => op a fun x => op v fun y =>
      if Ty.scalar ty && y.fits ty then match st.range x 32 with
        | some r => .ok [] (st.write r y.cells)
        | none => .ub
      else .stuck "a store of a type that is not a scalar, or of a value not of its type"
    | .memzero d l => op d fun x => op l fun n => match st.range x (w n) with
      | some r => .ok [] (st.writeBytes r ⟨Array.replicate (w n) 0⟩)
      | none => .ub
    | .symAddr s => match c.symbol s with
      | some (offset, _) => .ok [.int 256 offset] st
      | none => .stuck "a symbol the section does not have"
    | .symSize s => match c.symbol s with
      | some (_, size) => .ok [.int 256 size] st
      | none => .stuck "a symbol the section does not have"
    | .blackBox a => op a fun x => .ok [x] st
    | .keccakWords ws => match ws.mapM (evalOp env) with
      | some vs => .ok [.int 256 (keccakOfWords (vs.map st.uword)).toNat] st
      | none => .stuck "an operand with no value"
    | .funcPtr _ => .stuck "get_function_ptr is not in H"
    | .malloc _ | .alloca _ | .call _ _ => .stuck "an allocation or call outside the relation"
    | .insertValue .. | .extractValue .. => .stuck "an aggregate"
  | .gep baseTy base idxs =>
    match evalOp env base, idxs.mapM (evalOp env) with
    | some b, some is => match gepOffset c.structs st.word baseTy is, baseTy with
      | some off, .ptr _ => match b with
        | .ptr blk o => .ok [.ptr blk ((o + off) % 2 ^ 256)] st
        | .int _ n => .ok [.int 256 ((n + off) % 2 ^ 256)] st
      | _, _ => .stuck "a gep H does not define"
    | _, _ => .stuck "an operand with no value"
  | .mloadBytes a l =>
    match evalOp env a, evalOp env l with
    | some x, some n =>
      let len := st.word n
      if len > 32 then .ub
      else if len = 0 then .ok [.int 256 0] st
      else match st.range x len with
        | some r => .ok [.int 256 (fromByteArrayBigEndian (st.bytes r len))] st
        | none => .ub
    | _, _ => .stuck "an operand with no value"
  | .truncNuw a ty =>
    match evalOp env a with
    | some x =>
      if ty.bits == 0 then .stuck "trunc_nuw to a type that is not an integer"
      else if st.word x < 2 ^ ty.bits then .ok [.int ty.bits (st.word x)] st else .ub
    | none => .stuck "an operand with no value"

/-- How a terminator ends a block. -/
inductive TRes where
  | goto (dest : Nat)
  | ret (vals : List Val)
  | halt (o : Outcome)
  | stuck (why : String)

/-- Run a terminator (§3.6). -/
def stepTerm (I : ExecutionEnv) (env : HEnv) (st : State) : HTerm → TRes
  | .base t =>
    let w := st.word
    let data (a l : Operand) (k : ByteArray → TRes) : TRes :=
      match evalOp env a, evalOp env l with
      | some x, some n => match st.range x (w n) with
        | some r => k (st.bytes r (w n))
        | none => .halt .ub
      | _, _ => .stuck "an operand with no value"
    match t with
    | .jump d => .goto d
    | .br c nz z => match evalOp env c with
      | some x => .goto (if w x != 0 then nz else z)
      | none => .stuck "an operand with no value"
    | .brTable s d cases => match evalOp env s, cases.mapM fun (o, b) => (evalOp env o).map (w ·, b) with
      | some x, some vals => match (vals.find? (·.1 == w x)).map (·.2) <|> d with
        | some dest => .goto dest
        | none => .stuck "a br_table with no case for its scrutinee and no default"
      | _, _ => .stuck "an operand with no value"
    | .ret vs => match vs.mapM (evalOp env) with
      | some vals => .ret vals
      | none => .stuck "an operand with no value"
    | .evmReturn a l => data a l fun d => .halt (.ends (.error (.stop d st.world)))
    | .evmRevert a l => data a l fun d => .halt (.ends (.error (.revert d)))
    | .evmStop => .halt (.ends (.error (.stop .empty st.world)))
    | .evmInvalid | .unreachable => .halt (.ends (.error .trap))
    | .evmSelfDestruct a => match evalOp env a with
      | some x => match (Fe.EVM.selfdestruct (st.uword x)).exec I st.world with
        | some (.error e) => .halt (.ends (.error e))
        | some (.ok (e, _)) => nomatch e
        | none => .stuck "a run of the model library that does not terminate"
      | none => .stuck "an operand with no value"
  | .returnCode o l => match evalOp env o, evalOp env l with
    | some x, some n =>
      .halt (.ends (.error (.stop (I.code.readWithPadding (st.word x) (st.word n)) st.world)))
    | _, _ => .stuck "an operand with no value"

end Fe.Sonatina.H
