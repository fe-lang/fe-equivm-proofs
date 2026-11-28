import Fe.Sonatina.Stage3.Place.Record
import Fe.Sonatina.H.Wf

/-!
# The translation of S14 (design §5.1)

Machine lowering (`isa/evm/machine/lower.rs`) turns each source instruction into zero or more
machine statements, and each source value into a machine operand: a machine value, or an
immediate (an `alloca`'s address, a fixed buffer's base, a `gep` folded onto one).  This file
states what lowering may produce, as a walk over a source block and the machine statements of
its region:

- `walk` matches each source statement, in order, against the next machine statements, under a
  value map `vm` (source value ↦ machine operand) and the placement record.  A region is
  usually one machine block; the dynamic `evm_mload_bytes` and the heap base clamp end it in a
  diamond and continue in the join block.  The walk returns the machine block the source block's
  terminator is in.
- `phisOk`, `termOk`: phis entry by entry (the incoming block of a source predecessor is the
  block its region ends in), terminators slot by slot.

The walk runs in two modes.  Checking (`chk = true`), it changes nothing: every binding it would
make must already be in `vm`.  Inferring (`chk = false`), it adds them; `inferVm` runs it over the
blocks until every block has been walked, and its result is then checked.  Only the checking
walk is trusted.

**Typing.** H is stuck where an operand or a result does not have the type it is declared with
(`bindVals`, I10), while the machine IR coerces every value to a word.  So each pattern also
checks, from the source declarations, that H's step is defined on values of the declared types
(`FCtx.tyOf`, `sameW`), and each narrow operation is accepted only where H's semantics at its
width equals the machine's at 256 bits on the values of that width (PLAN F9): at `i1`, `and`,
`or`, `xor`, `is_zero`, `eq`, `ne` and the unsigned comparisons.

**Patterns** (`lower.rs`): see `stmt`.  Not accepted, each a rejection: `select`, generic
division, `get_function_ptr`, `evm_msize`, aggregates, `evm_keccak256_words`, a transient or
exact-base heap malloc (rule S2's first-stage switch), a default-less `br_table` (H has no rule
for a miss on a word), narrow operations other than those above.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps

/-- Source value ↦ machine operand. -/
abbrev VM := NatMap Operand

/-- What the walk of one function needs. -/
structure FCtx where
  prec : Record
  frec : FuncRec
  /-- The section's source module: struct types (layout) and callee signatures. -/
  src : HModule
  /-- The section's symbols. -/
  symbols : List (String × Nat × Nat)
  /-- The declared type of each source value. -/
  decls : NatMap Ty
  /-- Source block ↦ the machine block its region starts in. -/
  bm : NatMap Nat
  /-- The machine function. -/
  mf : Func

/-- The type of an operand: its declaration, or an immediate's width (with its value in range). -/
def FCtx.tyOf (c : FCtx) : Operand → Option Ty
  | .var x => c.decls.find? x
  | .imm bits v => if widths.contains bits && decide (v < 2 ^ bits) then some (.int bits) else none

/-- Two value types of one width: a value of one is a value of the other (`Val.fits` depends on
    the width only). -/
def sameW (t u : Ty) : Bool := Ty.value t && Ty.value u && t.bits == u.bits

/-- A word type: `i256` or a pointer. -/
def isWord (t : Ty) : Bool := Ty.value t && t.bits == 256

/-- The machine operand of a source operand: an immediate is the word of its value (machine
    lowering zero-extends, `lower_immediate`). -/
def mop (vm : VM) : Operand → Option Operand
  | .var x => vm.find? x
  | .imm _ v => some (.imm 256 v)

/-- Record that source value `x` is machine operand `o`; checking, that it is. -/
def bindV (chk : Bool) (vm : VM) (x : Nat) (o : Operand) : Option VM :=
  if chk then (if vm.find? x == some o then some vm else none) else some (vm.insert x o)

def w256 : Ty := .int 256
def imm (v : Nat) : Operand := .imm 256 v

/-- The next machine statement is `inst` with one word result: its id. -/
def take1 (inst : Inst) : List Stmt → Option (Nat × List Stmt)
  | ⟨[(r, .int 256)], i⟩ :: rest => if i == inst then some (r, rest) else none
  | _ => none

/-- The next machine statement is `inst` with no result. -/
def take0 (inst : Inst) : List Stmt → Option (List Stmt)
  | ⟨[], i⟩ :: rest => if i == inst then some rest else none
  | _ => none

/-- The next machine statement is `inst` with `n` word results: their ids. -/
def takeN (inst : Inst) (n : Nat) : List Stmt → Option (List Nat × List Stmt)
  | ⟨ds, i⟩ :: rest =>
    if i == inst && ds.length == n && ds.all (·.2 == w256) then some (ds.map (·.1), rest) else none
  | _ => none

/-- The comparison machine lowering emits for `le`, `ge`, `sle`, `sge`, `ne`, whose result it
    negates with `is_zero`. -/
def _root_.Fe.Sonatina.CmpOp.inverse : CmpOp → Option CmpOp
  | .le => some .gt
  | .ge => some .lt
  | .sle => some .sgt
  | .sge => some .slt
  | .ne => some .eq
  | _ => none

/-- Binary operations accepted at `i1`: their H semantics at width 1 is the machine's at 256 bits
    on 0 and 1. -/
def _root_.Fe.Sonatina.BinOp.okI1 : BinOp → Bool
  | .and | .or | .xor => true
  | _ => false

/-- Comparisons accepted on `i1` operands (unsigned, or equality). -/
def _root_.Fe.Sonatina.CmpOp.okI1 : CmpOp → Bool
  | .eq | .ne | .lt | .gt | .le | .ge => true
  | _ => false

/-- The result of a walk step: the value map, the machine block and its statements still to
    match, and the machine values the step defined. -/
abbrev Step := VM × Nat × List Stmt × List Nat

/-- A block holding no phi and no statement that jumps to `dest`. -/
def jumpOnly (b : Block) (dest : Nat) : Bool :=
  b.phis.isEmpty && b.body.isEmpty && b.term == .jump dest

/-- The address a `gep` computes, as lowering folds it (`lower_gep`): constant offsets
    accumulate (`k`); a dynamic index `i` of an element of `e ≠ 0` bytes flushes them
    (`add addr k`) and adds `mul i e`; at the end a nonzero `k` is added.  Returns the operand of
    the address, the statements left and the machine values defined. -/
def gepWalk (c : FCtx) (vm : VM) :
    Operand → Nat → Ty → List Operand → List Stmt → Option (Operand × List Stmt × List Nat)
  | addr, k, _, [], ms =>
    if k == 0 then some (addr, ms, [])
    else do
      let (r, ms) ← take1 (.bin .add addr (imm k)) ms
      some (.var r, ms, [r])
  | addr, k, .ptr elem, i :: rest, ms | addr, k, .array elem _, i :: rest, ms => do
    let size ← sizeOf c.src.structs sizeFuel elem
    match i with
    | .imm _ v => gepWalk c vm addr (k + size * v) elem rest ms
    | .var _ =>
      if size == 0 then gepWalk c vm addr k elem rest ms
      else do
        let (addr1, ms1, d1) ← (if k == 0 then some (addr, ms, [])
          else do
            let (r, ms') ← take1 (.bin .add addr (imm k)) ms
            some (.var r, ms', [r]))
        let i' ← mop vm i
        let (s, ms2) ← take1 (.bin .mul i' (imm size)) ms1
        let (a2, ms3) ← take1 (.bin .add addr1 (.var s)) ms2
        let (r, ms4, d4) ← gepWalk c vm (.var a2) 0 elem rest ms3
        some (r, ms4, d1 ++ [s, a2] ++ d4)
  | addr, k, .struct name, .imm _ idx :: rest, ms => do
    let fields ← c.src.structs.lookup name
    let field ← fields[idx]?
    let before ← (fields.take idx).foldlM (fun acc t => (acc + ·) <$> sizeOf c.src.structs sizeFuel t) 0
    gepWalk c vm addr (k + before) field rest ms
  | _, _, _, _ :: _, _ => none

/-- The machine statements of a heap malloc's size, aligned to words (`lower_malloc_aligned_size`):
    an immediate below `2 ^ 32` is aligned by lowering; any other size is `add n 31; and _ -32`. -/
def mallocSize (vm : VM) (a : Operand) (ms : List Stmt) : Option (Operand × List Stmt × List Nat) :=
  match a with
  | .imm _ n =>
    if n < 2 ^ 32 then some (imm (align32 n), ms, []) else dyn
  | .var _ => dyn
where
  dyn : Option (Operand × List Stmt × List Nat) := do
    let a' ← mop vm a
    let (t, ms) ← take1 (.bin .add a' (imm 31)) ms
    let (sz, ms) ← take1 (.bin .and (.var t) (imm (2 ^ 256 - 32))) ms
    some (.var sz, ms, [t, sz])

/-- The cast machine lowering makes of `cast op a ty` from type `ta`: the operand itself, or its
    low `k` bits (`and a (2^k - 1)`).  From `i1` a `zext`, `trunc`, `bitcast` or `int_to_ptr` is
    the operand; otherwise the width kept is the smaller of the two (`lower_zext_or_trunc`,
    `lower_bitcast`, `lower_ptr_to_int`, `lower_int_to_ptr`).  `sext` is not accepted (none in
    the corpus). -/
def castKeep (op : CastOp) (ta ty : Ty) : Option Nat :=
  match op with
  | .sext => none
  | _ => if ta == .int 1 && op != .ptrToInt then some 256 else some (min ta.bits ty.bits)

/-- Match one source statement against the machine statements `ms` of machine block `mb`.
    Its typing conditions are those under which H's step is defined on values of the declared
    types. -/
def stmt (c : FCtx) (chk : Bool) (vm : VM) (s : HStmt) (mb : Nat) (ms : List Stmt)
    (callee? : Option Nat) : Option Step := do
  let ty := c.tyOf
  let one (x : Nat) (_tx : Ty) (inst : Inst) (ok : Bool) : Option Step := do
    unless ok do none
    let (r, ms) ← take1 inst ms
    let vm ← bindV chk vm x (.var r)
    some (vm, mb, ms, [r])
  match s.inst, s.dsts with
  -- Structural instructions (`lower_structural`): the same instruction on mapped operands.
  | .base (.bin op a b), [(x, tx)] => do
    let (ta, tb) := (← ty a, ← ty b)
    let ok := sameW ta tb && !op.generic && (ta.bits == 256 || ta.bits == 1 && op.okI1) &&
      sameW tx ta
    one x tx (.bin op (← mop vm a) (← mop vm b)) ok
  | .base (.cmp op a b), [(x, tx)] => do
    let (ta, tb) := (← ty a, ← ty b)
    unless sameW ta tb && (ta.bits == 256 || ta.bits == 1 && op.okI1) && tx == .int 1 do none
    let (a', b') := (← mop vm a, ← mop vm b)
    match op.inverse with
    | some inv => do
      let (t, ms) ← take1 (.cmp inv a' b') ms
      let (r, ms) ← take1 (.isZero (.var t)) ms
      let vm ← bindV chk vm x (.var r)
      some (vm, mb, ms, [t, r])
    | none => one x tx (.cmp op a' b') true
  | .base (.isZero a), [(x, tx)] => do
    unless Ty.value (← ty a) do none
    one x tx (.isZero (← mop vm a)) (tx == .int 1)
  | .base (.not a), [(x, tx)] => do
    one x tx (.not (← mop vm a)) (isWord (← ty a) && isWord tx)
  | .base (.neg a), [(x, tx)] => do
    one x tx (.neg (← mop vm a)) (isWord (← ty a) && isWord tx)
  | .base (.clz a), [(x, tx)] => do
    one x tx (.clz (← mop vm a)) (isWord (← ty a) && isWord tx)
  | .base (.ctz a), [(x, tx)] => do
    one x tx (.ctz (← mop vm a)) (isWord (← ty a) && isWord tx)
  | .base (.ovf op a b), [(x, tx), (y, tyy)] => do
    unless isWord (← ty a) && isWord (← ty b) && isWord tx && tyy == .int 1 do none
    let (rs, ms) ← takeN (.ovf op (← mop vm a) (← mop vm b)) 2 ms
    let [r1, r2] := rs | none
    let vm ← bindV chk vm x (.var r1)
    let vm ← bindV chk vm y (.var r2)
    some (vm, mb, ms, [r1, r2])
  | .base (.sat op a b t), [(x, tx)] => do
    unless Ty.value (← ty a) && Ty.value (← ty b) && (t matches .int _) && Ty.value t do none
    one x tx (.sat op (← mop vm a) (← mop vm b) t) (isWord tx)
  | .base (.cast op a t), [(x, tx)] => do
    let ta ← ty a
    unless Ty.value ta && Ty.value t && sameW tx t do none
    let k ← castKeep op ta t
    let a' ← mop vm a
    if k == 256 then do
      let vm ← bindV chk vm x a'
      some (vm, mb, ms, [])
    else one x tx (.bin .and a' (imm (2 ^ k - 1))) true
  | .base (.blackBox a), [(x, tx)] => do
    one x tx (.blackBox (← mop vm a)) (sameW (← ty a) tx)
  -- The symbol's offset (size) is bound as a word: H is stuck on one of `2 ^ 256` or more, where
  -- the machine wraps it (review 25, H1).
  | .base (.symAddr sym), [(x, tx)] => do
    let (off, _) ← c.symbols.lookup sym
    one x tx (.symAddr sym) (isWord tx && decide (off < 2 ^ 256))
  | .base (.symSize sym), [(x, tx)] => do
    let (_, sz) ← c.symbols.lookup sym
    one x tx (.symSize sym) (isWord tx && decide (sz < 2 ^ 256))
  | .base (.evm op args), dsts => do
    let (nArgs, nRes) ← op.arity
    unless op != .msize && args.length == nArgs && dsts.length == nRes &&
        dsts.all (isWord ·.2) && (args.all fun a => (ty a).any Ty.value) do none
    let args' ← args.mapM (mop vm)
    let (rs, ms) ← takeN (.evm op args') nRes ms
    let vm ← (dsts.zip rs).foldlM (fun vm (d, r) => bindV chk vm d.1 (.var r)) vm
    some (vm, mb, ms, rs)
  -- Memory.
  | .base (.mload a t), [(x, tx)] => do
    unless Ty.value t && sameW tx t && (ty a).any Ty.value do none
    one x tx (.evm .mload [← mop vm a]) true
  | .base (.mstore a v t), [] => do
    unless Ty.value t && sameW (← ty v) t && (ty a).any Ty.value do none
    let ms ← take0 (.evm .mstore [← mop vm a, ← mop vm v]) ms
    some (vm, mb, ms, [])
  | .base (.memzero d l), [] => do
    unless (ty d).any Ty.value && (ty l).any Ty.value do none
    let (sz, ms) ← take1 (.evm .calldataSize []) ms
    let ms ← take0 (.evm .calldataCopy [← mop vm d, .var sz, ← mop vm l]) ms
    some (vm, mb, ms, [sz])
  | .mloadBytes a l, [(x, tx)] => do
    unless isWord tx && (ty a).any Ty.value && (ty l).any Ty.value do none
    let a' ← mop vm a
    match l with
    | .imm _ 0 => do
      let vm ← bindV chk vm x (imm 0)
      some (vm, mb, ms, [])
    | .imm _ n =>
      if 32 ≤ n then one x tx (.evm .mload [a']) true
      else do
        let (w, ms) ← take1 (.evm .mload [a']) ms
        let (r, ms) ← take1 (.bin .shr (imm ((32 - n) * 8)) (.var w)) ms
        let vm ← bindV chk vm x (.var r)
        some (vm, mb, ms, [w, r])
    | .var _ => do
      -- The diamond (`lower_mload_bytes`): `br len load join`; `load` reads the word and shifts
      -- it; `join` takes 0 or the shifted word.
      unless ms.isEmpty do none
      let l' ← mop vm l
      let cur ← c.mf.block? mb
      let .br cnd ld jn := cur.term | none
      unless cnd == l' do none
      let lb ← c.mf.block? ld
      let (w, r1) ← take1 (.evm .mload [a']) lb.body
      let (t1, r2) ← take1 (.bin .shl (imm 3) l') r1
      let (t2, r3) ← take1 (.bin .sub (imm 256) (.var t1)) r2
      let (sh, r4) ← take1 (.bin .shr (.var t2) (.var w)) r3
      unless r4.isEmpty && lb.phis.isEmpty && lb.term == .jump jn do none
      let jb ← c.mf.block? jn
      let [φ] := jb.phis | none
      unless φ.ty == w256 && φ.incoming == [(imm 0, mb), (.var sh, ld)] do none
      let vm ← bindV chk vm x (.var φ.dst)
      some (vm, jn, jb.body, [w, t1, t2, sh, φ.dst])
  | .truncNuw a t, [(x, tx)] => do
    unless Ty.value (← ty a) && (t matches .int _) && Ty.value t && sameW tx t do none
    let vm ← bindV chk vm x (← mop vm a)
    some (vm, mb, ms, [])
  | .gep bt base idxs, [(x, tx)] => do
    unless (bt matches .ptr _) && isWord tx && (ty base).any isWord &&
        (idxs.all fun i => (ty i).any Ty.value) do none
    let (addr, ms, ds) ← gepWalk c vm (← mop vm base) 0 bt idxs ms
    let vm ← bindV chk vm x addr
    some (vm, mb, ms, ds)
  -- Allocation.
  | .base (.alloca t), [(x, tx)] => do
    unless (sizeOf c.src.structs sizeFuel t).isSome && isWord tx do none
    let loc ← c.frec.allocas.lookup x
    let vm ← bindV chk vm x (imm (c.prec.wordAddr loc.word))
    some (vm, mb, ms, [])
  | .base (.malloc a), [(x, tx)] => do
    unless isWord tx && (ty a).any Ty.value do none
    match ← c.frec.mallocs.lookup x with
    | .fixed base _ => do
      let vm ← bindV chk vm x (imm base)
      some (vm, mb, ms, [])
    | .heap minBase none true => do
      let (b0, ms) ← take1 (.evm .mload [imm 64]) ms
      -- The clamp `max(w[0x40], min_base)` (`emit_word_max_with_compare`), unless lowering
      -- dropped it: a diamond whose join takes the larger.
      let clamp : Option (Operand × Nat × List Stmt × List Nat) := do
        unless minBase != 0 do none
        let (cnd, ms1) ← take1 (.cmp .gt (.var b0) (imm (minBase - 1))) ms
        unless ms1.isEmpty do none
        let cur ← c.mf.block? mb
        let .br cv lb rb := cur.term | none
        let mlb ← c.mf.block? lb
        let mrb ← c.mf.block? rb
        let .jump jn := mlb.term | none
        unless cv == .var cnd && lb != rb && jumpOnly mlb jn && jumpOnly mrb jn do none
        let jb ← c.mf.block? jn
        let [φ] := jb.phis | none
        unless φ.ty == w256 && φ.incoming == [(.var b0, lb), (imm minBase, rb)] do none
        some (.var φ.dst, jn, jb.body, [cnd, φ.dst])
      let (base, mb, ms, dc) ← clamp <|> some (.var b0, mb, ms, [])
      let (sz, ms, ds) ← mallocSize vm a ms
      let (nf, ms) ← take1 (.bin .add base sz) ms
      let ms ← take0 (.evm .mstore [imm 64, .var nf]) ms
      let vm ← bindV chk vm x base
      some (vm, mb, ms, [b0] ++ dc ++ ds ++ [nf])
    | _ => none
  | .base (.call g args), dsts => do
    let callee ← c.src.funcs[← callee?]?
    unless callee.name == g do none
    let tas ← args.mapM ty
    unless tas.length == callee.params.length &&
        (tas.zip callee.params).all (fun (t, p) => sameW t p.2) &&
        dsts.length == callee.rets.length &&
        (dsts.zip callee.rets).all (fun (d, t) => sameW d.2 t) do none
    let args' ← args.mapM (mop vm)
    let (rs, ms) ← takeN (.call g args') dsts.length ms
    let vm ← (dsts.zip rs).foldlM (fun vm (d, r) => bindV chk vm d.1 (.var r)) vm
    some (vm, mb, ms, rs)
  | _, _ => none

/-- The machine blocks a step from block `mb` to block `mb'` enters: none if it stays, else the
    diamond's blocks (the successors of `mb`'s terminator) and its join `mb'`. -/
def entered (mf : Func) (mb mb' : Nat) : List Nat :=
  if mb == mb' then []
  else (((mf.block? mb).map (·.term.succs)).getD []).filter (· != mb') ++ [mb']

/-- Walk a source block's statements from the statements `ms` of machine block `mb`: the value
    map, the machine block the region ends in with its statements left (the terminator's
    expansion), the machine values each statement defined, and the machine blocks the region
    enters after its first (the diamonds' blocks). -/
def walk (c : FCtx) (chk : Bool) :
    VM → List HStmt → Nat → List Stmt → List Nat →
      Option (VM × Nat × List Stmt × List (List Nat) × List Nat)
  | vm, [], mb, ms, _ => some (vm, mb, ms, [], [])
  | vm, s :: rest, mb, ms, cs => do
    let (callee?, cs) := if s.inst matches .base (.call ..) then (cs.head?, cs.tail) else (none, cs)
    let (vm, mb', ms, ds) ← stmt c chk vm s mb ms callee?
    let (vm, tb, ms, dss, bs) ← walk c chk vm rest mb' ms cs
    some (vm, tb, ms, ds :: dss, entered c.mf mb mb' ++ bs)

/-- The machine terminator lowering makes of a source one (`lower_inst_active`): targets mapped
    by the block map, operands by the value map; a `br_table` with a default and no case is a
    `jump`.  A default-less `br_table` is not accepted: at this dialect its scrutinee is a word,
    on which H has no rule for a miss.  A `return`'s values must have the function's result
    types. -/
def mapTerm (c : FCtx) (vm : VM) (rets : List Ty) : Term → Option Term
  | .jump d => return .jump (← c.bm.find? d)
  | .br cnd nz z => do
    unless (c.tyOf cnd).any Ty.value do none
    return .br (← mop vm cnd) (← c.bm.find? nz) (← c.bm.find? z)
  | .brTable s (some d) cases => do
    unless (c.tyOf s).any Ty.value && cases.all (fun (o, _) => (c.tyOf o).any Ty.value) do none
    let d' ← c.bm.find? d
    let cases' ← cases.mapM fun (o, b) => return (← mop vm o, ← c.bm.find? b)
    if cases'.isEmpty then return .jump d'
    return .brTable (← mop vm s) (some d') cases'
  | .brTable _ none _ => none
  | .ret vs => do
    let ts ← vs.mapM c.tyOf
    unless ts.length == rets.length && (ts.zip rets).all (fun (t, r) => sameW t r) do none
    return .ret (← vs.mapM (mop vm))
  | .evmReturn a l => do
    unless (c.tyOf a).any Ty.value && (c.tyOf l).any Ty.value do none
    return .evmReturn (← mop vm a) (← mop vm l)
  | .evmRevert a l => do
    unless (c.tyOf a).any Ty.value && (c.tyOf l).any Ty.value do none
    return .evmRevert (← mop vm a) (← mop vm l)
  | .evmStop => return .evmStop
  | .evmInvalid => return .evmInvalid
  | .unreachable => return .unreachable
  | .evmSelfDestruct a => do
    unless (c.tyOf a).any Ty.value do none
    return .evmSelfDestruct (← mop vm a)

/-- The expansion of `evm_revert_word sel word` (decision 9.2, design §8 step 2b): the selector
    word stored at 0, `word` at 4, and a revert of the 36 bytes at 0, in the typed forms of the
    panic blocks before the terminator (`evm_mstore 0.i256 C.i256; evm_mstore 4.i256 word;
    evm_revert 0.i256 36.i256`).  The selector word `C` is the immediate `sel · 2 ^ 224` for an
    immediate `sel`, else the result of `shl 224 sel` just before the first store, which
    `word`'s machine operand is not.  `sel` is an `i32` (an immediate one below `2 ^ 32`) and
    `word` a word (PLAN F9): H reverts with the low four bytes of `sel`'s word (`revertWordData`),
    which are what `shl 224` keeps of the machine's. -/
def revertWordOk (c : FCtx) (vm : VM) (s w : Operand) (ms : List Stmt) (mt : Term) : Bool :=
  (do
    unless (c.tyOf s).any (sameW · (.int 32)) && (c.tyOf w).any isWord do none
    let w' ← mop vm w
    let rest ← match s with
      | .imm _ v => take0 (.evm .mstore [imm 0, imm (v * 2 ^ 224)]) ms
      | .var _ => do
        let s' ← mop vm s
        let (t, ms) ← take1 (.bin .shl (imm 224) s') ms
        unless w' != Operand.var t do none
        take0 (.evm .mstore [imm 0, Operand.var t]) ms
    let rest ← take0 (.evm .mstore [imm 4, w']) rest
    unless rest.isEmpty && mt == Term.evmRevert (imm 0) (imm 36) do none
    some ()).isSome

/-- The source terminator `t`, with the machine statements `ms` left in the region's last block,
    is lowered as the machine terminator `mt`: `evm_return_code o l` is `evm_code_copy 0 o l;
    evm_return 0 l` (`lower_return_code`), `evm_revert_word` is `revertWordOk`'s two stores and
    revert, every other terminator is `mapTerm`'s with nothing before it. -/
def termOk (c : FCtx) (vm : VM) (rets : List Ty) (t : HTerm) (ms : List Stmt) (mt : Term) :
    Bool :=
  match t with
  | .returnCode o l => (do
      unless (c.tyOf o).any Ty.value && (c.tyOf l).any Ty.value do none
      let (o', l') := (← mop vm o, ← mop vm l)
      let rest ← take0 (.evm .codeCopy [imm 0, o', l']) ms
      unless rest.isEmpty && mt == Term.evmReturn (imm 0) l' do none
      some ()).isSome
  | .revertWord s w => revertWordOk c vm s w ms mt
  | .base t => ms.isEmpty && mapTerm c vm rets t == some mt

/-- The list without repeats, its first occurrences kept last to first (structural, so that the
    kernel evaluates it; `List.eraseDups` is not). -/
def _root_.List.dedupB {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => let r := xs.dedupB; if r.contains x then r else x :: r

/-- `x` inserted in the ascending list, once. -/
def sortedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: sortedInsert x ys

/-- A set of naturals, ascending and without repeats (`Plan.normSet` sorts by `mergeSort`,
    which the kernel does not evaluate). -/
def nset (l : List Nat) : List Nat := l.foldr sortedInsert []

/-- The list has no repeated element. -/
def nodupB (l : List Nat) : Bool := l.dedupB.length == l.length

/-- The machine block's phis are the source block's, in order: each defines its source phi's
    machine value, as a word, and takes, from the block the region of each source predecessor
    ends in (`tb`), the mapped operand.  The source phi's operands have its type. -/
def phisOk (c : FCtx) (vm : VM) (tb : NatMap Nat) (ps mps : List Phi) : Bool :=
  ps.length == mps.length && (ps.zip mps).all fun (p, mp) =>
    vm.find? p.dst == some (.var mp.dst) && mp.ty == w256 && Ty.value p.ty &&
      (p.incoming.all fun (o, _) => (c.tyOf o).any (sameW · p.ty)) &&
      nodupB (p.incoming.map (·.2)) && nodupB (mp.incoming.map (·.2)) &&
      p.incoming.mapM (fun (o, b) => return (← mop vm o, ← tb.find? b)) == some mp.incoming

/-- The region of source block `b`: its machine start block, the walk of its statements, and its
    terminator; the machine block it ends in, the machine values each statement defined, and
    the machine blocks of the region, its start first. -/
def blockLower (c : FCtx) (chk : Bool) (vm : VM) (rets : List Ty) (b : HBlock) (cs : List Nat) :
    Option (VM × Nat × List (List Nat) × List Nat) := do
  let mb ← c.bm.find? b.id
  let mblk ← c.mf.block? mb
  let vm ← if chk then some vm else
    some ((b.phis.zip mblk.phis).foldl (fun vm (p, mp) => vm.insert p.dst (.var mp.dst)) vm)
  let (vm, tbk, ms, dss, bs) ← walk c chk vm b.body mb mblk.body cs
  let tblk ← c.mf.block? tbk
  unless termOk c vm rets b.term ms tblk.term do none
  some (vm, tbk, dss, mb :: bs)

/-- The source value of each declaration of `f`: parameters, phis, statement results. -/
def declsOf (f : HFunc) : NatMap Ty :=
  NatMap.ofList (f.params ++ f.blocks.flatMap fun b =>
    b.phis.map (fun p => (p.dst, p.ty)) ++ b.body.flatMap (·.dsts))

/-- The block map: the record's, or the `k`-th source block to machine block `k`, as machine
    lowering creates them (`create_source_blocks`). -/
def blockMapOf (fr : FuncRec) (f : HFunc) : NatMap Nat :=
  NatMap.ofList (fr.blockMap.getD (f.blocks.zipIdx.map fun (b, k) => (b.id, k)))

/-- The parameters: each source parameter is the machine parameter at its place, a word. -/
def paramVm (f : HFunc) (mf : Func) : VM :=
  NatMap.ofList ((f.params.zip mf.params).map fun (p, mp) => (p.1, .var mp.1))

/-- Infer the value map: walk the blocks not yet walked in rounds, until none is left or a round
    walks none (untrusted: the result is checked by `funcLowerOk`). -/
def inferVm (c : FCtx) (f : HFunc) : Nat → VM → List (HBlock × List Nat) → VM
  | 0, vm, _ => vm
  | n + 1, vm, pending =>
    let (vm, left) := pending.foldl (fun (vm, left) (b, cs) =>
      match blockLower c false vm f.rets b cs with
      | some (vm', _, _, _) => (vm', left)
      | none => (vm, left ++ [(b, cs)])) (vm, [])
    if left.isEmpty || left.length == pending.length then vm else inferVm c f n vm left

/-- What the translation check of a function yields: the value map, the block each source
    block's region ends in, and per source block the machine values each statement defined. -/
structure FuncLower where
  vm : VM
  tb : NatMap Nat
  defs : NatMap (List (List Nat))

/-- The values a source function defines: its parameters, phis and statement results. -/
def _root_.Fe.Sonatina.H.HFunc.defs (f : HFunc) : List Nat :=
  f.params.map (·.1) ++ f.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))

/-- The values a machine function defines: its parameters, phis and statement results. -/
def mdefs (mf : Func) : List Nat :=
  mf.params.map (·.1) ++ mf.blocks.flatMap fun b => b.phis.map (·.dst) ++ b.body.flatMap (·.dsts.map (·.1))

/-- `funcLower`'s shape conditions (see there). -/
def funcShapeOk (c : FCtx) (f : HFunc) (e : HBlock) (me : Block) (be : Nat) : Bool :=
  f.params.length == c.mf.params.length && c.mf.params.all (·.2 == w256) &&
    f.params.all (Ty.value ·.2) && f.rets.length == c.mf.rets.length &&
    c.mf.rets.all (· == w256) && f.rets.all Ty.value && e.phis.isEmpty &&
    (me.id == be || jumpOnly me be) && distinct f.defs && distinct (f.blocks.map (·.id)) &&
    distinct (mdefs c.mf) &&
    f.blocks.all (fun b => b.term.succs.all fun d => f.blocks.any (·.id == d))

/-- Each source block with the callee places of its calls (the record's hints). -/
def blockCalls (c : FCtx) (f : HFunc) : List (HBlock × List Nat) :=
  f.blocks.zipIdx.map fun (b, k) => (b, (c.frec.calls[k]?).getD [])

/-- The value map: the record's certificate, or the inferred one. -/
def funcVm (c : FCtx) (f : HFunc) : VM :=
  match c.frec.vmCert with
  | some l => NatMap.ofList l
  | none => inferVm c f (f.blocks.length + 1) (paramVm f c.mf) (blockCalls c f)

/-- Each source parameter is the machine parameter at its place. -/
def paramsOk (c : FCtx) (f : HFunc) (vm : VM) : Bool :=
  (f.params.zip c.mf.params).all (fun (p, mp) => vm.find? p.1 == some (.var mp.1))

/-- The checking walk of every source block: its id, the block its region ends in, the machine
    values each statement defined, and the region's machine blocks. -/
def regionsOf (c : FCtx) (f : HFunc) (vm : VM) :
    Option (List (Nat × Nat × List (List Nat) × List Nat)) :=
  (blockCalls c f).mapM fun (b, cs) => do
    let (_, tbk, dss, bs) ← blockLower c true vm f.rets b cs
    some (b.id, tbk, dss, bs)

/-- The machine entry block, when it is a block that only jumps to the source entry's region. -/
def trampOf (me : Block) (be : Nat) : List Nat := if me.id == be then [] else [me.id]

/-- Every source block's phis match its machine start block's. -/
def phisAllOk (c : FCtx) (f : HFunc) (vm : VM) (tb : NatMap Nat) : Bool :=
  f.blocks.all fun b => match c.bm.find? b.id >>= c.mf.block? with
    | some mblk => phisOk c vm tb b.phis mblk.phis
    | none => false

/-- The translation check of function `f` against machine function `c.mf` (`c.bm`, `c.decls` as
    `blockMapOf`, `declsOf` give them): each value of `f` and of `c.mf` is defined once, and the
    blocks of `f` have distinct ids (review 25, C2, C4, C5a); every block a source terminator goes
    to is a block of `f` (H has no rule for a jump elsewhere, where a record's block map may send
    the machine on; session 4, T2); parameters and results are words
    at the same places; the machine entry is `bm` of the source entry, or a block that only
    jumps there (lowering adds one when the source entry has predecessors), and the source
    entry has no phi; every source block's region, terminator and phis match under the
    inferred value map; the machine blocks of the regions, and the entry block that jumps to
    the first, are distinct (C5b, M1). -/
def funcLower (c : FCtx) (f : HFunc) : Option FuncLower := do
  let e ← f.blocks.head?
  let me ← c.mf.blocks.head?
  let be ← c.bm.find? e.id
  unless funcShapeOk c f e me be do none
  let vm := funcVm c f
  unless paramsOk c f vm do none
  let rs ← regionsOf c f vm
  unless distinct (trampOf me be ++ rs.flatMap (·.2.2.2)) do none
  let tb := NatMap.ofList (rs.map fun (b, t, _) => (b, t))
  unless phisAllOk c f vm tb do none
  some ⟨vm, tb, NatMap.ofList (rs.map fun (b, _, d, _) => (b, d))⟩

end Fe.Sonatina.Stage3.Place
