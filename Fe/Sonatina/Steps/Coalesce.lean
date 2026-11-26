import Fe.Sonatina.Steps.Wf

/-!
# `coalesce_copies` (design §4.10, review H-6)

Sonatina's `coalesce_machine_copies` (`isa/evm/machine/copy.rs` at `machine-steps` `0585e54f`)
replaces a run of full-word copies `v_i = evm_mload (s + 32 i)`, `evm_mstore (d + 32 i) v_i`,
`i < n`, in one block, by `evm_mcopy d s (32 n)` at the place of the run's last store (with its
instruction id), and deletes the run's other instructions that have no result or an unused one.

The check: the output has the input's blocks, in order, with their ids, phis and terminators.
Each output block's statements are the input block's, in order (`cbodyOk`), where a window of
the input (`runOk`) may become the window's `add`/`sub` statements the output keeps, in order,
followed by `evm_mcopy`:

- the window holds only `evm_mload` with one result, `evm_mstore`, and `add`/`sub` with one
  result, and ends in a store;
- its loads `l_0 … l_{n-1}` read at `s + 32 i` and its stores `t_0 … t_{n-1}`, in order, store
  `l_i`'s result at `d + 32 i`, `n ≥ 2`, the addresses as affine forms over the input's `add`/
  `sub` definitions (`addrNorm`: a base value or none, and an offset modulo `2 ^ 256`);
- the copy is `evm_mcopy d s L` with `d` and `s` the first store's and first load's address
  operands and `L` the literal `32 n`;
- each load's result has one use in the input function, its store;
- all loads come before the first store (snapshot, `loadsFirst`), or both ranges are constant
  and disjoint in `Nat`;
- both ranges are constant, `s + L ≤ 2 ^ 256` and `d + L ≤ 2 ^ 256` in `Nat`, unless `allowBase`:
  the interpreter's `mcopy` reads and writes at `Nat` addresses where the `add`s that build a
  base-relative run's addresses wrap (review C-1, design §4.10's extra condition).

What may be deleted: the window's loads and other stores, and `add`/`sub` statements of the
window; no result of a window statement the output does not keep is defined in the output
(`keptOk`, `fresh`) or used in it (`unusedOk'`).  Everything else of the function is unchanged.  Instruction ids: kept statements keep theirs, a copy has the replaced
store's.
-/

namespace Fe.Sonatina.Steps

/-- `2 ^ 256`. -/
abbrev W256 : Nat := 2 ^ 256

/-- Base-relative runs: accepted only once the interpreter's `mcopy` diverges past `2 ^ 256`
    (review C-1). -/
def allowBase : Bool := false

/-- The instruction defining `u`: a statement of a block the tree reaches, `u` its one result. -/
def stmtOf (B : NatMap Block) (D : NatMap Def) (T : DomTree) (u : Nat) : Option Inst :=
  match D.find? u with
  | some (.stmt d j) =>
    if (T.reach.find? d).isSome then
      match B.find? d with
      | some blk => match blk.body[j]? with
        | some s => match s.dsts with
          | [(u', _)] => if u' = u then some s.inst else none
          | _ => none
        | none => none
      | none => none
    else none
  | _ => none

/-- An address as a base value (none for a constant) and an offset modulo `2 ^ 256`, following
    `add` with an immediate and `sub` of an immediate, at most `n` steps (stopping early only
    leaves a larger base). -/
def addrNorm (B : NatMap Block) (D : NatMap Def) (T : DomTree) : Nat → Operand → Option Nat × Nat
  | _, .imm _ v => (none, v % W256)
  | 0, .var u => (some u, 0)
  | n + 1, .var u => match stmtOf B D T u with
    | some (.bin .add a (.imm _ c)) =>
      let (b, o) := addrNorm B D T n a; (b, (o + c) % W256)
    | some (.bin .add (.imm _ c) a) =>
      let (b, o) := addrNorm B D T n a; (b, (o + c) % W256)
    | some (.bin .sub a (.imm _ c)) =>
      let (b, o) := addrNorm B D T n a; (b, (o + W256 - c % W256) % W256)
    | _ => (some u, 0)

/-- How often each value is read in the function: phi operands, statement operands, terminator
    operands. -/
def useCount (f : Func) (u : Nat) : Nat :=
  ((f.blocks.flatMap fun b =>
    (b.phis.flatMap fun phi => phi.incoming.map (·.1)) ++ (b.body.flatMap (·.inst.args)) ++
      b.term.args).filter (· == .var u)).length

/-- A load of a run: its address and result. -/
def asLoad (s : Stmt) : Option (Operand × Nat) :=
  match s.inst, s.dsts with
  | .evm .mload [a], [(r, _)] => some (a, r)
  | _, _ => none

/-- A store of a run: its address and value. -/
def asStore (s : Stmt) : Option (Operand × Operand) :=
  match s.inst, s.dsts with
  | .evm .mstore [a, v], [] => some (a, v)
  | _, _ => none

/-- Address arithmetic a run may hold. -/
def isArith (s : Stmt) : Bool :=
  match s.inst, s.dsts with
  | .bin .add _ _, [_] | .bin .sub _ _, [_] => true
  | _, _ => false

/-- No load of the window comes after its first store. -/
def loadsFirst : List Stmt → Bool
  | [] => true
  | st :: rest => if (asStore st).isSome then rest.all fun st => (asLoad st).isNone else loadsFirst rest

/-- A statement none of whose results the output defines. -/
def fresh (OD : NatMap Def) (s : Stmt) : Bool := s.dsts.all fun d => (OD.find? d.1).isNone

/-- What the copy check reads. -/
structure KCtx where
  f : Func
  B : NatMap Block
  D : NatMap Def
  OD : NatMap Def
  T : DomTree
  fuel : Nat

def KCtx.of (f f' : Func) : KCtx :=
  ⟨f, .ofListBy (·.id) f.blocks, defsOf f, defsOf f', domTree f,
    f.blocks.foldl (fun n b => n + b.body.length) 1⟩

namespace KCtx

variable (X : KCtx)

def norm (o : Operand) : Option Nat × Nat := addrNorm X.B X.D X.T X.fuel o

/-- `o` is `base + off + 32 i`. -/
def atOff (base : Option Nat × Nat) (i : Nat) (o : Operand) : Bool :=
  let (b, off) := X.norm o
  b == base.1 && off == (base.2 + 32 * i) % W256

/-- A window of the input and the copy that replaces it. -/
def runOk (win : List Stmt) (mc : Stmt) : Bool :=
  let loads := win.filterMap asLoad
  let stores := win.filterMap asStore
  let n := loads.length
  match loads.head?, stores.head?, win.getLast? with
  | some (s, _), some (d, _), some last =>
    let sb := X.norm s
    let db := X.norm d
    let L := 32 * n
    -- the window's shape
    win.all (fun st => (asLoad st).isSome || (asStore st).isSome || isArith st) &&
      (asStore last).isSome && n ≥ 2 && stores.length == n &&
      -- the copy
      decide (mc = ⟨[], .evm .mcopy [d, s, .imm 256 L]⟩) &&
      -- addresses and values
      (loads.zipIdx.all fun (ld, i) => X.atOff sb i ld.1 && useCount X.f ld.2 == 1) &&
      ((stores.zip loads).zipIdx.all fun ((st, ld), i) => X.atOff db i st.1 && decide (st.2 = .var ld.2)) &&
      -- in bounds
      (allowBase || (sb.1.isNone && db.1.isNone && decide (sb.2 + L ≤ W256) &&
        decide (db.2 + L ≤ W256))) &&
      -- snapshot, or constant ranges disjoint in `Nat`
      (loadsFirst win ||
         (sb.1.isNone && db.1.isNone && (decide (sb.2 + L ≤ db.2) || decide (db.2 + L ≤ sb.2))))
  | _, _, _ => false

/-- `kept` is a subsequence of `win`'s arithmetic, and the window's other statements have no
    result the output defines. -/
def keptOk : List Stmt → List Stmt → Bool
  | [], ws => ws.all (fresh X.OD)
  | _ :: _, [] => false
  | k :: ks, w :: ws =>
    if decide (k = w) && isArith w then keptOk ks ws else fresh X.OD w && keptOk (k :: ks) ws

/-- The output's statements against the input's: each the same, or a window and its copy (at
    most `n` input statements; running out rejects). -/
def cbodyOk : Nat → List Stmt → List Stmt → Bool
  | _, [], [] => true
  | _, _ :: _, [] => false
  | 0, _, _ :: _ => false
  | n + 1, os, i :: is =>
    (match os with
      | o :: os' => decide (o = i) && cbodyOk n os' is
      | [] => false) ||
    -- a window `i :: is` of length `w + 1`, its kept statements, then its copy
    ((List.range is.length).any fun w =>
      let win := (i :: is).take (w + 2)
      let k := os.findIdx fun o => match o.inst with | .evm .mcopy _ => true | _ => false
      match os[k]? with
      | some mc => X.runOk win mc && X.keptOk (os.take k) win &&
          cbodyOk n (os.drop (k + 1)) ((i :: is).drop (w + 2))
      | none => false)

/-- An output block against the input block at its place. -/
def blockOk (b' b : Block) : Bool :=
  b'.id == b.id && decide (b'.phis = b.phis) && decide (b'.term = b.term) &&
    X.cbodyOk (b.body.length + 1) b'.body b.body

end KCtx

/-- No input statement result the output does not define is used in the output. -/
def unusedOk' (f f' : Func) : Bool :=
  let U := usedVars' f'
  let OD := defsOf f'
  f.blocks.all fun b => b.body.all fun s => s.dsts.all fun d =>
    (OD.find? d.1).isSome || (U.find? d.1).isNone
where
  usedVars' (f : Func) : NatMap Unit :=
    .ofList ((f.blocks.flatMap fun b =>
      (b.phis.flatMap fun phi => phi.incoming.map (·.1)) ++ (b.body.flatMap (·.inst.args)) ++
        b.term.args).filterMap fun o => match o with
      | .var u => some (u, ())
      | _ => none)

/-- The check of a `coalesce_copies` step of `f` to the snapshot `s` (instruction ids are the
    statements', checked by `checkStep`'s `wf`; the copy's id is the replaced store's). -/
def checkCoalesce (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap) : Bool :=
  let f' := s.func
  let X := KCtx.of f f'
  ids.isSome && f'.name == f.name && decide (f'.params = f.params) && decide (f'.rets = f.rets) &&
    f'.machine && X.T.valid f && ssa f X.T && f'.blocks.length == f.blocks.length &&
    (f'.blocks.zip f.blocks).all (fun p => X.blockOk p.1 p.2) && unusedOk' f f'

end Fe.Sonatina.Steps
