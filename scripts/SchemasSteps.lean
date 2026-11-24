import Fe.Sonatina.Steps.SchemasStep
import Fe.Sonatina.Steps.Validate
import Fe.Sonatina.Steps.Read

/-!
`lake env lean --run scripts/SchemasSteps.lean [--mutate-facts | --mutate-out] <sidecar>...`:
replay each version-5 record of each sidecar without checking, and run `checkSccpFold` and
`checkKnownBitsSimplify` on every function of every step of those kinds.  One line per function
step: `path  section  kind  func  ACCEPT|REJECT  reason`.  Interpreted, not kernel-evaluated.

With a mutation flag, each step is mutated instead, every mutant of a kind at its first place
that applies, and each mutant is checked: `path  section  kind  func  MUT:<name>  verdict`.
Every mutant should be rejected; `scripts/SchemasStepsTab.py` counts them.

`--mutate-facts` (the output left as recorded):
- `const+1`: every SCCP constant `c` made `(c + 1) mod 2^256`;
- `kb-flip`: the first known-bits claim made all zeros, or all ones if it was all zeros;
- `kb-contra`: the first claim made `kz = ko = 1`;
- `dead-live`: a slot the run may take (of the entry's terminator) added to the dead edges.

`--mutate-out` (the facts left as recorded, review 13 finding 7):
- `sigma-lit`: one literal σ substitutes made `c + 1`;
- `sigma-var`: one value σ substitutes replaced by another parameter, or by `0`;
- `sigma-one`: of a deleted value read twice, one substituted use changed;
- `opcode`: the opcode of one unchanged paired pure statement changed, same arity;
- `swap-br`: the two targets of one `br` swapped;
- `phi-block`: the incoming block of one output phi operand changed;
- `del-used`: one pure statement whose result the output uses, deleted;
- `del-effect`: one statement that is not pure, deleted;
- `kept-use`: one use of a kept value replaced by another parameter, or by `0`;
- `ssa`: one use replaced by a value the block defines after it;
- `params`: the output's first two parameters swapped;
- `ids-short`: the last id of the output's first block dropped;
- `imm-range`: one output literal made `2 ^ 256`, unreduced.
-/

open Fe.Sonatina Fe.Sonatina.Steps Fe.Sonatina.Steps.Schemas

/-! ## Fact mutations -/

def factMutants (f : Func) (F : StepFacts) : List (String × StepFacts) := Id.run do
  let mut out := []
  if let some cs := F.consts then
    unless cs.isEmpty do
      out := out ++ [("const+1", { F with consts := some (cs.map fun e => (e.1, (e.2 + 1) % W)) })]
  match F.knownBits with
  | e :: es =>
    let flip := if e.2.1 != M then (e.1, M, 0) else (e.1, 0, M)
    out := out ++ [("kb-flip", { F with knownBits := flip :: es }),
      ("kb-contra", { F with knownBits := (e.1, 1, 1) :: es })]
  | [] => pure ()
  if F.consts.isSome then
    match f.blocks.head? with
    | some e =>
      match (e.term.succs.zipIdx.find? fun tk => !F.deadEdges.contains (e.id, tk.2)) with
      | some (_, k) => out := out ++ [("dead-live", { F with deadEdges := (e.id, k) :: F.deadEdges })]
      | none => pure ()
    | none => pure ()
  return out

/-! ## Output mutations -/

/-- The instruction with its argument at position `k` (in `Inst.args` order) replaced. -/
def setArgAt (i : Inst) (k : Nat) (o : Operand) : Inst :=
  let new := i.args.set k o
  let g : Operand → StateM Nat Operand := fun x => do
    let j ← get
    set (j + 1)
    return (new[j]?).getD x
  let st : StateM Nat Inst := match i with
    | .bin op a b => do return .bin op (← g a) (← g b)
    | .cmp op a b => do return .cmp op (← g a) (← g b)
    | .isZero a => do return .isZero (← g a)
    | .not a => do return .not (← g a)
    | .clz a => do return .clz (← g a)
    | .mload a ty => do return .mload (← g a) ty
    | .mstore a v ty => do return .mstore (← g a) (← g v) ty
    | .evm op args => do return .evm op (← args.mapM g)
    | .call f args => do return .call f (← args.mapM g)
    | i => pure i
  (st.run 0).1

def setBlock (s : FuncSnap) (bi : Nat) (b : Block) : FuncSnap :=
  { s with func := { s.func with blocks := s.func.blocks.set bi b } }

def setStmt (s : FuncSnap) (bi j : Nat) (st : Stmt) : FuncSnap :=
  match s.func.blocks[bi]? with
  | some b => setBlock s bi { b with body := b.body.set j st }
  | none => s

/-- The output with statement `j` of block `bi` removed, its id too. -/
def delStmt (s : FuncSnap) (bi j : Nat) : FuncSnap :=
  match s.func.blocks[bi]?, s.insts[bi]? with
  | some b, some ids =>
    { setBlock s bi { b with body := b.body.eraseIdx j } with
      insts := s.insts.set bi (ids.eraseIdx (b.phis.length + j)) }
  | _, _ => s

def usedIn (f : Func) (v : Nat) : Bool := f.blocks.any fun b =>
  b.phis.any (·.incoming.any (·.1 == .var v)) || b.body.any (·.inst.args.contains (.var v)) ||
    b.term.args.contains (.var v)

def otherOp : Op2 → Op2
  | .add => .sub | .sub => .add | .mul => .add | .and => .or | .or => .and | .xor => .and
  | .lt => .gt | .gt => .lt | .slt => .sgt | .sgt => .slt | .eq => .lt | .shl => .shr
  | .shr => .shl | .sar => .shr | .udiv => .umod | .umod => .udiv | .sdiv => .smod
  | .smod => .sdiv | .exp => .mul | .byte => .signextend | .signextend => .byte

/-- Another value than `o`: a parameter, else `0`. -/
def other (f : Func) (o : Operand) : Operand :=
  match f.params.find? (fun p => Operand.var p.1 != o) with
  | some (p, _) => .var p
  | none => .imm 256 0

def outMutants (f : Func) (ids : List (List Nat)) (s : FuncSnap) : List (String × FuncSnap) :=
  Id.run do
  let mut out : List (String × FuncSnap) := []
  let fo := s.func
  let pairsOf : List (Option (List (Line × Line))) :=
    ((f.blocks.zip ids).zip (fo.blocks.zip s.insts)).map fun bb =>
      (pairUp (idLines bb.1.1 bb.1.2) (idLines bb.2.1 bb.2.2)).map (·.1)
  let σ := (sigmaOf ((pairsOf.filterMap id).flatten)).getD .empty
  let inDefs := defsOf f
  let outDefs := defsOf fo
  -- The output statement paired with input statement `si` substituted operand `k`.
  let subAt := fun (bi : Nat) (st : Stmt) (k : Nat) =>
    ((pairsOf[bi]?).bind id).any fun ps => ps.any fun LL => match LL with
      | (.stmt si, .stmt so) => so == st && (si.inst.args[k]?).any fun a =>
          (st.inst.args[k]?).any fun o => a != o && match a with
            | .var v => σ.find? v == some o
            | _ => false
      | _ => false
  let mut seen : List String := []
  for (ob, bi) in fo.blocks.zipIdx do
    for (st, j) in ob.body.zipIdx do
      for (o, k) in st.inst.args.zipIdx do
        if subAt bi st k then
          match o with
          | .imm b c =>
            if !seen.contains "sigma-lit" then
              out := out ++ [("sigma-lit", setStmt s bi j { st with inst := setArgAt st.inst k (.imm b (c + 1)) })]
              seen := "sigma-lit" :: seen
          | o =>
            if !seen.contains "sigma-var" then
              out := out ++ [("sigma-var", setStmt s bi j { st with inst := setArgAt st.inst k (other fo o) })]
              seen := "sigma-var" :: seen
        -- a kept value's use
        if !seen.contains "kept-use" then
          match o with
          | .var u =>
            if (outDefs.find? u).isSome && (inDefs.find? u).isSome && !subAt bi st k then
              out := out ++ [("kept-use", setStmt s bi j { st with inst := setArgAt st.inst k (other fo o) })]
              seen := "kept-use" :: seen
          | _ => pure ()
        -- a use of a value the block defines later
        if !seen.contains "ssa" then
          match (ob.body.drop (j + 1)).findSome? (·.dsts.head?) with
          | some (later, _) =>
            out := out ++ [("ssa", setStmt s bi j { st with inst := setArgAt st.inst k (.var later) })]
            seen := "ssa" :: seen
          | none => pure ()
        if !seen.contains "imm-range" then
          match o with
          | .imm _ _ =>
            out := out ++ [("imm-range", setStmt s bi j { st with inst := setArgAt st.inst k (.imm 256 (2 ^ 256)) })]
            seen := "imm-range" :: seen
          | _ => pure ()
      -- opcode of an unchanged paired pure statement
      if !seen.contains "opcode" then
        let unchanged := ((pairsOf[bi]?).bind id).any fun ps => ps.any fun LL => match LL with
          | (.stmt si, .stmt so) => si == st && so == st
          | _ => false
        if unchanged then
          let i' : Option Inst := match pureInst? st.inst with
            | some (.op2 o a b) => some (PureInst.op2 (otherOp o) a b).toInst
            | some (.op1 .not a) => some (.isZero a)
            | some (.op1 .isZero a) => some (.not a)
            | _ => none
          if let some i' := i' then
            out := out ++ [("opcode", setBlock s bi { ob with body := ob.body.set j { st with inst := i' } })]
            seen := "opcode" :: seen
      if !seen.contains "del-used" && (pureInst? st.inst).isSome &&
          st.dsts.any (fun d => usedIn fo d.1) then
        out := out ++ [("del-used", delStmt s bi j)]
        seen := "del-used" :: seen
      if !seen.contains "del-effect" && (pureInst? st.inst).isNone then
        out := out ++ [("del-effect", delStmt s bi j)]
        seen := "del-effect" :: seen
    -- phi incoming block
    if !seen.contains "phi-block" then
      match ob.phis.head? with
      | some p => match p.incoming with
        | (o, q) :: rest =>
          let q' := (fo.blocks.find? (·.id != q)).map (·.id) |>.getD (q + 1)
          out := out ++ [("phi-block", setBlock s bi { ob with phis := { p with incoming := (o, q') :: rest } :: ob.phis.tail })]
          seen := "phi-block" :: seen
        | [] => pure ()
      | none => pure ()
    if !seen.contains "swap-br" then
      match ob.term with
      | .br c x y =>
        if x != y then
          out := out ++ [("swap-br", setBlock s bi { ob with term := .br c y x })]
          seen := "swap-br" :: seen
      | _ => pure ()
  -- a deleted value read twice, one substituted use changed: found through σ's targets
  let twice := (sigmaKeys ((pairsOf.filterMap id).flatten) σ)
  match twice.find? (fun v => (twice.filter (· == v)).length ≥ 2) with
  | some v =>
    match σ.find? v with
    | some x =>
      let x' := match x with | .imm b c => Operand.imm b (c + 1) | o => other fo o
      match (fo.blocks.zipIdx.findSome? fun (ob, bi) => ob.body.zipIdx.findSome? fun (st, j) =>
          (st.inst.args.zipIdx.find? fun (o, k) => o == x && subAt bi st k).map fun (_, k) => (bi, j, k)) with
      | some (bi, j, k) =>
        match fo.blocks[bi]? with
        | some ob => match ob.body[j]? with
          | some st => out := out ++ [("sigma-one", setStmt s bi j { st with inst := setArgAt st.inst k x' })]
          | none => pure ()
        | none => pure ()
      | none => pure ()
    | none => pure ()
  | none => pure ()
  -- frame
  match fo.params with
  | p :: q :: rest => out := out ++ [("params", { s with func := { fo with params := q :: p :: rest } })]
  | _ => pure ()
  match s.insts with
  | ids0 :: rest => out := out ++ [("ids-short", { s with insts := ids0.dropLast :: rest })]
  | [] => pure ()
  return out

def check (k : StepKind) (f : Func) (ids : Option (List (List Nat))) (s : FuncSnap)
    (F : StepFacts) : Bool :=
  if k == StepKind.sccpFold then checkSccpFold f ids s F else checkKnownBitsSimplify f ids s F

def main (args : List String) : IO Unit := do
  let (mode, args) := match args with
    | "--mutate-facts" :: rest => ("facts", rest)
    | "--mutate-out" :: rest => ("out", rest)
    | rest => ("none", rest)
  for path in args do
    let text ← IO.FS.readFile path
    match Parse.parseSidecar text with
    | .error e => IO.println s!"{path}\t-\t-\t-\tNOT READ\tsidecar: {e}"
    | .ok s =>
      for sec in s.sections do
        let some low := sec.lowering | pure ()
        match Read.sectionSteps text sec.name with
        | .error e => IO.println s!"{path}\t{sec.name}\t-\t-\tNOT READ\tmachine_steps: {e}"
        | .ok none => pure ()
        | .ok (some r) =>
          let mut M := r.module low.machine.structs
          let mut I := r.ids
          for p in r.passes do
            for st in p.steps do
              if st.kind == StepKind.sccpFold || st.kind == StepKind.knownBitsSimplify then
                for fs in st.funcs do
                  let pre := s!"{path}\t{sec.name}\t{st.kind.name}\t{fs.func}"
                  match M.func? fs.func, readFacts fs.facts with
                  | none, _ => IO.println s!"{pre}\tREJECT\tno such function"
                  | _, .error e => IO.println s!"{pre}\tREJECT\tfacts not read: {e}"
                  | some f, .ok F =>
                    let ids := I.lookup fs.func
                    if mode == "facts" then
                      for (nm, F') in factMutants f F do
                        IO.println s!"{pre}\tMUT:{nm}\t{if check st.kind f ids fs.out F' then "ACCEPT" else "REJECT"}"
                    else if mode == "out" then
                      for (nm, s') in outMutants f (ids.getD []) fs.out do
                        IO.println s!"{pre}\tMUT:{nm}\t{if check st.kind f ids s' F then "ACCEPT" else "REJECT"}"
                    else
                      let ok := check st.kind f ids fs.out F
                      let why := (if st.kind == StepKind.sccpFold then diagnoseSccpFold f ids fs.out F
                        else diagnoseKnownBitsSimplify f ids fs.out F).getD "-"
                      IO.println s!"{pre}\t{if ok then "ACCEPT" else "REJECT"}\t{why}"
              M := stepOut M st.funcs
              I := stepIds I st.funcs
