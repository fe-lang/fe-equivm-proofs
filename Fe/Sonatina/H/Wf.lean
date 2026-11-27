import Fe.Sonatina.H.Sem
import Fe.Sonatina.H.Parse
import Fe.Sonatina.Steps.Wf

/-!
# Static well-formedness of a handover section (design §3.7, "static rejections")

`wfReasons s` lists why section `s` is outside what H defines, each a reason key and where;
`wfH s` is that the list is empty.  It is for H what `Func.wf`/`Module.wf`
(`Fe/Sonatina/Steps/Wf.lean`) are for machine IR, and it reuses their machinery: the control
flow is `Func.cfgOk`, and the dominator tree (`domTree`, validated by `DomTree.valid`) and
strict SSA (`ssa`) are computed on the function as the machine IR's syntax (`HFunc.skel`: the
same blocks, phis, results and terminators; an instruction of this dialect stands for one that
reads the same operands).

## What `wfH` is meant to guarantee

Progress, stated here and not proved: for a section `wfH` accepts, no run of `Object.Runtime`
or `Object.Deploy` is stuck.  Every function's run keeps the invariant that each value of its
environment is of its declared type (`Val.fits`), and from a state with that invariant each
rule of `ExecBody`, `ExecBlocks` and `ExecFunc` that the run is at applies or ends the run: no
`stepInst` or `stepTerm` gives `stuck`, and no `bindVals`, `enter`, `evalOp`, `func?`,
`block?`, `head?`, `sizeOf` or `gepOffset` the rules need is `none`.  For a scalar type, whether
a value is of it depends on the type's width only (`Ty.value`, `Val.fits`), so the checks are on
widths.  Each check names the way a run would otherwise be stuck:

- `noEntry`, `entryParams`, `entryReturns`: the section's entry is a function of the module,
  with no parameters (it runs on `[]`, `bindVals`), that never returns (a section run that
  returns has no outcome, as M treats it as stuck);
- `duplicateFunc`, `duplicateStruct`: function and struct names are unique (`func?` and
  `lookup` take the first);
- `symbol`, `symbolRange`: every `sym_addr`/`sym_size` names a symbol of the section, and every
  symbol's offset and size is below `2 ^ 256` (its value is bound as an `i256`);
- `aggregateValue`: every parameter, phi, result and function result is of a value type (an
  integer of a Sonatina width or a pointer; no aggregates after S12, no objects or enums after
  S4d, §4.2; V4 holds of both);
- `cfg` (`Func.cfgOk`): an entry block with no phis, distinct block ids, every target a block
  and none the entry, every phi with one operand from each predecessor and none from elsewhere
  (`block?`, `enter`);
- `dom`, `duplicateDef`, `dominance` (`DomTree.valid`, `ssa`): every value is defined once, and
  every use in a reachable block is dominated by its definition, a phi's operand by the end of
  its predecessor (`evalOp`); blocks the tree does not reach never run;
- `undeclared`, `imm`: every operand anywhere is a declared value, or an immediate of a
  Sonatina width whose value is in range (`evalOp`, `Val.fits`);
- `operandType`: the operands an instruction takes at one width have it (`bin`, `cmp`, `ovf`,
  `select`, a stored value and its type; `binVal`, `stepInst`);
- `results`, `resultType`: a statement binds as many values as its instruction gives, each
  declared at the width it has (`bindVals`; for a call, the callee's results);
- `phiType`, `ret`, `retType`: each phi's operands have its width; each `return` returns as many
  values as the function's results, at their widths (`enter`, and the caller's `bindVals`);
- `callSig`: every call names a function of the module, with as many arguments as parameters,
  each at its parameter's width (`func?`, `bindVals`);
- `evmArity`, `msize`: every `evm_*` operation has its exact number of operands, `evm_log` at
  most four topics (`evmH`); `evm_msize` is not in H (E4);
- `evmWidth`: `evm_exp`, `evm_byte` and `evm_sign_extend` are at `i256` (H computes them as
  words, a narrower result would not fit);
- `memType`, `castType`, `satType`, `truncNuw`: the types of `mload`/`mstore` and `cast` are
  value types, those of the saturating operations and `trunc_nuw` integers of a Sonatina width;
- `allocaType`, `allocaSize`: an `alloca`'s type has a size (`sizeOf`), and some address word
  fits a block of that size (`AddrOk`; `evm_malloc` is bounded by the heap budget instead);
- `gep`: a `gep`'s base is declared at its pointer type, and its path is one H defines
  (`gepOffset`);
- `brTable`: a `br_table` has a default (a default-less one needs an exhaustive `enumtag`
  scrutinee, which this dialect has none of) and distinct immediate keys;
- §3.7's rejections that are no stuck run but outside the subset: `genericDiv` (generic
  `udiv`/`sdiv`/`umod`/`smod`, §3.6), `select` (until #625), `funcPtr` (`get_function_ptr`;
  indirect calls have no syntax), `aggregate` (`insert_value`/`extract_value`).

Every function of the module is checked, called or not, so a callee is well formed in the same
module.  Typing is checked in every block, reachable or not; dominance in the reachable ones.

**What a run of an accepted section can still end in without an outcome**: it does not
terminate (a loop or a recursion H runs forever); or the model library's run does not
terminate (`IRes.diverge`, `TRes.diverge`): a creation of more than 49152 bytes of init code,
which runs out of gas on the EVM, or a `gas()`, call, creation or `evm_self_destruct` when the
feed has no entry left, which the call's real feed has when H makes the calls the bytes make.  Before Osaka `clz`
is the EVM's invalid instruction, an exit, not a stuck run.
-/

namespace Fe.Sonatina.H

open Fe.Sonatina Fe.Sonatina.Steps

/-! ## The function as machine IR syntax -/

/-- An instruction as one of the machine IR's syntax that reads the same operands: itself, or for
    one the machine IR has no constructor for, `evm_keccak256_words` (`gep`), `memzero`
    (`evm_mload_bytes`) or `black_box` (`trunc_nuw`) of its operands. -/
def HInst.skel : HInst → Inst
  | .base i => i
  | .gep _ b idxs => .keccakWords (b :: idxs)
  | .mloadBytes a l => .memzero a l
  | .truncNuw a _ => .blackBox a

/-- A terminator as one of the machine IR's syntax with the same successors and operands. -/
def HTerm.skel : HTerm → Term
  | .base t => t
  | .returnCode o l => .evmReturn o l

/-- The function as the machine IR's syntax: its control flow, definitions and uses. -/
def HFunc.skel (f : HFunc) : Func where
  name := f.name
  params := f.params
  rets := f.rets
  blocks := f.blocks.map fun b =>
    { id := b.id, phis := b.phis, body := b.body.map fun s => ⟨s.dsts, s.inst.skel⟩,
      term := b.term.skel }

/-- The operands an instruction reads. -/
def HInst.args (i : HInst) : List Operand := i.skel.args

/-! ## Instructions -/

/-- A `gep`'s path is one H defines, statically: through pointers and arrays, and through
    structs by immediate indices in range. -/
def gepPathOk (structs : List (String × List Ty)) : Ty → List Operand → Bool
  | _, [] => true
  | .ptr elem, _ :: rest | .array elem _, _ :: rest =>
    (sizeOf structs sizeFuel elem).isSome && gepPathOk structs elem rest
  | .struct name, .imm _ k :: rest => match structs.lookup name with
    | some fields => match fields[k]? with
      | some field => (fields.take k).all (sizeOf structs sizeFuel · |>.isSome) &&
          gepPathOk structs field rest
      | none => false
    | none => false
  | _, _ :: _ => false

/-- The widths of the values instruction `i` gives, from the widths `w` of its operands, or the
    reason H does not define it: `M` gives the callees' signatures and the struct types, `syms`
    the section's symbols, `tyOf` the declared types of the operands. -/
def resultWidths (M : HModule) (syms : List (String × Nat × Nat)) (tyOf : Operand → Option Ty)
    (w : Operand → Nat) : HInst → Except String (List Nat)
  | .base i => match i with
    | .bin op a b =>
      if op.generic then .error "genericDiv"
      else if w a != w b then .error "operandType"
      else if (op matches .evmExp | .evmByte | .evmSignExtend) && w a != 256 then
        .error "evmWidth"
      else .ok [w a]
    | .cmp _ a b => if w a == w b then .ok [1] else .error "operandType"
    | .isZero _ => .ok [1]
    | .not a | .neg a | .clz a | .ctz a | .blackBox a => .ok [w a]
    | .ovf _ a b => if w a == w b then .ok [w a, 1] else .error "operandType"
    | .sat _ _ _ ty => if ty matches .int _ && Ty.value ty then .ok [256] else .error "satType"
    | .cast _ _ ty => if Ty.value ty then .ok [ty.bits] else .error "castType"
    | .select _ a b => if w a == w b then .ok [w a] else .error "operandType"
    | .evm op args => match op.arity with
      | some (n, r) => if args.length == n then .ok (List.replicate r 256) else .error "evmArity"
      | none => .error (if op == .msize then "msize" else "evmArity")
    | .mload _ ty => if Ty.value ty then .ok [ty.bits] else .error "memType"
    | .mstore _ v ty =>
      if !Ty.value ty then .error "memType"
      else if w v == ty.bits then .ok [] else .error "operandType"
    | .memzero .. => .ok []
    | .malloc _ => .ok [256]
    | .alloca ty => match sizeOf M.structs sizeFuel ty with
      | some n => if AddrOk 1 n then .ok [256] else .error "allocaSize"
      | none => .error "allocaType"
    | .symAddr s | .symSize s => if (syms.lookup s).isSome then .ok [256] else .error "symbol"
    | .funcPtr _ => .error "funcPtr"
    | .insertValue .. | .extractValue .. => .error "aggregate"
    | .keccakWords _ => .ok [256]
    | .call callee args => match M.func? callee with
      | some g =>
        if args.length == g.params.length && (args.zip g.params).all (fun (a, p) => w a == p.2.bits)
        then .ok (g.rets.map Ty.bits) else .error "callSig"
      | none => .error "callSig"
  | .gep baseTy base idxs =>
    if baseTy matches .ptr _ && tyOf base == some baseTy && gepPathOk M.structs baseTy idxs then
      .ok [256]
    else .error "gep"
  | .mloadBytes .. => .ok [256]
  | .truncNuw _ ty => if ty matches .int _ && Ty.value ty then .ok [ty.bits] else .error "truncNuw"

/-- §3.7's rejections of an instruction H defines: `select` until #625. -/
def HInst.excluded : HInst → Option String
  | .base (.select ..) => some "select"
  | _ => none

/-! ## Sections -/

/-- Why section `s` is outside H: reason keys, each with where. -/
def wfReasons (s : HSection) : List (String × String) := Id.run do
  let M := s.module
  let mut out : List (String × String) := []
  match M.func? s.entry with
  | none => out := out ++ [("noEntry", s.entry)]
  | some f =>
    unless f.params.isEmpty do out := out ++ [("entryParams", s.entry)]
    if f.blocks.any fun b => b.term matches .base (.ret _) then
      out := out ++ [("entryReturns", s.entry)]
  let names := M.funcs.map (·.name)
  unless names.eraseDups.length == names.length do out := out ++ [("duplicateFunc", "module")]
  let structNames := M.structs.map (·.1)
  unless structNames.eraseDups.length == structNames.length do
    out := out ++ [("duplicateStruct", "module")]
  for (sym, offset, size) in s.symbols do
    unless offset < 2 ^ 256 && size < 2 ^ 256 do out := out ++ [("symbolRange", sym)]
  for f in M.funcs do
    let decls := Parse.declTypes f.params f.blocks
    let tyOf (o : Operand) : Option Ty := match o with
      | .var id => decls.lookup id
      | .imm bits _ => some (.int bits)
    let w (o : Operand) : Nat := ((tyOf o).map Ty.bits).getD 0
    let here (b : Nat) (what : String) := s!"{f.name} block{b}: {what}"
    -- Operands: declared values, immediates of a width, in range; the reasons, with where.
    let operands (where_ : String) (os : List Operand) : List (String × String) :=
      os.filterMap fun o => match o with
        | .var id => if (decls.lookup id).isSome then none else some ("undeclared", s!"{where_} v{id}")
        | .imm bits v =>
          if widths.contains bits && decide (v < 2 ^ bits) then none
          else some ("imm", s!"{where_} {bits}.{v}")
    let known (os : List Operand) : Bool := os.all fun o => (tyOf o).isSome
    -- Value types.
    for (_, ty) in decls do
      unless Ty.value ty do out := out ++ [("aggregateValue", s!"{f.name}: {repr ty}")]
    for ty in f.rets do
      unless Ty.value ty do out := out ++ [("aggregateValue", s!"{f.name} result: {repr ty}")]
    -- Control flow, definitions and dominance.
    let F := f.skel
    if !F.cfgOk then out := out ++ [("cfg", f.name)]
    else
      let T := domTree F
      if !T.valid F then out := out ++ [("dom", f.name)]
      else if !distinct ((defList F).map (·.1)) then out := out ++ [("duplicateDef", f.name)]
      else if !ssa F T then out := out ++ [("dominance", f.name)]
    for b in f.blocks do
      for phi in b.phis do
        let ops := phi.incoming.map (·.1)
        out := out ++ operands (here b.id s!"phi v{phi.dst}") ops
        unless ops.all fun o => !(tyOf o).isSome || w o == phi.ty.bits do
          out := out ++ [("phiType", here b.id s!"phi v{phi.dst}")]
      for st in b.body do
        let wh := here b.id (toString (repr st.inst))
        out := out ++ operands wh st.inst.args
        if let some k := st.inst.excluded then out := out ++ [(k, wh)]
        if known st.inst.args then
          match resultWidths M s.symbols tyOf w st.inst with
          | .error k => out := out ++ [(k, wh)]
          | .ok rs =>
            if st.dsts.length != rs.length then out := out ++ [("results", wh)]
            else unless st.dsts.map (·.2.bits) == rs do out := out ++ [("resultType", wh)]
      let tw := here b.id "terminator"
      let targs := b.term.skel.args
      out := out ++ operands tw targs
      match b.term with
      | .base (.ret vs) =>
        if vs.length != f.rets.length then out := out ++ [("ret", tw)]
        else if known vs && vs.map w != f.rets.map Ty.bits then out := out ++ [("retType", tw)]
      | .base (.brTable _ d cases) =>
        let keys := cases.filterMap fun (o, _) => match o with
          | .imm _ v => some v
          | _ => none
        unless d.isSome && keys.length == cases.length && keys.eraseDups.length == keys.length do
          out := out ++ [("brTable", tw)]
      | _ => pure ()
  return out

/-- The section is in what H defines, statically (§3.7). -/
def wfH (s : HSection) : Bool := (wfReasons s).isEmpty

/-- Both sections of the object are. -/
def Object.wfH (h : Object) : Bool := H.wfH h.init && H.wfH h.runtime

end Fe.Sonatina.H
