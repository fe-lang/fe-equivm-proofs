import Fe.Sonatina.H.Sem
import Fe.Sonatina.H.Parse

/-!
# Static well-formedness of a handover section (design §3.7, "static rejections")

`wfReasons s` lists why section `s` is outside what H defines, each a reason key and where;
`wfH s` is that the list is empty.  A construct H does not define is a rejection, never an
excuse (§3.7), so these are the constructs a run would be stuck at, and the ones §3.7 names:

- `msize`: `evm_msize` (E4); `funcPtr`: `get_function_ptr` (indirect calls have no syntax);
  `genericDiv`: generic `udiv`/`sdiv`/`umod`/`smod` (§3.6); `select`: until #625 lands;
  `aggregate`: `insert_value`/`extract_value`, and `aggregateValue`: a value, parameter or
  result of a type that is not an integer or a pointer (no aggregates after S12, no objects or
  enums after S4d, §4.2; V4 holds of the rest, as both are inhabited);
- `callSig`: a call to no function of the module, or whose arity, result count or argument and
  result types do not match the callee's signature (`i256` and pointer types are one word, and
  an immediate's pointer type is not kept by the reader, so they match each other);
- `results`: a statement that binds another number of values than its instruction gives;
- `cfg`: no entry, duplicate block ids, a target that is no block or is the entry, phis in the
  entry, a phi whose incoming blocks are not its block's predecessors (phis lead their block by
  the reader);
- `brTable`: a `br_table` without a default (a default-less one needs an exhaustive `enumtag`
  scrutinee, which this dialect has none of) or with non-immediate or duplicate keys;
- `ret`: a `return` of another number of values than the function's results;
  `entryReturns`: a section entry with a `return` (M treats it as stuck); `noEntry`: no entry;
- `symbol`: a symbol the section does not have; `memType`: `mload`/`mstore` of a type that is
  not a scalar; `allocaType`: an `alloca` of a type with no size; `gep`: a `gep` whose base is
  not a pointer, through a scalar, or with a struct index that is not an immediate in range;
  `truncNuw`: `trunc_nuw` to a type that is not an integer.
-/

namespace Fe.Sonatina.H

open Fe.Sonatina

/-- An integer of a Sonatina width, or a pointer: the value types of this dialect. -/
def Ty.value : Ty → Bool
  | .int n => [1, 8, 16, 32, 64, 128, 256].contains n
  | .ptr _ => true
  | _ => false

/-- Two types an argument may be passed at: equal, or both one word (`i256` or a pointer). -/
def Ty.compat (a b : Ty) : Bool :=
  a == b || (match a, b with
    | .int 256, .ptr _ | .ptr _, .int 256 | .ptr _, .ptr _ => true
    | _, _ => false)

/-- The number of values an instruction gives, except a call's. -/
def HInst.results? : HInst → Option Nat
  | .base (.call ..) => none
  | .base (.ovf ..) => some 2
  | .base (.mstore ..) | .base (.memzero ..) => some 0
  | .base (.evm op _) => some (match op with
    | .calldataCopy | .codeCopy | .extCodeCopy | .returnDataCopy | .mstore | .sstore | .tstore
    | .mcopy | .mstore8 | .log _ => 0
    | _ => 1)
  | _ => some 1

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

/-- Why section `s` is outside H: reason keys, each with where. -/
def wfReasons (s : HSection) : List (String × String) := Id.run do
  let M := s.module
  let mut out : List (String × String) := []
  match M.func? s.entry with
  | none => out := out ++ [("noEntry", s.entry)]
  | some f =>
    if f.blocks.any fun b => b.term matches .base (.ret _) then
      out := out ++ [("entryReturns", s.entry)]
  for f in M.funcs do
    let decls := Parse.declTypes f.params f.blocks
    let tyOf (o : Operand) : Option Ty := match o with
      | .var id => decls.lookup id
      | .imm bits _ => some (.int bits)
    let here (b : Nat) (what : String) := s!"{f.name} block{b}: {what}"
    -- Value types.
    for (_, ty) in decls do
      unless Ty.value ty do out := out ++ [("aggregateValue", s!"{f.name}: {repr ty}")]
    for ty in f.rets do
      unless Ty.value ty do out := out ++ [("aggregateValue", s!"{f.name} result: {repr ty}")]
    -- Control flow.
    let ids := f.blocks.map (·.id)
    let preds (id : Nat) := f.blocks.filter (·.term.succs.contains id) |>.map (·.id)
    match f.blocks.head? with
    | none => out := out ++ [("cfg", s!"{f.name}: no blocks")]
    | some e =>
      unless e.phis.isEmpty do out := out ++ [("cfg", s!"{f.name}: phis in the entry")]
      unless ids.eraseDups.length == ids.length do
        out := out ++ [("cfg", s!"{f.name}: duplicate block ids")]
      for b in f.blocks do
        for t in b.term.succs do
          unless t != e.id && ids.contains t do
            out := out ++ [("cfg", here b.id s!"target block{t}")]
        for phi in b.phis do
          let ins := phi.incoming.map (·.2)
          let ps := preds b.id
          unless ins.eraseDups.length == ins.length && ins.all ps.contains && ps.all ins.contains do
            out := out ++ [("cfg", here b.id s!"phi v{phi.dst}")]
    for b in f.blocks do
      for st in b.body do
        let w := here b.id (toString (repr st.inst))
        match st.inst.results? with
        | some n => unless st.dsts.length == n do out := out ++ [("results", w)]
        | none => pure ()
        match st.inst with
        | .base (.evm .msize _) => out := out ++ [("msize", w)]
        | .base (.funcPtr _) => out := out ++ [("funcPtr", w)]
        | .base (.bin op _ _) => if op.generic then out := out ++ [("genericDiv", w)]
        | .base (.select ..) => out := out ++ [("select", w)]
        | .base (.insertValue ..) | .base (.extractValue ..) => out := out ++ [("aggregate", w)]
        | .base (.call callee args) => match M.func? callee with
          | none => out := out ++ [("callSig", w)]
          | some g =>
            let argsOk := args.length == g.params.length &&
              (args.zip g.params).all fun (a, (_, ty)) => (tyOf a).any (Ty.compat · ty)
            let retsOk := st.dsts.length == g.rets.length &&
              (st.dsts.zip g.rets).all fun ((_, ty), r) => Ty.compat ty r
            unless argsOk && retsOk do out := out ++ [("callSig", w)]
        | .base (.symAddr sym) | .base (.symSize sym) =>
          unless (s.symbols.lookup sym).isSome do out := out ++ [("symbol", w)]
        | .base (.mload _ ty) | .base (.mstore _ _ ty) =>
          unless Ty.scalar ty do out := out ++ [("memType", w)]
        | .base (.alloca ty) =>
          unless (sizeOf M.structs sizeFuel ty).isSome do out := out ++ [("allocaType", w)]
        | .gep baseTy _ idxs =>
          unless (baseTy matches .ptr _) && gepPathOk M.structs baseTy idxs do
            out := out ++ [("gep", w)]
        | .truncNuw _ ty => unless (ty matches .int _) do out := out ++ [("truncNuw", w)]
        | _ => pure ()
      match b.term with
      | .base (.ret vs) =>
        unless vs.length == f.rets.length do out := out ++ [("ret", here b.id "return")]
      | .base (.brTable _ d cases) =>
        let keys := cases.filterMap fun (o, _) => match o with
          | .imm _ v => some v
          | _ => none
        unless d.isSome && keys.length == cases.length && keys.eraseDups.length == keys.length do
          out := out ++ [("brTable", here b.id "br_table")]
      | _ => pure ()
  return out

/-- The section is in what H defines, statically (§3.7). -/
def wfH (s : HSection) : Bool := (wfReasons s).isEmpty

/-- Both sections of the object are. -/
def Object.wfH (h : Object) : Bool := H.wfH h.init && H.wfH h.runtime

end Fe.Sonatina.H
