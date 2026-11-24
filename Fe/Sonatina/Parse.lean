import Fe.Sonatina.Syntax
import Lean.Data.Json
import Lean.Elab.Command

/-!
# Reading Sonatina IR

`parseModule` reads a module in the text form Sonatina's `ModuleWriter` prints, a statement a
line, and `parseSidecar` the JSON `fe build --emit sidecar` writes: that text, and the bytes and
symbols of each section compiled from it.  An instruction outside the subset of `Syntax.lean` is
an error, not skipped.  In a sidecar, what the checker reads (the object declarations, and per
section the bytes, symbols, machine IR and hints) must be read; the module after optimization
and a section's IR before machine lowering are `none` where they are outside the subset, and a
model of either level is then stuck.

`sonatina_sidecar name "path"` reads a sidecar when it elaborates and defines `name` as the
`Sidecar` it holds, so that the IR is a term of its own.  The parser runs only then; nothing
about it needs to be proved, since a misread module is a different module, which the bytecode
then fails to implement.
-/

namespace Fe.Sonatina.Parse

open Lean

abbrev P := Except String

/-- The tokens of a statement: words, and the punctuation `(`, `)`, `,` and `=`.  An array type
    `[T; n]` is one word. -/
def tokens (line : String) : List String :=
  let flush (acc : List String) (word : List Char) :=
    if word.isEmpty then acc else String.ofList word.reverse :: acc
  let (acc, word, _) := line.toList.foldl (init := ([], [], 0)) fun (acc, word, depth) c =>
    if c == '[' then (acc, c :: word, depth + 1)
    else if c == ']' then (acc, c :: word, depth - 1)
    else if depth > 0 then (acc, c :: word, depth)
    else if c == ' ' || c == '\t' then (flush acc word, [], depth)
    else if c == '(' || c == ')' || c == ',' || c == '=' then
      (String.singleton c :: flush acc word, [], depth)
    else (acc, c :: word, depth)
  (flush acc word).reverse

partial def parseTy (s : String) : P Ty :=
  match s.toList with
  | '*' :: rest => return .ptr (← parseTy (String.ofList rest))
  | '@' :: rest => return .struct (String.ofList rest)
  | '[' :: rest =>
    -- The length follows the last `;`: the element type may be an array.
    let body := ((String.ofList rest).dropEnd 1).toString
    match body.splitOn ";" |>.reverse with
    | len :: elem@(_ :: _) => do
      let some len := len.trimAscii.toString.toNat? | throw s!"bad array type {s}"
      return .array (← parseTy (";".intercalate elem.reverse).trimAscii.toString) len
    | _ => throw s!"bad array type {s}"
  | 'i' :: rest =>
    match (String.ofList rest).toNat? with
    | some bits =>
      if [1, 8, 16, 32, 64, 128, 256].contains bits then pure (.int bits)
      else throw s!"unknown type {s}"
    | none => throw s!"unknown type {s}"
  | _ =>
    if s == "unit" then pure .unit
    else if let some t := (s.dropPrefix? "objref<").bind (·.toString.dropSuffix? ">") then
      return .objRef (← parseTy t.toString)
    else if let some t := (s.dropPrefix? "constref<").bind (·.toString.dropSuffix? ">") then
      return .constRef (← parseTy t.toString)
    else throw s!"unsupported type {s}"

/-- `word` split at its first `.`. -/
def splitDot (word : String) : String × String :=
  match word.splitOn "." with
  | head :: rest => (head, ".".intercalate rest)
  | [] => (word, "")

/-- The id of `v<id>`. -/
def valueId? (s : String) : Option Nat :=
  match s.toList with
  | 'v' :: digits => (String.ofList digits).toNat?
  | _ => none

/-- `v<id>.T`, a value a statement or a parameter declares. -/
def parseDecl (word : String) : P (Nat × Ty) := do
  let (name, ty) := splitDot word
  let some id := valueId? name | throw s!"expected a value declaration, got {word}"
  return (id, ← parseTy ty)

/-- A decimal or `0x` hexadecimal natural number. -/
def parseNat (cs : List Char) : Option Nat :=
  match cs with
  | '0' :: 'x' :: hex@(_ :: _) =>
    hex.foldlM (init := 0) fun n c =>
      if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
      else none
  | _ => (String.ofList cs).toNat?

/-- An operand: `v<id>` or an integer `n.T`, held as its value modulo `2 ^ bits`. -/
def parseOperand (word : String) : P Operand := do
  if let some id := valueId? word then return .var id
  let (head, ty) := splitDot word
  let ty ← parseTy ty
  let n : Option Int := match head.toList with
    | '-' :: rest => (parseNat rest).map fun n => -(n : Int)
    | cs => (parseNat cs).map Int.ofNat
  let some n := n | throw s!"expected an operand, got {word}"
  let bits := ty.bits
  return .imm bits (n % (2 ^ bits : Int)).toNat

/-- The id of `block<id>`. -/
def blockId (word : String) : P Nat := do
  let some id := (word.dropPrefix? "block").bind (·.toString.toNat?)
    | throw s!"expected a block, got {word}"
  return id

/-- The `(operand block)` pairs of a `phi` or a `br_table`. -/
def pairs : List String → P (List (Operand × Nat))
  | [] => pure []
  | "(" :: value :: block :: ")" :: rest =>
    return (← parseOperand value, ← blockId block) :: (← pairs rest)
  | ws => throw s!"expected (value block), got {ws}"

/-- The name of a symbol: `&embed`, `%func`, `$global` or `.`. -/
def symbol (word : String) : P String :=
  if word == "." || word.startsWith "&" || word.startsWith "%" || word.startsWith "$" then
    pure word
  else throw s!"expected a symbol, got {word}"

def binOps : List (String × BinOp) :=
  [("add", .add), ("sub", .sub), ("mul", .mul), ("udiv", .udiv), ("sdiv", .sdiv),
   ("umod", .umod), ("smod", .smod), ("shl", .shl), ("shr", .shr), ("sar", .sar), ("and", .and),
   ("or", .or), ("xor", .xor), ("evm_udiv", .evmUdiv), ("evm_sdiv", .evmSdiv),
   ("evm_umod", .evmUmod), ("evm_smod", .evmSmod), ("evm_exp", .evmExp), ("evm_byte", .evmByte),
   ("evm_signextend", .evmSignExtend)]

def cmpOps : List (String × CmpOp) :=
  [("lt", .lt), ("gt", .gt), ("le", .le), ("ge", .ge), ("slt", .slt), ("sgt", .sgt),
   ("sle", .sle), ("sge", .sge), ("eq", .eq), ("ne", .ne)]

def ovfOps : List (String × OvfOp) :=
  [("uaddo", .uaddo), ("saddo", .saddo), ("usubo", .usubo), ("ssubo", .ssubo),
   ("umulo", .umulo), ("smulo", .smulo)]

def castOps : List (String × CastOp) :=
  [("zext", .zext), ("sext", .sext), ("trunc", .trunc), ("ptr_to_int", .ptrToInt),
   ("int_to_ptr", .intToPtr), ("bitcast", .bitcast)]

/-- The EVM instructions, with the number of operands each takes. -/
def evmOps : List (String × EvmOp × Nat) :=
  [("evm_address", .address, 0), ("evm_balance", .balance, 1), ("evm_origin", .origin, 0),
   ("evm_caller", .caller, 0), ("evm_call_value", .callValue, 0),
   ("evm_calldata_load", .calldataLoad, 1), ("evm_calldata_size", .calldataSize, 0),
   ("evm_calldata_copy", .calldataCopy, 3), ("evm_code_size", .codeSize, 0),
   ("evm_code_copy", .codeCopy, 3), ("evm_gas_price", .gasPrice, 0),
   ("evm_ext_code_size", .extCodeSize, 1), ("evm_ext_code_hash", .extCodeHash, 1),
   ("evm_ext_code_copy", .extCodeCopy, 4), ("evm_return_data_size", .returnDataSize, 0),
   ("evm_return_data_copy", .returnDataCopy, 3), ("evm_block_hash", .blockHash, 1),
   ("evm_coin_base", .coinbase, 0), ("evm_timestamp", .timestamp, 0),
   ("evm_number", .number, 0), ("evm_prev_randao", .prevRandao, 0),
   ("evm_gas_limit", .gasLimit, 0), ("evm_chain_id", .chainId, 0),
   ("evm_self_balance", .selfBalance, 0), ("evm_base_fee", .baseFee, 0),
   ("evm_blob_hash", .blobHash, 1), ("evm_blob_base_fee", .blobBaseFee, 0),
   ("evm_gas", .gas, 0), ("evm_code_load", .codeLoad, 1), ("evm_mload", .mload, 1),
   ("evm_mstore", .mstore, 2), ("evm_sload", .sload, 1),
   ("evm_sstore", .sstore, 2),
   ("evm_tload", .tload, 1), ("evm_tstore", .tstore, 2), ("evm_keccak256", .keccak256, 2),
   ("evm_mcopy", .mcopy, 3), ("evm_mstore8", .mstore8, 2), ("evm_log0", .log 0, 2),
   ("evm_log1", .log 1, 3), ("evm_log2", .log 2, 4), ("evm_log3", .log 3, 5),
   ("evm_log4", .log 4, 6), ("evm_create", .create, 3), ("evm_create2", .create2, 4),
   ("evm_call", .call, 7), ("evm_static_call", .staticCall, 6),
   ("evm_delegate_call", .delegateCall, 6), ("evm_add_mod", .addMod, 3),
   ("evm_mul_mod", .mulMod, 3)]

/-- The words of a statement after its name, without parentheses or commas, as operands. -/
def operands (args : List String) : P (List Operand) :=
  (args.filter fun w => w != "(" && w != ")" && w != ",").mapM parseOperand

/-- An instruction from its name and the words after it. -/
def parseInst (name : String) (args : List String) : P Inst := do
  let ops := fun () => operands args
  if let some op := binOps.lookup name then
    let [a, b] ← ops () | throw s!"{name} takes two operands"
    return .bin op a b
  if let some op := cmpOps.lookup name then
    let [a, b] ← ops () | throw s!"{name} takes two operands"
    return .cmp op a b
  if let some op := ovfOps.lookup name then
    let [a, b] ← ops () | throw s!"{name} takes two operands"
    return .ovf op a b
  if let some op := castOps.lookup name then
    let [a, ty] := args | throw s!"{name} takes an operand and a type"
    return .cast op (← parseOperand a) (← parseTy ty)
  if let some (op, arity) := evmOps.lookup name then
    let args ← ops ()
    unless args.length == arity do throw s!"{name} takes {arity} operands"
    return .evm op args
  match name, args with
  | "is_zero", [a] => return .isZero (← parseOperand a)
  | "not", [a] => return .not (← parseOperand a)
  | "neg", [a] => return .neg (← parseOperand a)
  | "clz", [a] => return .clz (← parseOperand a)
  | "ctz", [a] => return .ctz (← parseOperand a)
  | "select", [c, a, b] =>
    return .select (← parseOperand c) (← parseOperand a) (← parseOperand b)
  | "mload", [addr, ty] => return .mload (← parseOperand addr) (← parseTy ty)
  | "mstore", [addr, value, ty] =>
    return .mstore (← parseOperand addr) (← parseOperand value) (← parseTy ty)
  | "memzero", [dest, len] => return .memzero (← parseOperand dest) (← parseOperand len)
  | "evm_malloc", [size] => return .malloc (← parseOperand size)
  | "alloca", [ty] => return .alloca (← parseTy ty)
  | "sym_addr", [s] => return .symAddr (← symbol s)
  | "sym_size", [s] => return .symSize (← symbol s)
  | "insert_value", [agg, index, value] =>
    return .insertValue (← parseOperand agg) (← parseOperand index) (← parseOperand value)
  | "extract_value", [agg, index] =>
    return .extractValue (← parseOperand agg) (← parseOperand index)
  | "evm_keccak256_words", _ => return .keccakWords (← ops ())
  | "call", callee :: rest =>
    unless callee.startsWith "%" do throw s!"call of {callee}"
    return .call (callee.drop 1).toString (← operands rest)
  | _, _ => throw s!"unsupported instruction {name} {args}"

/-- A terminator from its name and the words after it, or `none` if the name is not one. -/
def parseTerm? (name : String) (args : List String) : P (Option Term) := do
  match name, args with
  | "jump", [dest] => return some (.jump (← blockId dest))
  | "br", [c, nz, z] => return some (.br (← parseOperand c) (← blockId nz) (← blockId z))
  | "br_table", scrutinee :: rest =>
    let (default, cases) := match rest with
      | w :: rest' => if w.startsWith "block" then (some w, rest') else (none, rest)
      | [] => (none, [])
    let default ← default.mapM blockId
    return some (.brTable (← parseOperand scrutinee) default (← pairs cases))
  | "return", rest => return some (.ret (← operands rest))
  | "evm_return", [a, l] => return some (.evmReturn (← parseOperand a) (← parseOperand l))
  | "evm_revert", [a, l] => return some (.evmRevert (← parseOperand a) (← parseOperand l))
  | "evm_stop", [] => return some .evmStop
  | "evm_invalid", [] => return some .evmInvalid
  | "unreachable", [] => return some .unreachable
  | _, _ => return none

/-- A block in the making: its phis and statements so far, last first. -/
structure OpenBlock where
  id : Nat
  phis : List Phi := []
  body : List Stmt := []

/-- Add a statement line, without its `;`, to the block; a terminator closes it. -/
def statement (b : OpenBlock) (line : String) : P (OpenBlock ⊕ Block) := do
  let ws := tokens line
  let (dsts, rest) ← match ws.span (· != "=") with
    | (_, []) => pure ([], ws)
    | (lhs, _ :: rhs) =>
      let decls := lhs.filter fun w => w != "(" && w != ")" && w != ","
      pure (← decls.mapM parseDecl, rhs)
  let name :: args := rest | throw s!"empty statement: {line}"
  if name == "phi" then
    let [(dst, ty)] := dsts | throw s!"phi defines one value: {line}"
    return .inl { b with phis := ⟨dst, ty, ← pairs args⟩ :: b.phis }
  if dsts.isEmpty then
    if let some term ← parseTerm? name args then
      return .inr ⟨b.id, b.phis.reverse, b.body.reverse, term⟩
  return .inl { b with body := ⟨dsts, ← parseInst name args⟩ :: b.body }

/-- `%name(v0.T, …) -> R {` after `func` and its hints and linkage. -/
def funcHeader (line : String) : P (String × List (Nat × Ty) × List Ty) := do
  let some start := line.find? (· == '%') | throw s!"no function name: {line}"
  let rest := (line.sliceFrom start).toString.drop 1 |>.toString
  let name := (rest.takeWhile (· != '(')).toString
  let afterName := (rest.dropWhile (· != '(')).toString
  let params := (afterName.drop 1 |>.takeWhile (· != ')')).toString
  let params ← (params.splitOn ",").map String.trimAscii |>.filter (!·.isEmpty)
    |>.mapM fun p => parseDecl (tokens p.toString).getLast!
  let afterParams := (afterName.dropWhile (· != ')')).toString.drop 1 |>.toString
  let rets ← match afterParams.splitOn "->" with
    | [_, ret] =>
      let ret := ret.replace "{" "" |>.replace "(" "" |>.replace ")" ""
      (ret.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.mapM parseTy
    | _ => pure []
  return (name, params, rets)

/-- The lines of a text, trimmed, without empty ones. -/
def lines (text : String) : List String :=
  (text.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- A module and its objects from the lines of the text `ModuleWriter` prints. -/
def parseLines (lines : List String) : P (Module × List Object) := do
  let mut structs : List (String × List Ty) := []
  let mut funcs : List Func := []
  let mut objects : List Object := []
  -- The function, block and object being read, if any.
  let mut func : Option (String × List (Nat × Ty) × List Ty × List Block) := none
  let mut block : Option OpenBlock := none
  let mut object : Option (String × List Section) := none
  let mut sect : Option Section := none
  -- Inside an enum declaration, which the subset does not use.
  let mut inEnum := false
  for line in lines do
    if inEnum then
      inEnum := line != "};"
    else if let some (name, params, rets, blocks) := func then
      if line == "}" then
        if block.isSome then throw s!"block of {name} has no terminator"
        funcs := ⟨name, params, rets, blocks.reverse⟩ :: funcs
        func := none
      else if line.endsWith ":" then
        if block.isSome then throw s!"block of {name} has no terminator"
        block := some { id := ← blockId (line.dropEnd 1).toString }
      else
        let some b := block | throw s!"statement outside a block: {line}"
        match ← statement b (line.dropEndWhile (· == ';')).toString with
        | .inl b => block := some b
        | .inr done =>
          func := some (name, params, rets, done :: blocks)
          block := none
    else if let some (oname, sections) := object then
      if let some s := sect then
        if line == "}" then
          sect := none
          object := some (oname, { s with embeds := s.embeds.reverse } :: sections)
        else
          match tokens (line.dropEndWhile (· == ';')).toString with
          | ["entry", f] => sect := some { s with entry := (f.drop 1).toString }
          | ["include", _] => pure ()
          | ["embed", source, "as", sym] =>
            unless source.startsWith "." do throw s!"external embed {source}"
            sect := some { s with embeds := (sym, (source.drop 1).toString) :: s.embeds }
          | _ => throw s!"unsupported section directive {line}"
      else if line == "}" then
        objects := ⟨oname, sections.reverse⟩ :: objects
        object := none
      else
        match tokens line with
        | ["section", name, "{"] => sect := some ⟨name, "", []⟩
        | _ => throw s!"expected a section: {line}"
    else if line.startsWith "target" || line.startsWith "declare" then
      pure ()
    -- A global is not part of the subset; an instruction or directive that names one is an
    -- error.
    else if line.startsWith "global " then
      pure ()
    else if line.startsWith "type " && (line.splitOn "= enum {").length == 2 then
      inEnum := !line.endsWith "};"
    else if line.startsWith "type " then
      let ws := tokens line
      let name :: _ := ws.drop 1 | throw s!"bad type: {line}"
      let body := (line.dropWhile (· != '{')).toString
      unless body.startsWith "{" do throw s!"unsupported type declaration: {line}"
      let fields := body.drop 1 |>.takeWhile (· != '}') |>.toString
      let fields ← (fields.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
        |>.mapM parseTy
      structs := ((name.drop 1).toString, fields) :: structs
    else if line.startsWith "func " then
      let (name, params, rets) ← funcHeader line
      func := some (name, params, rets, [])
    else if line.startsWith "object " then
      match tokens line with
      | ["object", name, "{"] => object := some ((name.drop 1).toString, [])
      | _ => throw s!"bad object: {line}"
    else throw s!"unsupported declaration: {line}"
  if func.isSome || object.isSome then throw "unterminated function or object"
  return (⟨structs.reverse, funcs.reverse⟩, objects.reverse)

/-- A module from the text `ModuleWriter` prints. -/
def parseModule (text : String) : P Module := (·.1) <$> parseLines (lines text)

/-- The lines of the text's object declarations, and the other lines.  An object is declared
    at the top level, from `object @name {` to the `}` that closes it. -/
def splitObjects (lines : List String) : List String × List String :=
  let (objs, rest, _) := lines.foldl (init := ([], [], 0)) fun (objs, rest, depth) line =>
    if depth == 0 && !line.startsWith "object " then (objs, line :: rest, depth)
    else
      let depth := if line.endsWith "{" then depth + 1 else if line == "}" then depth - 1
        else depth
      (line :: objs, rest, depth)
  (objs.reverse, rest.reverse)

/-- The bytes a string of hex digits spells. -/
def hexBytes (digits : String) : P ByteArray := do
  let digit (c : Char) : P Nat :=
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw s!"not a hex digit: {c}"
  let rec go : List Char → ByteArray → P ByteArray
    | hi :: lo :: rest, acc => do
      go rest (acc.push (UInt8.ofNat (16 * (← digit hi) + (← digit lo))))
    | [], acc => pure acc
    | _, _ => throw "odd number of hex digits"
  go digits.toList ByteArray.empty

/-- The variant of an enum as serde writes it: a string for a variant without data, else an
    object of one field, the variant's name. -/
def variant (json : Json) : P (String × Json) :=
  match json with
  | .str name => pure (name, .null)
  | .obj fields =>
    match fields.toList with
    | [(name, value)] => pure (name, value)
    | _ => throw s!"expected one variant, got {json.compress}"
  | _ => throw s!"expected a variant, got {json.compress}"

def parseSlot (json : Json) : P Slot := do
  match ← variant json with
  | ("value", v) => return .value (← v.getNat?)
  | ("imm", v) => match (← v.getStr?).toNat? with
    | some n => return .imm n
    | none => throw s!"bad immediate {v.compress}"
  | ("func_return", _) => return .funcReturn
  | ("call_return", _) => return .callReturn
  | (name, _) => throw s!"unknown stack slot {name}"

def parseLocation (json : Json) : P SpillLocation := do
  match ← variant json with
  | ("memory", v) => return .memory (← v.getNat?)
  | ("frame", v) => return .frame (← v.getNat?)
  | ("rematerialized", _) => return .rematerialized
  | (name, _) => throw s!"unknown spill location {name}"

def parsePoint (json : Json) : P CodePoint := do
  match ← variant json with
  | ("entry", _) => return .entry
  | ("before", v) => return .before (← v.getObjValAs? Nat "block") (← v.getObjValAs? Nat "index")
  | ("after", v) => return .after (← v.getObjValAs? Nat "block") (← v.getObjValAs? Nat "index")
  | ("case", v) =>
    return .case (← v.getObjValAs? Nat "block") (← v.getObjValAs? Nat "index")
      (← v.getObjValAs? Nat "case")
  | (name, _) => throw s!"unknown code point {name}"

def parseLabel (json : Json) : P CodeLabel := do
  match ← variant json with
  | ("block", v) =>
    return .block (← v.getObjValAs? String "func") (← v.getObjValAs? Nat "block")
  | ("func", v) => return .func (← v.getStr?)
  | ("unit", v) => return .unit (← v.getStr?)
  | ("inst", _) => return .inst
  | (name, _) => throw s!"unknown code label {name}"

def parseLowering (json : Json) : P Lowering := do
  let funcs ← (← json.getObjValAs? (Array Json) "funcs").toList.mapM fun f => do
    let blocks ← (← f.getObjValAs? (Array Json) "blocks").toList.mapM fun b => do
      return ({ block := ← b.getObjValAs? Nat "block"
                sources := ← b.getObjValAs? (List Nat) "sources"
                offset := ← b.getObjValAs? (Option Nat) "offset"
                aliasOf := ← b.getObjValAs? (Option Nat) "alias"
                entryStack := ← (← b.getObjValAs? (Array Json) "entry_stack").toList.mapM
                  parseSlot } : BlockHint)
    let spills ← (← f.getObjValAs? (Array Json) "spills").toList.mapM fun s => do
      let points (key : String) : P (List CodePoint) := do
        (← s.getObjValAs? (Array Json) key).toList.mapM parsePoint
      return ({ value := ← s.getObjValAs? Nat "value"
                location := ← parseLocation (← s.getObjVal? "location")
                stores := ← points "stores"
                reloads := ← points "reloads" } : SpillHint)
    let frame ← f.getObjVal? "frame"
    let (stable, _) ← variant (← frame.getObjVal? "stable")
    let frame : FrameHint :=
      { dynamicFrame := stable == "dynamic_frame"
        lazyFrame := ← frame.getObjValAs? Bool "lazy_frame"
        dynSpInit := (← frame.getObjValAs? (Option String) "dyn_sp_entry_init").isSome
          || (← frame.getObjValAs? Nat "dyn_sp_init_calls") != 0
        callPreserves := (← frame.getObjValAs? (Array Json) "call_preserves").size }
    return ({ name := ← f.getObjValAs? String "name"
              offset := ← f.getObjValAs? (Option Nat) "offset"
              blocks, spills, frame } : FuncHint)
  let units ← (← json.getObjValAs? (Array Json) "units").toList.mapM fun u => do
    return (← u.getObjValAs? String "name", ← u.getObjValAs? Nat "offset",
      ← u.getObjValAs? Nat "size")
  let redirects ← (← json.getObjValAs? (Array Json) "redirects").toList.mapM fun r => do
    return (← parseLabel (← r.getObjVal? "from"), ← parseLabel (← r.getObjVal? "to"))
  return { source := (parseModule (← json.getObjValAs? String "source_ir")).toOption
           machine := ← parseModule (← json.getObjValAs? String "machine_ir")
           codeSize := ← json.getObjValAs? Nat "code_size"
           arenaBase := ← json.getObjValAs? Nat "arena_base"
           dynBase := ← json.getObjValAs? Nat "dyn_base"
           entryFreePtr := ← json.getObjValAs? (Option Nat) "entry_free_ptr"
           funcs, units, redirects }

/-- The sidecar versions this reader reads: 5 adds `machine_steps` to a section's lowering,
    which `Steps/Read.lean` reads. -/
def sidecarVersions : List Nat := [4, 5]

/-- A sidecar from the JSON `fe build --emit sidecar` writes. -/
def parseSidecar (text : String) : P Sidecar := do
  let json ← Json.parse text
  let version ← json.getObjValAs? Nat "version"
  unless sidecarVersions.contains version do
    throw s!"sidecar version {version}, not one of {sidecarVersions}"
  -- The objects are read strictly, since the checker reads each section's entry from them; the
  -- rest of the module only where it is in the subset, as no check needs it.
  let (objectLines, moduleLines) := splitObjects (lines (← json.getObjValAs? String "ir"))
  let (_, objects) ← parseLines objectLines
  let module := (parseLines moduleLines).toOption.map (·.1)
  let sections ← (← json.getObjValAs? (Array Json) "sections").toList.mapM fun s => do
    let symbols ← (← s.getObjValAs? (Array Json) "symbols").toList.mapM fun sym =>
      return (← sym.getObjValAs? String "symbol", ← sym.getObjValAs? Nat "offset",
        ← sym.getObjValAs? Nat "size")
    let bytecode ← hexBytes (← s.getObjValAs? String "bytecode")
    let lowering ← match ← s.getObjVal? "lowering" with
      | .null => pure none
      | l => some <$> parseLowering l
    return (⟨← s.getObjValAs? String "name", bytecode, symbols, lowering⟩ : CodeSection)
  return ⟨← json.getObjValAs? String "object", objects, module, sections⟩

end Fe.Sonatina.Parse

namespace Fe.Sonatina

open Lean Elab Command

instance : ToExpr ByteArray where
  toExpr b := mkApp (mkConst ``ByteArray.mk) (toExpr b.data)
  toTypeExpr := mkConst ``ByteArray

deriving instance Lean.ToExpr for CodeSection
deriving instance Lean.ToExpr for Sidecar

/-- `sonatina_sidecar name "path"`: define `name : Sidecar` from the sidecar at `path`, relative
    to the project root. -/
elab "sonatina_sidecar " name:ident path:str : command => do
  let text ← IO.FS.readFile path.getString
  match Parse.parseSidecar text with
  | .error e => throwError "{path.getString}: {e}"
  | .ok sidecar =>
    let decl := Declaration.defnDecl {
      name := (← getCurrNamespace) ++ name.getId
      levelParams := []
      type := mkConst ``Sidecar
      value := toExpr sidecar
      hints := .abbrev
      safety := .safe }
    liftCoreM (addAndCompile decl)

/-- `sonatina_func name "path" "section" "entry"`: define `name : Func` as the machine IR's
    function `entry` of section `section` of the sidecar at `path`, for proofs that run it, and
    for each block `b` of it a `simp` lemma `name.block_b : name.block? b = some …`, so that a run
    finds its blocks without unfolding the whole function, a `simp` lemma
    `name.params_eq : name.params = […]`, so that a call binds its arguments, and for each value
    `k` a `br_table` case of the function tests a `simp` lemma
    `name.caseBlock_k : name.caseBlock k = b`, so that a proof names a dispatcher's arm by its
    selector, not by its block's number. -/
elab "sonatina_func " name:ident path:str sec:str fn:str : command => do
  let text ← IO.FS.readFile path.getString
  match Parse.parseSidecar text with
  | .error e => throwError "{path.getString}: {e}"
  | .ok sidecar =>
    let some f := ((sidecar.section? sec.getString).bind (·.lowering)).bind
        (·.machine.func? fn.getString)
      | throwError "{path.getString}: no machine function {fn.getString} in {sec.getString}"
    let declName := (← getCurrNamespace) ++ name.getId
    let decl := Declaration.defnDecl {
      name := declName
      levelParams := []
      type := mkConst ``Func
      value := toExpr f
      hints := .abbrev
      safety := .safe }
    liftCoreM do
      addAndCompile decl
      enableRealizationsForConst declName
    let blockTy := mkApp (mkConst ``Option [0]) (mkConst ``Block)
    for b in f.blocks do
      let lhs := mkApp2 (mkConst ``Func.block?) (mkConst declName) (toExpr b.id)
      let rhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Block) (toExpr b)
      let thm := declName ++ Name.mkSimple s!"block_{b.id}"
      liftCoreM do
        addDecl (.thmDecl {
          name := thm
          levelParams := []
          type := mkApp3 (mkConst ``Eq [1]) blockTy lhs rhs
          value := mkApp2 (mkConst ``Eq.refl [1]) blockTy rhs })
      liftTermElabM do
        Lean.Meta.addSimpTheorem Lean.Meta.simpExtension thm (post := true) (inv := false)
          .global (eval_prio default)
    let paramsTy := toTypeExpr (List (Nat × Ty))
    let params := toExpr f.params
    let thm := declName ++ `params_eq
    liftCoreM do
      addDecl (.thmDecl {
        name := thm
        levelParams := []
        type := mkApp3 (mkConst ``Eq [1]) paramsTy
          (mkApp (mkConst ``Func.params) (mkConst declName)) params
        value := mkApp2 (mkConst ``Eq.refl [1]) paramsTy params })
    liftTermElabM do
      Lean.Meta.addSimpTheorem Lean.Meta.simpExtension thm (post := true) (inv := false)
        .global (eval_prio default)
    -- The block each `br_table` case value goes to, as `Func.caseBlock` finds it.
    let keys := (f.blocks.flatMap fun b => match b.term with
      | .brTable _ _ cases => cases.filterMap fun (o, _) => match o with
        | .imm _ v => some v
        | _ => none
      | _ => []).eraseDups
    for k in keys do
      let lhs := mkApp2 (mkConst ``Func.caseBlock) (mkConst declName) (toExpr k)
      let rhs := toExpr (f.caseBlock k)
      let thm := declName ++ Name.mkSimple s!"caseBlock_{k}"
      liftCoreM do
        addDecl (.thmDecl {
          name := thm
          levelParams := []
          type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) lhs rhs
          value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) rhs })
      liftTermElabM do
        Lean.Meta.addSimpTheorem Lean.Meta.simpExtension thm (post := true) (inv := false)
          .global (eval_prio default)

end Fe.Sonatina
