import Fe.Sonatina.FrameSafe
import Fe.Sonatina.Parse

/-!
Runs the checker of bytes against machine IR (`Fe/Sonatina/Check.lean`): on the fixtures, which
it must accept where they are in its class, on mutations of their hints, which it must reject
unless the mutation changes nothing the semantics reads, on mutations of the calls of the
fixtures with internal calls, of WETH9's message call, of a reentrancy guard's transient storage,
of a factory's creation and of a leading-zeros probe's `CLZ`, which it must reject, and on every
sidecar of a directory, as `SONATINA_CHECK_DIR` names, with a line per section and per sidecar
the reader rejects, counting the sections it accepts and why it rejects the others.
Run with `lake env lean scripts/SonatinaCheck.lean`.
-/

open Fe.Sonatina

def mapBlocks (c : CodeSection) (g : BlockHint → BlockHint) : CodeSection :=
  { c with lowering := c.lowering.map fun l => { l with funcs := l.funcs.map fun f =>
      { f with blocks := f.blocks.map g } } }

def mutations : List (String × (CodeSection → CodeSection)) :=
  [("drop the top entry slot",
      fun c => mapBlocks c fun b => { b with entryStack := b.entryStack.drop 1 }),
   ("add an entry slot",
      fun c => mapBlocks c fun b => { b with entryStack := .imm 7 :: b.entryStack }),
   ("swap the top two slots", fun c => mapBlocks c fun b => match b.entryStack with
      | x :: y :: r => { b with entryStack := y :: x :: r }
      | _ => b),
   ("move offsets by a byte",
      fun c => mapBlocks c fun b => { b with offset := b.offset.map (· + 1) }),
   ("move the initial free pointer", fun c => { c with lowering := c.lowering.map fun l =>
      { l with entryFreePtr := l.entryFreePtr.map (· + 32) } }),
   ("drop the redirects",
      fun c => { c with lowering := c.lowering.map fun l => { l with redirects := [] } }),
   ("move the symbols",
      fun c => { c with symbols := c.symbols.map fun (n, o, z) => (n, o + 1, z) })]

/-- The section with function `func`'s machine IR changed by `g`. -/
def mapFunc (func : String) (g : Func → Func) (c : CodeSection) : CodeSection :=
  { c with lowering := c.lowering.map fun l => { l with machine := { l.machine with
      funcs := l.machine.funcs.map fun f => if f.name == func then g f else f } } }

/-- Block `id` of a function changed by `g`. -/
def mapBlock (id : Nat) (g : Block → Block) (f : Func) : Func :=
  { f with blocks := f.blocks.map fun b => if b.id == id then g b else b }

/-- The section with byte `i` of its code `v`. -/
def setByte (i : Nat) (v : UInt8) (c : CodeSection) : CodeSection :=
  { c with bytecode := c.bytecode.set! i v }

/-- Mutations of `Case44Bank`'s runtime, whose block 11 calls `credit` twice, the first call's
    bytes at 57: `PUSH1 0x44` (the continuation) at 62, `PUSH1 0x79` (`credit`) at 65, `JUMP`. -/
def callMutations : List (String × (CodeSection → CodeSection)) :=
  [("a wrong continuation", setByte 63 0x45),
   ("the callee's offset off by one", setByte 66 0x7a),
   ("the arguments swapped", mapFunc "contract_runtime_root_Case44Bank" <| mapBlock 11 fun b =>
      { b with body := b.body.map fun s => match s.inst with
        | .call g args => { s with inst := .call g args.reverse }
        | _ => s }),
   ("a call to a returning function without a continuation",
      -- `PUSH1 0x44` as two `JUMPDEST`s.
      fun c => setByte 62 0x5b (setByte 63 0x5b c)),
   ("an unreachable after a returning call", mapFunc "contract_runtime_root_Case44Bank" <|
      mapBlock 11 fun b => { b with body := b.body.take 2, term := .unreachable })]

/-- WETH9's runtime block 36 with its message call's operands changed by `g`: the call is
    `evm_call v0 v115 v119 v130 0 224 0` (gas, the caller, the amount, the arguments' offset and
    size, the return window's offset and size). -/
def mapCall (g : List Operand → List Operand) : CodeSection → CodeSection :=
  mapFunc "contract_runtime_root_WETH9" <| mapBlock 36 fun b =>
    { b with body := b.body.map fun s => match s.inst with
      | .evm .call args => { s with inst := .evm .call (g args) }
      | _ => s }

/-- Mutations of WETH9's message call, each of which the bytes contradict. -/
def messageMutations : List (String × (CodeSection → CodeSection)) :=
  [("a wrong gas operand", mapCall fun
      | _ :: rest => .imm 256 0 :: rest
      | args => args),
   ("the value and the address swapped", mapCall fun
      | g :: a :: v :: rest => g :: v :: a :: rest
      | args => args),
   ("the return window off by a word", mapCall fun
      | [g, a, v, ap, al, .imm b rp, rl] => [g, a, v, ap, al, .imm b (rp + 32), rl]
      | args => args),
   ("the arguments' window off by a word", mapCall fun
      | [g, a, v, ap, .imm b al, rp, rl] => [g, a, v, ap, .imm b (al + 32), rp, rl]
      | args => args)]

/-- The reentrancy guard's runtime block `id` with its statements changed by `g`. -/
def mapGuard (id : Nat) (g : Inst → Inst) : CodeSection → CodeSection :=
  mapFunc "contract_runtime_root_B" <| mapBlock id fun b =>
    { b with body := b.body.map fun s => { s with inst := g s.inst } }

/-- Mutations of the reentrancy guard's transient storage: block 12 sets the lock with
    `evm_tstore 1 1`, block 11 reads it with `evm_tload 1`, block 24 stores with `evm_sstore 0 v18`
    and clears the lock with `evm_tstore 1 0`. -/
def transientMutations : List (String × (CodeSection → CodeSection)) :=
  [("a wrong transient slot written", mapGuard 12 fun
      | .evm .tstore [_, v] => .evm .tstore [.imm 256 2, v]
      | i => i),
   ("a wrong transient slot read", mapGuard 11 fun
      | .evm .tload [_] => .evm .tload [.imm 256 2]
      | i => i),
   ("tstore for sstore", mapGuard 24 fun
      | .evm .sstore args => .evm .tstore args
      | i => i),
   ("sstore for tstore", mapGuard 24 fun
      | .evm .tstore args => .evm .sstore args
      | i => i)]

/-- The factory's runtime block 13 with its creation changed by `g`: the creation is
    `evm_create2 0 v34 v29 v18` (the value, the init code's offset and size, the salt), the init
    code `v23` bytes of the child's code at `v34` followed by two argument words. -/
def mapCreate (g : List Operand → Inst) : CodeSection → CodeSection :=
  mapFunc "contract_runtime_root_Factory" <| mapBlock 13 fun b =>
    { b with body := b.body.map fun s => match s.inst with
      | .evm .create2 args => { s with inst := g args }
      | _ => s }

/-- Mutations of the factory's creation, each of which the bytes contradict. -/
def createMutations : List (String × (CodeSection → CodeSection)) :=
  [("a wrong value operand", mapCreate fun
      | _ :: rest => .evm .create2 (.imm 256 1 :: rest)
      | args => .evm .create2 args),
   ("the init code without its argument words", mapCreate fun
      | [v, p, _, z] => .evm .create2 [v, p, .var 23, z]
      | args => .evm .create2 args),
   ("the init code's offset and size swapped", mapCreate fun
      | [v, p, l, z] => .evm .create2 [v, l, p, z]
      | args => .evm .create2 args),
   ("a wrong salt", mapCreate fun
      | [v, p, l, _] => .evm .create2 [v, p, l, .var 23]
      | args => .evm .create2 args),
   ("create for create2", mapCreate fun args => .evm .create (args.take 3))]

/-! Mutations of a section with memory spills (`NestedArrayCaller`, Fe's
    `msg_nested_array_arg.fe`), each of which the spill-aware checker must reject. -/

/-- The bytes `bs` from offset `i`. -/
def setBytes (i : Nat) (bs : List UInt8) (c : CodeSection) : CodeSection :=
  { c with bytecode := (bs.zipIdx.foldl (fun b (v, k) => b.set! (i + k) v) c.bytecode) }

/-- The big-endian bytes of `v`, `n` of them. -/
def beBytes (n v : Nat) : List UInt8 :=
  (List.range n).reverse.map fun k => UInt8.ofNat (v / 256 ^ k % 256)

/-- The sites `PUSHn w; op` of the code with `w` a word of `words`: the push's offset, width and
    word. -/
def wordSites (c : CodeSection) (words : List Nat) (op : Ethereum.Operation) :
    List (Nat × Nat × Nat) :=
  let is := Check.codeInstrs c.bytecode
  (is.zip (is.drop 1)).filterMap fun ((pc, o, a, nx), (_, o', _, _)) =>
    match a with
    | some w => if o' == op && words.contains w && o != .PUSH0 then some (pc, nx - pc - 1, w)
      else none
    | none => none

/-- The section with the spill word of value `v` in the record `w`. -/
def setSpillWord (v w : Nat) (c : CodeSection) : CodeSection :=
  { c with lowering := c.lowering.map fun l => { l with funcs := l.funcs.map fun f =>
      { f with spills := f.spills.map fun (x, loc) =>
        if x == v then (x, .memory w) else (x, loc) } } }

/-- The spill-aware checker's verdict on section `name` of `s` changed by `m`, its plan the
    walk's on the changed section, or `plan` if given. -/
def spillVerdict (s : Sidecar) (name entry : String) (m : CodeSection → CodeSection)
    (plan : Option SpillPlan := none) : String :=
  match s.section? name with
  | none => "no section"
  | some code =>
    let code' := m code
    let p := plan.getD (code'.spillPlan entry)
    match Check.checkSection code' entry p with
    | .ok () => "ACCEPTED"
    | .error e => s!"rejected: {e}"

/-- The spill mutations of a section: each a name and its verdict. -/
def spillMutations (s : Sidecar) (name entry : String) : List (String × String) := Id.run do
  let some code := s.section? name | return []
  let plan := code.spillPlan entry
  let spills := plan.flatMap (·.2)
  let words := spills.map (·.word)
  let reloads := wordSites code words .MLOAD
  let stores := wordSites code words .MSTORE
  let mut out := []
  -- Two reloads of different words, their words swapped.
  match reloads.find? fun (_, n, _) => n > 0, reloads with
  | some (p1, n1, w1), _ =>
    match reloads.find? fun (p2, n2, w2) => p2 != p1 && n2 == n1 && w2 != w1 with
    | some (p2, _, w2) =>
      out := out ++ [("swap two reload words in the bytes", spillVerdict s name entry
        (setBytes (p1 + 1) (beBytes n1 w2) ∘ setBytes (p2 + 1) (beBytes n1 w1)))]
    | none => out := out ++ [("swap two reload words in the bytes", "NO SITE")]
  | none, _ => out := out ++ [("swap two reload words in the bytes", "NO SITE")]
  -- A spill store dropped: `PUSHn w MSTORE` as `POP` and `JUMPDEST`s.
  match stores.head? with
  | some (pc, n, w) =>
    out := out ++ [("drop a spill store from the bytes", spillVerdict s name entry
      (setBytes pc (0x50 :: List.replicate (n + 1) 0x5b)))]
    out := out ++ [("store to the wrong word", spillVerdict s name entry
      (setBytes (pc + 1) (beBytes n (w + 32))))]
  | none => out := out ++ [("drop a spill store from the bytes", "NO SITE")]
  -- A spill word changed in the record only.
  match spills.head? with
  | some sp => out := out ++ [("change a spill word in the record only",
      spillVerdict s name entry (setSpillWord sp.value (sp.word + 32)))]
  | none => pure ()
  -- A word reused before a reload: a value stored alone at its word, before a reload of
  -- another word in its block, stored (in the record and the bytes) at the reloaded word.
  let offs := ((code.lowering.map (·.funcs)).getD []).flatMap (·.blocks) |>.filterMap (·.offset)
  let blockOf := fun (pc : Nat) => (offs.filter (· ≤ pc)).foldl max 0
  let single := spills.filter fun sp => (spills.filter (·.word == sp.word)).length == 1
  let cand := stores.findSome? fun (pc, n, wu) =>
    (single.find? (·.word == wu)).bind fun u =>
      (reloads.find? fun (r, n', wv) => r > pc && n' == n && wv != wu &&
        blockOf r == blockOf pc).map fun (_, _, wv) => (pc, n, u.value, wv)
  match cand with
  | some (pc, n, u, wv) => out := out ++ [("reload a value after its word was reused",
      spillVerdict s name entry (setSpillWord u wv ∘ setBytes (pc + 1) (beBytes n wv)))]
  | none => out := out ++ [("reload a value after its word was reused", "NO SITE")]
  -- A value the bytes reload with no reload point in the plan.
  match spills.find? (!·.reloads.isEmpty) with
  | some sp =>
    let plan' := plan.map fun (f, fp) =>
      (f, fp.map fun (x : Spill) => if x.value == sp.value then { x with reloads := [] } else x)
    out := out ++ [("mark a value as reloaded where the plan does not have it live",
      spillVerdict s name entry id plan')]
  | none => pure ()
  return out

/-- The section with every `CLZ` of its code (opcode `0x1e`) the opcode `op`. -/
def clzBytes (op : UInt8) (c : CodeSection) : CodeSection :=
  let bytes := (Check.codeInstrs c.bytecode).foldl
    (fun b (pc, o, _) => if o == .CLZ then b.set! pc op else b) c.bytecode
  { c with bytecode := bytes }

/-- The section with every `clz` of its machine IR the instruction `g`. -/
def clzInsts (g : Operand → Inst) (c : CodeSection) : CodeSection :=
  { c with lowering := c.lowering.map fun l => { l with machine := { l.machine with
      funcs := l.machine.funcs.map fun f => { f with blocks := f.blocks.map fun b =>
        { b with body := b.body.map fun s => match s.inst with
          | .clz a => { s with inst := g a }
          | _ => s } } } } }

/-- Mutations of a leading-zeros probe's `CLZ`, each of which the bytes contradict. -/
def clzMutations : List (String × (CodeSection → CodeSection)) :=
  [("NOT for CLZ in the bytes", clzBytes 0x19), ("ISZERO for CLZ in the bytes", clzBytes 0x15),
   ("not for clz in the IR", clzInsts .not), ("is_zero for clz in the IR", clzInsts .isZero)]

#eval show IO Unit from do
  for f in ["FeConstant", "FeScalarStore", "FeERC20", "DepositContract", "Case44Bank",
      "TypedCallsTarget", "WETH9", "ReentrancyMutex", "Factory", "BitsProbe",
      "NestedArrayCaller"] do
    let s ← IO.ofExcept
      (Parse.parseSidecar (← IO.FS.readFile s!"Fe/Sonatina/Fixtures/{f}.sidecar.json"))
    for (name, entry) in Check.entries s do
      let some code := s.section? name | continue
      let verdict := match Check.checkSection code entry (code.spillPlan entry) with
        | .ok () => "accepted"
        | .error e => s!"rejected: {e}"
      let plain := (Check.checkSection code entry [] matches .ok ()) &&
        ((code.lowering.map (·.funcs.all (·.spills.isEmpty))).getD true)
      IO.println s!"CHECK {f} {name} {verdict} (check: {if plain then "accepted" else "rejected"})"
      if Check.checkSection code entry (code.spillPlan entry) matches .ok () then
        for (what, m) in mutations do
          let changed := m code
          unless changed.lowering == code.lowering && changed.symbols == code.symbols do
            if Check.checkSection changed entry (changed.spillPlan entry) matches .ok () then
              IO.println s!"  MUTANT ACCEPTED {what}"
        if f == "NestedArrayCaller" && name == "runtime" then
          for (what, v) in spillMutations s name entry do
            IO.println s!"  SPILL MUTANT {what}: {v}"
        if f == "Case44Bank" && name == "runtime" then
          for (what, m) in callMutations do
            let verdict := match Check.checkSection (m code) entry ((m code).spillPlan entry) with
              | .ok () => "ACCEPTED"
              | .error e => s!"rejected: {e}"
            IO.println s!"  CALL MUTANT {what}: {verdict}"
        if f == "WETH9" && name == "runtime" then
          for (what, m) in messageMutations do
            let changed := m code
            let verdict := if changed.lowering == code.lowering then "UNCHANGED"
              else match Check.checkSection changed entry (changed.spillPlan entry) with
                | .ok () => "ACCEPTED"
                | .error e => s!"rejected: {e}"
            IO.println s!"  MESSAGE MUTANT {what}: {verdict}"
        if f == "ReentrancyMutex" && name == "runtime" then
          for (what, m) in transientMutations do
            let changed := m code
            let verdict := if changed.lowering == code.lowering then "UNCHANGED"
              else match Check.checkSection changed entry (changed.spillPlan entry) with
                | .ok () => "ACCEPTED"
                | .error e => s!"rejected: {e}"
            IO.println s!"  TRANSIENT MUTANT {what}: {verdict}"
        if f == "BitsProbe" && name == "runtime" then
          for (what, m) in clzMutations do
            let changed := m code
            let verdict := if changed.lowering == code.lowering && changed.bytecode == code.bytecode
              then "UNCHANGED"
              else match Check.checkSection changed entry (changed.spillPlan entry) with
                | .ok () => "ACCEPTED"
                | .error e => s!"rejected: {e}"
            IO.println s!"  CLZ MUTANT {what}: {verdict}"
        if f == "Factory" && name == "runtime" then
          for (what, m) in createMutations do
            let changed := m code
            let verdict := if changed.lowering == code.lowering then "UNCHANGED"
              else match Check.checkSection changed entry (changed.spillPlan entry) with
                | .ok () => "ACCEPTED"
                | .error e => s!"rejected: {e}"
            IO.println s!"  CREATE MUTANT {what}: {verdict}"

#eval show IO Unit from do
  let some dir ← IO.getEnv "SONATINA_CHECK_DIR" | return
  let mut (accepted, acceptedS, rejected, unparsed) := (0, 0, (#[] : Array String), 0)
  for entry in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
    unless entry.fileName.endsWith ".sidecar.json" do continue
    match Parse.parseSidecar (← IO.FS.readFile entry.path) with
    | .error e =>
      unparsed := unparsed + 1
      IO.println s!"UNPARSED {entry.fileName}: {e}"
    | .ok s =>
      for (name, fn) in Check.entries s do
        let some code := s.section? name | continue
        let spills := !(code.lowering.map (·.funcs.all (·.spills.isEmpty))).getD true
        let plain := match Check.checkSection code fn [] with
          | .ok () => if spills then .error "memory spills" else .ok ()
          | e => e
        let withSpills := if spills then Check.checkSection code fn (code.spillPlan fn) else plain
        let say := fun (r : Except String Unit) => match r with
          | .ok () => "accepted"
          | .error e => s!"rejected: {e}"
        IO.println s!"SECTION {entry.fileName} {name} check={say plain} checkSpills={say withSpills}"
        if plain matches .ok () then accepted := accepted + 1
        if withSpills matches .ok () then acceptedS := acceptedS + 1
        match withSpills with
        | .error e => rejected := rejected.push e
        | .ok () => pure ()
  IO.println s!"sidecars unparsed {unparsed}; sections accepted by check {accepted}, by checkSpills {acceptedS}, rejected by checkSpills {rejected.size}"
  let reasons := rejected.toList.map fun e =>
    String.ofList ((e.splitOn ": ").getLast!.toList.filter (!·.isDigit))
  for r in reasons.eraseDups do
    IO.println s!"  {(reasons.filter (· == r)).length} {r}"
