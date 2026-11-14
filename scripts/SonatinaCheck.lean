import Fe.Sonatina.Check
import Fe.Sonatina.Parse

/-!
Runs the checker of bytes against machine IR (`Fe/Sonatina/Check.lean`): on the fixtures, which
it must accept where they are in its class, on mutations of their hints, which it must reject
unless the mutation changes nothing the semantics reads, on mutations of the calls of the
fixtures with internal calls, which it must reject, and on every sidecar of a directory, as
`SONATINA_CHECK_DIR` names, counting the sections it accepts and why it rejects the others.
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

#eval show IO Unit from do
  for f in ["FeConstant", "FeScalarStore", "FeERC20", "DepositContract", "Case44Bank",
      "TypedCallsTarget"] do
    let s ← IO.ofExcept
      (Parse.parseSidecar (← IO.FS.readFile s!"Fe/Sonatina/Fixtures/{f}.sidecar.json"))
    for (name, entry) in Check.entries s do
      let some code := s.section? name | continue
      let verdict := match Check.checkSection code entry with
        | .ok () => "accepted"
        | .error e => s!"rejected: {e}"
      IO.println s!"CHECK {f} {name} {verdict}"
      if Check.checkSection code entry matches .ok () then
        for (what, m) in mutations do
          let changed := m code
          unless changed.lowering == code.lowering && changed.symbols == code.symbols do
            if Check.checkSection changed entry matches .ok () then
              IO.println s!"  MUTANT ACCEPTED {what}"
        if f == "Case44Bank" && name == "runtime" then
          for (what, m) in callMutations do
            let verdict := match Check.checkSection (m code) entry with
              | .ok () => "ACCEPTED"
              | .error e => s!"rejected: {e}"
            IO.println s!"  CALL MUTANT {what}: {verdict}"

#eval show IO Unit from do
  let some dir ← IO.getEnv "SONATINA_CHECK_DIR" | return
  let mut (accepted, rejected) := (0, (#[] : Array String))
  for entry in ← System.FilePath.readDir dir do
    unless entry.fileName.endsWith ".sidecar.json" do continue
    let .ok s := Parse.parseSidecar (← IO.FS.readFile entry.path) | continue
    for (name, fn) in Check.entries s do
      let some code := s.section? name | continue
      match Check.checkSection code fn with
      | .ok () => accepted := accepted + 1
      | .error e => rejected := rejected.push e
  IO.println s!"sections accepted {accepted}, rejected {rejected.size}"
  let reasons := rejected.toList.map fun e =>
    String.ofList ((e.splitOn ": ").getLast!.toList.filter (!·.isDigit))
  for r in reasons.eraseDups do
    IO.println s!"  {(reasons.filter (· == r)).length} {r}"
