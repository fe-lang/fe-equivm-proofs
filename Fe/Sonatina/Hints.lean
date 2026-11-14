import Fe.Sonatina.Syntax
import Ethereum.Semantics

/-!
# Checking the lowering record against the bytes

The hints of a sidecar's lowering record are untrusted, and a checker of the bytes against the
machine IR will refute a wrong one.  `check` refutes the cheap cases now, by a linear scan of
each laid-out block's bytes:

- every function and block offset is the start of an instruction, and every function offset is
  the function's symbol;
- every machine block the IR reaches has a place: an offset, a block it is emitted as, or a
  chain of redirects to one;
- no instruction of a block reads below the block's recorded entry stack;
- every jump whose target is a pushed constant goes to a successor of the block in the machine
  IR, to an outlined unit, or to a function, which the scan then steps over as a call: it
  consumes the arguments and the continuation and leaves the results;
- a block leaves at least as many items as the entry stack of the successor it jumps or falls to.

A failure is a finding about the instrumentation or the compiler, not about the semantics.
-/

namespace Fe.Sonatina.Hints

open Ethereum Ethereum.EVM

/-- An instruction of the code: what it is, its immediate, and where the next one starts. -/
def decodeAt (code : ByteArray) (pc : Nat) : Option (Operation × Option Nat × Nat) :=
  (decode code (.ofNat pc)).map fun (op, arg) =>
    (op, (arg.map (·.1.toNat)).orElse fun _ => if op == .PUSH0 then some 0 else none,
      pc + 1 + (arg.map (·.2)).getD 0)

/-- The offsets at which the instructions of the first `size` bytes start. -/
def starts (code : ByteArray) (size : Nat) : Std.HashSet Nat := Id.run do
  let mut pc := 0
  let mut set : Std.HashSet Nat := {}
  for _ in [:size] do
    if pc ≥ size then break
    set := set.insert pc
    pc := ((decodeAt code pc).map (·.2.2)).getD (pc + 1)
  return set

/-- The successors of a block in its function. -/
def successors (f : Func) (block : Nat) : List Nat :=
  match (f.block? block).map Fe.Sonatina.Block.term with
  | some (.jump dest) => [dest]
  | some (.br _ nz z) => [nz, z]
  | some (.brTable _ default cases) => default.toList ++ cases.map (·.2)
  | _ => []

/-- Where the code a label names starts: a block's offset, or the place of the block it is
    emitted as, or of where the late merges redirected it, at most `depth` steps away. -/
def place (low : Lowering) : Nat → CodeLabel → Option Nat
  | 0, _ => none
  | depth + 1, label =>
    let redirected := (low.redirects.lookup label).bind (place low depth)
    match label with
    | .block func block => do
      let f ← low.funcs.find? (·.name == func)
      let b ← f.blocks.find? (·.block == block)
      b.offset <|> (b.aliasOf.bind fun a => place low depth (.block func a)) <|> redirected <|>
        -- A function merged into another has the other's code, block for block.
        (if f.offset.isNone then place low depth (.func func) else none)
    | .func name => ((low.funcs.find? (·.name == name)).bind (·.offset)) <|> redirected
    | .unit name => ((low.units.find? (·.1 == name)).map (·.2.1)) <|> redirected
    | .inst => none

/-- The failures of the hints of section `code`, each in a few words. -/
def check (code : CodeSection) : List String := Id.run do
  let some low := code.lowering | return ["no lowering record"]
  let bytes := code.bytecode
  let starts := starts bytes low.codeSize
  let mut failures : Array String := #[]
  let placeOf (func : String) (block : Nat) := place low 16 (.block func block)
  -- Where code starts that a scan must not run into: blocks, units and functions.
  let boundaries : Std.HashSet Nat := Std.HashSet.ofList
    (low.funcs.flatMap (fun f => f.offset.toList ++ f.blocks.filterMap (·.offset)) ++
      low.units.map (·.2.1))
  let entries : List (Nat × Func) := low.funcs.filterMap fun f => do
    return (← f.offset, ← low.machine.func? f.name)
  for f in low.funcs do
    if let some offset := f.offset then
      unless starts.contains offset do failures := failures.push s!"{f.name} starts mid-instruction"
      unless (code.symbols.lookup s!"%{f.name}").map (·.1) == some offset do
        failures := failures.push s!"{f.name} starts at {offset}, not at its symbol"
    let some mf := low.machine.func? f.name
      | failures := failures.push s!"no machine IR of {f.name}"
        continue
    let height (block : Nat) : Option Nat :=
      (f.blocks.find? (·.block == block)).map (·.entryStack.length)
    for b in f.blocks do
      if (mf.block? b.block).isSome && (placeOf f.name b.block).isNone then
        failures := failures.push s!"{f.name} block{b.block} has no place"
      let some offset := b.offset | continue
      unless starts.contains offset do
        failures := failures.push s!"{f.name} block{b.block} starts mid-instruction"
        continue
      let succs := (successors mf b.block).filterMap fun s => do
        return (← placeOf f.name s, s)
      -- The successor at `pc` must find at least its entry stack.
      let mut d := b.entryStack.length
      let mut pc := offset
      let mut pushed : Option Nat := none
      for _ in [:low.codeSize] do
        if pc != offset && boundaries.contains pc then
          match succs.find? (·.1 == pc) with
          | some (_, s) =>
            if d < (height s).getD 0 then
              failures := failures.push s!"{f.name} block{b.block} falls to block{s} short"
          | none =>
            failures := failures.push s!"{f.name} block{b.block} falls to {pc}, no successor"
          break
        let some (op, arg, next) := decodeAt bytes pc
          | failures := failures.push s!"{f.name} block{b.block}: no instruction at {pc}"
            break
        -- EVMLean gives `INVALID` no stack effect.
        if op == .INVALID then break
        let (some pops, some pushes) := (δ op, α op)
          | failures := failures.push s!"{f.name} block{b.block}: {repr op} at {pc}"
            break
        if d < pops then
          failures := failures.push s!"{f.name} block{b.block} reads below its stack at {pc}"
          break
        d := d - pops + pushes
        if op == .JUMP || op == .JUMPI then
          if let some target := pushed then
            if let some (_, callee) := entries.find? (·.1 == target) then
              -- A call: the callee takes its arguments and the continuation, if it returns,
              -- and leaves its results.
              let returns := callee.blocks.any fun cb => cb.term matches .ret _
              let taken := callee.params.length + if returns then 1 else 0
              if d < taken then
                failures := failures.push s!"{f.name} block{b.block} calls {callee.name} short"
                break
              d := d - taken + callee.rets.length
            else if low.units.any (·.2.1 == target) then
              if op == .JUMP then break
            else
              match succs.find? (·.1 == target) with
              | some (_, s) =>
                if d < (height s).getD 0 then
                  failures := failures.push s!"{f.name} block{b.block} jumps to block{s} short"
              | none =>
                failures :=
                  failures.push s!"{f.name} block{b.block} jumps to {target}, no successor"
              if op == .JUMP then break
          else if op == .JUMP then break
        if [Operation.STOP, .RETURN, .REVERT, .SELFDESTRUCT].contains op then break
        pushed := if arg.isSome then arg else none
        pc := next
  return failures.toList

end Fe.Sonatina.Hints
