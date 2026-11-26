import Fe.Sonatina.Spill
import Fe.Sonatina.CheckSound

/-!
# The spill plan of a sidecar, and `FrameSafe`

`Sidecar.spillPlan s name` is the spill plan of section `name`: for each function with memory
spills, each spilled value, its word from the lowering record, and its reload points, which a
walk of the bytes finds as the checker walks them (`Check.run`), against the instrumented
machine IR (`Func.instrument`).  It is untrusted: nothing is proved of it but that it is empty
for a sidecar without spills.  A reload is a bytes `MLOAD` of a constant word that is not the
IR's next event and that the path's own stores (or the block's spilled live-in values and
phis) hold; its point is the position of the IR's next event or call in the block, or the
terminator's if none is left.

`FrameSafe s` says the machine IR with its spills under that plan ends as the machine IR does,
on every call and deployment `Sound` speaks of.  It is a statement about the machine IR and the
plan alone.  As the machine IR never panics (`machine_not_panic`), it says that no statement
changes a word whose value the bytes reload later.  `frameSafe_of_noSpills`: a sidecar without
spills is frame-safe.
-/

namespace Fe.Sonatina

open Ethereum Ethereum.EVM Fe Fe.EVM Check

/-! ## The walk -/

/-- What the walk knows of a block: the checker's context, the block's hints and places, its
    id, and the number of its statements. -/
structure WalkBlock where
  c : Check.Ctx
  hints : List BlockHint
  place : Nat → Option Nat
  b : Nat
  len : Nat

/-- The position of the IR's next event or call in the block, or the terminator's. -/
def WalkBlock.gap (k : WalkBlock) (p : Path) : Nat :=
  match p.events, p.calls with
  | ev :: _, _ => ev.pos
  | [], cs :: _ => cs.pos
  | [], [] => k.len

/-- Walk the bytes of a block from `p` for at most `fuel` steps, as `Check.run` does, but on
    every path and to the end of what matches: each reload found, its value and point, added to
    `acc`.  `slots` holds the words the path knows, each with its expression and the spilled
    value it holds, if known. -/
def walkBlock (code : ByteArray) (tree : PcTree (Operation × Option Nat × Nat))
    (dests : List Nat) (k : WalkBlock) :
    Nat → Path → List (Nat × Expr × Option Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, acc => acc
  | fuel + 1, p, slots, acc =>
    if p.events.isEmpty && p.calls.isEmpty && (p.exit.selected.bind k.place) == some p.pc then acc
    else
    match opAt code tree p.pc with
    | none => acc
    | some (op, arg, next) =>
      let go (stack : List Expr) (events : List Event) (slots' := slots) (acc' := acc) :=
        walkBlock code tree dests k fuel { p with pc := next, stack, events } slots' acc'
      if op == .JUMPDEST then go p.stack p.events
      else if let some v := arg then go (.const v :: p.stack) p.events
      else if op == .PUSH0 then go (.const 0 :: p.stack) p.events
      else if op == .POP then
        match p.stack with
        | _ :: rest => go rest p.events
        | [] => acc
      else if let some n := dupN op then
        match p.stack[n - 1]? with
        | some e => go (e :: p.stack) p.events
        | none => acc
      else if let some n := swapN op then
        match p.stack[0]?, p.stack[n]? with
        | some a, some e => go ((p.stack.set 0 e).set n a) p.events
        | _, _ => acc
      else if pureOps.contains op then
        match δ op with
        | some n =>
          match mkOp op (p.stack.take n) with
          | some e =>
            if p.stack.length < n then acc else go (k.c.canon.intern e :: p.stack.drop n) p.events
          | none => acc
        | none => acc
      else if op == .MLOAD && (match p.stack with
          | .const w :: _ =>
            !(p.events.head?.any fun ev => ev.op == .MLOAD && ev.args == [.const w]) &&
              (slots.find? (·.1 == w)).isSome
          | _ => false) then
        -- A reload: the word's expression, and the value it holds at this point.
        match p.stack, p.stack.head?.bind fun e => match e with
            | .const w => slots.find? (·.1 == w)
            | _ => none with
        | _ :: rest, some (_, e, v) =>
          go (e :: rest) p.events slots (match v with
            | some v => (v, k.gap p) :: acc
            | none => acc)
        | _, _ => acc
      else if readOps.contains op || writeOps.contains op then
        match δ op, p.events with
        | some n, ev :: events =>
          if ev.op == op && p.stack.length ≥ n && p.stack.take n == ev.args then
            match ev.result, readOps.contains op with
            | some id, true => go (.atom id :: p.stack.drop n) events
            | none, false => go (p.stack.drop n) events (match op, ev.args with
              | .MSTORE, [.const w, e] => (w, e, ev.stores) :: slots
              | _, _ => slots)
            | _, _ => acc
          else acc
        | _, _ => acc
      else if haltOps.contains op then acc
      else if op == .JUMP then
        match p.stack with
        | .const t :: rest =>
          if !validJump code dests t then acc else
          match p.events, p.calls with
          | [], cs :: more =>
            match k.c.frame.callee cs.callee with
            | some ce =>
              if ce.offset == t && ce.returns && cs.args.length ≤ rest.length then
                match rest.drop cs.args.length with
                | .const r :: rest' =>
                  walkBlock code tree dests k fuel
                    ⟨r, cs.dsts.map .atom ++ rest', cs.events, p.exit, more, []⟩ slots acc
                | _ => acc
              else acc
            | none => acc
          | _, _ =>
            if p.events.isEmpty && p.calls.isEmpty && (p.exit.selected.bind k.place) == some t
            then acc
            else if k.hints.any (k.place ·.block == some t) then acc
            else walkBlock code tree dests k fuel { p with pc := t, stack := rest } slots acc
        | _ => acc
      else if op == .JUMPI then
        match p.stack with
        | .const _ :: cond :: rest =>
          match p.exit.way cond false with
          | some (.succ s) =>
            walkBlock code tree dests k fuel { p with pc := next, stack := rest, exit := .goto s }
              slots acc
          | some (.exit e) =>
            walkBlock code tree dests k fuel { p with pc := next, stack := rest, exit := e }
              slots acc
          | _ => acc
        | _ => acc
      else acc

/-- Values a block reads before it defines them, and those it defines, its phis among them. -/
def blockUses (b : Block) : List Nat × List Nat :=
  let (u, d) := b.body.foldl (init := (([] : List Nat), b.phis.map (·.dst))) fun (u, d) s =>
    (u ++ (s.inst.operands.filterMap Operand.var?).filter (!d.contains ·), d ++ s.dsts.map (·.1))
  (u ++ (b.term.operands.filterMap Operand.var?).filter (!d.contains ·), d)

/-- The values live at the entry of each block of the machine IR, by rounds. -/
def irLiveIn (f : Func) : List (Nat × List Nat) :=
  let step := fun (L : List (Nat × List Nat)) => f.blocks.map fun b =>
    let (uses, defs) := blockUses b
    let out := b.term.succs.flatMap fun s => match f.block? s with
      | some sb => ((L.lookup s).getD []).filter (fun v => !(sb.phis.any (·.dst == v))) ++
          sb.phis.filterMap fun phi => (phi.incoming.find? (·.2 == b.id)).bind (·.1.var?)
      | none => []
    (b.id, normSet (uses ++ out.filter (!defs.contains ·)))
  go step (f.blocks.length + 1) (f.blocks.map (·.id, []))
where
  go (step : List (Nat × List Nat) → List (Nat × List Nat)) :
      Nat → List (Nat × List Nat) → List (Nat × List Nat)
    | 0, L => L
    | n + 1, L => let L' := step L; if L' == L then L else go step n L'

/-- The reloads the bytes make in function `hint` of the section, found by walking each block
    of its instrumented machine IR: each value and point. -/
def walkFunc (code : CodeSection) (low : Lowering) (entry : String) (hint : FuncHint)
    (words : List (Nat × Nat)) : List (Nat × Nat × Nat) := Id.run do
  let some f := low.machine.func? hint.name | return []
  let fi := f.instrument words
  let fr := frameOf low entry fi
  let place := placeIn low hint.name
  let live := irLiveIn fi
  let tree := codeTree code.bytecode
  let dests := jumpdests code.bytecode
  let isRoot := hint.name == entry
  let entryId := (fi.blocks.head?.map (·.id)).getD 0
  fi.blocks.flatMap fun b =>
    let c := Ctx.ofBlock fi b code.symbols fr ⟨words, [], fun _ => [], entryId⟩
    match hint.blocks.find? (·.block == b.id), place b.id with
    | some h, some pc =>
      match c.entryStack h, c.segments [] 0 b.body, c.exitOf b.term with
      | some stack, some (events, calls), some exit =>
        let events := match low.entryFreePtr, isRoot && b.id == entryId with
          | some ptr, true =>
            { op := .MSTORE, args := [.const 0x40, .const ptr], result := none } :: events
          | _, _ => events
        let wb : WalkBlock := ⟨c, hint.blocks, place, b.id, b.body.length⟩
        let liveIn := ((live.lookup b.id).getD []).filter (words.lookup · |>.isSome)
        let slots := (liveIn ++ b.phis.map (·.dst)).filterMap fun v =>
          (words.lookup v).bind fun w => (c.expand v).map fun e => (w, e, some v)
        (walkBlock code.bytecode tree dests wb (2 * low.codeSize + 2)
          ⟨pc, stack, events, exit, calls, []⟩ slots []).map fun (v, k) => (v, b.id, k)
      | _, _, _ => []
    | _, _ => []

/-- The spill plan of a section, found by walking its bytes against its entry `entry`: for each
    function with memory spills, each spilled value, its word, and the points it is reloaded
    at. -/
def CodeSection.spillPlan (code : CodeSection) (entry : String) : SpillPlan :=
  match code.lowering with
  | none => []
  | some low => low.funcs.filterMap fun hint =>
    if hint.spillWords.isEmpty then none else
      let reloads := walkFunc code low entry hint hint.spillWords
      some (hint.name, hint.spillWords.map fun (v, w) =>
        ⟨v, w, normPoints (reloads.filterMap fun (v', b, k) =>
          if v' == v then some (b, k) else none)⟩)
where
  normPoints (ps : List (Nat × Nat)) : List (Nat × Nat) := ps.eraseDups

/-- The spill plan of section `name` of the sidecar (`CodeSection.spillPlan`), empty if the
    sidecar's object has no such section. -/
def Sidecar.spillPlan (s : Sidecar) (name : String) : SpillPlan :=
  match s.section? name, (entries s).lookup name with
  | some code, some entry => code.spillPlan entry
  | _, _ => []

/-! ## `FrameSafe` -/

/-- The memory spills of the sidecar change nothing the contract shows: on every message call
    `CalldataFits` admits and every deployment, the machine IR with its spills, under the
    sidecar's spill plan, ends as the machine IR does.  As the machine IR never panics, this
    also says no statement changes a word whose value the bytes reload later. -/
def FrameSafe (s : Sidecar) : Prop :=
  Implements (s.model .machine) (s.spilledModel s.spillPlan) CalldataFits ∧
    ImplementsDeploy (s.model .machine) (s.spilledModel s.spillPlan) (s.code "init") .empty
      .empty (fun _ => True)

/-- A run ends as itself. -/
theorem _root_.Fe.EVM.EndsAs.refl : ∀ r : Option (Except (Exit World) (ByteArray × World)),
    EndsAs r r
  | none => .diverge
  | some (.error f) => .exit f
  | some (.ok _) => .ok_ok rfl rfl rfl

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by cases h
  | (x, y) :: l, h => by
    by_cases hx : a = x
    · subst hx
      simp only [List.lookup, BEq.rfl, Option.some.injEq] at h
      subst h; exact List.mem_cons_self
    · have : (a == x) = false := by simpa using hx
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The plan of a section without memory spills is empty. -/
theorem spillPlan_eq_nil {s : Sidecar} (h : s.noSpills = true) (name : String) :
    s.spillPlan name = [] := by
  unfold Sidecar.spillPlan
  split
  · next code entry hcode hentry =>
    unfold CodeSection.spillPlan
    split
    · rfl
    · next low hlow =>
      have hn := List.all_eq_true.mp h (name, entry) (mem_of_lookup hentry)
      simp only [hcode, hlow, Option.bind_some, Option.all_some, List.all_eq_true,
        List.isEmpty_iff] at hn
      apply List.filterMap_eq_nil_iff.mpr
      intro hint hmem
      simp [FuncHint.spillWords, hn hint hmem]
  · rfl

/-- A sidecar without memory spills is frame-safe: its instrumented model is its machine
    IR's. -/
theorem frameSafe_of_noSpills {s : Sidecar} (h : s.noSpills = true) : FrameSafe s := by
  have hm : s.spilledModel s.spillPlan = s.model .machine := by
    rw [show s.spillPlan = fun _ => [] from funext (spillPlan_eq_nil h), spilledModel_nil]
  rw [FrameSafe, hm]
  exact ⟨fun I σ A feed _ _ => ⟨feed, EndsAs.refl _⟩,
    fun I σ A feed args _ _ _ _ => ⟨feed, EndsAs.refl _⟩⟩

/-! ## Fixed-slot spills (a convenience check)

Sonatina may spill to the scratch words at `0x00` and `0x20`, which the IR uses too.  A spill
store over IR data that the IR reads later makes the bytes read the spilled value where the
machine IR reads its data: a miscompile, which `FrameSafe` excludes, since the two models then
end differently wherever that read shows.  `fixedSlotsSafe` rejects such a section outright, as
cheaply as it can be seen: from a spill store at `0x00` or `0x20`, no read of the IR at a
constant address may meet a byte of that word before the IR writes the byte, along the
function's blocks.  Soundness does not rest on it: `checkSpills_sound` needs `FrameSafe`, which
is false for such a section. -/

/-- The bytes `[a, a + len)` meets of the word at `w`, as a mask of its 32 bytes. -/
def wordMask (w a len : Nat) : Nat :=
  (List.range 32).foldl (fun m i => if a ≤ w + i && w + i < a + len then m ||| (1 <<< i) else m)
    0

/-- The constant-address reads and writes of an instruction, each as an address and a length. -/
def Inst.constAccesses : Inst → List (Nat × Nat) × List (Nat × Nat)
  | .mload (.imm _ a) _ => ([(a, 32)], [])
  | .mstore (.imm _ a) _ _ => ([], [(a, 32)])
  | .evm op args =>
    match op, args with
    | .mload, [.imm _ a] => ([(a, 32)], [])
    | .mstore, [.imm _ a, _] => ([], [(a, 32)])
    | .mstore8, [.imm _ a, _] => ([], [(a, 1)])
    | .keccak256, [.imm _ p, .imm _ l] => ([(p, l)], [])
    | .log _, .imm _ p :: .imm _ l :: _ => ([(p, l)], [])
    | .calldataCopy, [.imm _ d, _, .imm _ l] | .codeCopy, [.imm _ d, _, .imm _ l]
    | .returnDataCopy, [.imm _ d, _, .imm _ l] | .extCodeCopy, [_, .imm _ d, _, .imm _ l] =>
      ([], [(d, l)])
    | .mcopy, [.imm _ d, .imm _ s, .imm _ l] => ([(s, l)], [(d, l)])
    | .mcopy, [_, .imm _ s, .imm _ l] => ([(s, l)], [])
    | .create, [_, .imm _ p, .imm _ l] | .create2, [_, .imm _ p, .imm _ l, _] => ([(p, l)], [])
    | .call, [_, _, _, ap, al, rp, rl] | .callCode, [_, _, _, ap, al, rp, rl]
    | .staticCall, [_, _, ap, al, rp, rl]
    | .delegateCall, [_, _, ap, al, rp, rl] =>
      ((match ap, al with | .imm _ a, .imm _ l => [(a, l)] | _, _ => []),
        (match rp, rl with | .imm _ a, .imm _ l => [(a, l)] | _, _ => []))
    | _, _ => ([], [])
  | _ => ([], [])

/-- The constant-address reads of a terminator. -/
def Term.constReads : Term → List (Nat × Nat)
  | .evmReturn (.imm _ a) (.imm _ l) | .evmRevert (.imm _ a) (.imm _ l) => [(a, l)]
  | _ => []

/-- From statement `k` of block `b` of `f`, the bytes `mask` of the word at `w` still holding a
    spilled value: does no constant-address read of the IR meet one before the IR writes it?
    Each block is entered at most `fuel` times with bytes it was not entered with. -/
def fixedSlotFrom (f : Func) (words : List (Nat × Nat)) (w : Nat) :
    Nat → List (Nat × Nat × Nat) → List (Nat × Nat) → Bool
  | 0, _, _ => true
  | _, [], _ => true
  | fuel + 1, (b, k, mask) :: work, seen =>
    match f.block? b with
    | none => fixedSlotFrom f words w fuel work seen
    | some blk =>
      -- Run the block's statements from `k`.
      let step := (blk.body.drop k).foldl (fun (acc : Option Nat) s => acc.bind fun m =>
        if (storedValue f words blk s).isSome then some m else
        let (rs, ws) := s.inst.constAccesses
        if rs.any (fun (a, l) => m &&& wordMask w a l != 0) then none
        else some (ws.foldl (fun m (a, l) => m - (m &&& wordMask w a l)) m)) (some mask)
      match step with
      | none => false
      | some m =>
        if m == 0 then fixedSlotFrom f words w fuel work seen
        else if blk.term.constReads.any (fun (a, l) => m &&& wordMask w a l != 0) then false
        else
          let new := blk.term.succs.filter fun S =>
            ((seen.lookup S).getD 0) &&& m != m
          let seen := new.foldl (fun sn S => (S, ((sn.lookup S).getD 0) ||| m) :: sn) seen
          fixedSlotFrom f words w fuel (work ++ new.map (·, 0, m)) seen

/-- No spill store at `0x00` or `0x20` in a function of the plan is followed by a
    constant-address read of the IR of a byte of that word before the IR writes the byte. -/
def fixedSlotsSafe (s : Sidecar) (plan : String → SpillPlan) : Bool :=
  (entries s).all fun (name, _) =>
    ((s.section? name).bind (·.lowering)).all fun low =>
      (plan name).all fun (fname, p) =>
        match low.machine.func? fname with
        | none => true
        | some f =>
          let f := f.instrument p.words
          f.blocks.all fun b => b.body.zipIdx.all fun (s, k) =>
            match storedValue f p.words b s with
            | some (w, _) => !(w == 0 || w == 32) ||
                fixedSlotFrom f p.words w (33 * f.blocks.length + 1) [(b.id, k + 1, 2 ^ 32 - 1)] []
            | none => true

/-! ## The checkers -/

/-- The spill-aware checker: each section of the sidecar checked against its machine IR with
    the stores of its spill plan (`Sidecar.spillPlan`), under the guard the instrumented model
    runs it under, and no fixed-slot spill over IR data (`fixedSlotsSafe`, a convenience).
    `checkSpills_sound` (`CheckCert.lean`) needs `FrameSafe s` besides. -/
def Check.checkSpills (s : Sidecar) : Bool :=
  Check.checkWith s.spillPlan s && fixedSlotsSafe s s.spillPlan

/-- The checker of sidecars without memory spills, whose spill plans are empty; it reads no
    plan, so the kernel never runs the walk. -/
def Check.check (s : Sidecar) : Bool := Check.checkWith (fun _ => []) s && s.noSpills

/-- `check` is `checkSpills` of a sidecar without memory spills. -/
theorem Check.check_eq (s : Sidecar) : Check.check s = (Check.checkSpills s && s.noSpills) := by
  unfold Check.check Check.checkSpills
  cases hn : s.noSpills
  · simp
  · rw [show s.spillPlan = fun _ => [] from funext (spillPlan_eq_nil hn)]
    simp [fixedSlotsSafe]

end Fe.Sonatina
