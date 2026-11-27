import Fe.Sonatina.H.Run
import Fe.Sonatina.H.Wf
import Fe.Sonatina.Diff

/-!
Runs the handover semantics H (`Fe/Sonatina/H/`) on every sidecar under the directory
`HDIFF_DIR`, with a line per section and per call:

- `WF <file> <section> accepted`, or `WF <file> <section> rejected <reason> <where>` for each
  reason `wfReasons` gives (`H/Wf.lean`);
- for generated calls (`Fe/EVM/Generate.lean`'s generators; the interface from the contract's
  ABI under `FeProofs/` if there is one, else the dispatcher's `br_table` keys as selectors with
  random argument words), each frame is run on the bytes, which give the feed; then on the
  machine IR's model (`Sidecar.model .machine`) and on H (`runRuntime`, `runDeploy`) under three
  oracles, from the same world and feed:
  - `mach`: blocks where the machine puts them, as far as the lowering record says
    (`arena_base`, each function's stable frame base word, `alloca`s in order within it, heap
    mallocs from the entry free pointer bumped by the heap requests, clamped by `min_base`, or
    at their exact or fixed base), fresh bytes nonzero; an address word H does not allow
    (`AddrOk`) is reported as a bad oracle, not replaced;
  - `far`: blocks far apart in reverse order of allocation, other nonzero bytes;
  - `zero`: blocks packed close, overlapping, zero bytes;
- `CALL <file> <section> <oracle> <verdict> <input>: M … | H …` for each oracle's outcome that
  is not `.ends` agreeing with the machine IR's (`ub` of cause `literal` or `OTHER`,
  `exhausted`, `stuck`, `diverge`, out of fuel, a bad oracle, a disagreement),
  `UB <file> <section> <oracle> <cause> <where>` for each `ub`, and
  `ORACLES <file> <section> <input>: …` when the oracles' outcomes differ;
- `SUM <file> …` per sidecar and `TOTAL …` at the end.

An H run and a machine run agree when they end as `EndsAs` says: the same exit, or the same
return data, accounts, logs and recorded calls, each call compared field by field (`madeEq`).
`diverge` counts H runs in which the model library's run does not terminate (too much init
code, an exhausted feed): divergence the model intends, apart from `stuck`.

A `ub`'s cause: `panic` (an access at a literal address in a block that ends
`evm_revert 0 36`, Fe's panic payload), `immutables` (in an init section, the hand-off of the
immutable fields through address 0: a store `mstore 0 v i256` of a value in a block that
returns, or a load `mload 0 i256`), `literal` (another literal-address access) or `OTHER`.

Run with `HDIFF_DIR=<dir> lake lean scripts/HDiff.lean`; `HDIFF_SEQ` and `HDIFF_CALLS` set the
sequences per contract and calls per sequence (4 and 16).
-/

open Lean Ethereum Ethereum.EVM Fe Fe.EVM Fe.EVM.Diff Fe.Sonatina
open Fe.Sonatina.H (Oracle AllocInfo RRes HSection HInst HTerm)

namespace HDiff

/-! ## Oracles -/

/-- Where the lowering record of a section says the machine puts blocks. -/
structure Placement where
  arenaBase : Nat := 0
  freePtr : Nat := 0
  frameBase : Std.HashMap String Nat := {}
  allocaOff : Std.HashMap (String × Nat) Nat := {}
  /-- Per function and value: `min_base`, and the exact or fixed base if any. -/
  mallocs : Std.HashMap (String × Nat) (Nat × Option Nat) := {}

def placementOf (json : Json) (name : String) (h : HSection) : Placement := Id.run do
  let secs := (json.getObjValAs? (Array Json) "sections").toOption.getD #[]
  let some s := secs.find? (·.getObjValAs? String "name" == .ok name) | return {}
  let some l := (s.getObjVal? "lowering").toOption | return {}
  let arena := (l.getObjValAs? Nat "arena_base").toOption.getD 0
  let efp := ((l.getObjValAs? (Option Nat) "entry_free_ptr").toOption.join).getD 0x60
  let mut p : Placement := { arenaBase := arena, freePtr := efp }
  for f in (l.getObjValAs? (Array Json) "funcs").toOption.getD #[] do
    let fname := (f.getObjValAs? String "name").toOption.getD ""
    match ((f.getObjVal? "frame").bind (·.getObjVal? "stable")).bind (·.getObjVal? "abs")
      |>.bind (·.getObjValAs? Nat "base_word") with
    | .ok w => p := { p with frameBase := p.frameBase.insert fname (arena + 32 * w) }
    | .error _ => pure ()
    for m in (f.getObjValAs? (Array Json) "mallocs").toOption.getD #[] do
      let v := (m.getObjValAs? Nat "value").toOption.getD 0
      let pl := (m.getObjVal? "placement").toOption.getD .null
      match pl.getObjVal? "heap", pl.getObjVal? "fixed" with
      | .ok hp, _ =>
        let minBase := (hp.getObjValAs? Nat "min_base").toOption.getD 0
        let exact := (hp.getObjValAs? (Option Nat) "exact_base").toOption.join
        p := { p with mallocs := p.mallocs.insert (fname, v) (minBase, exact) }
      | _, .ok fx =>
        let fixed := (0, (fx.getObjValAs? Nat "base").toOption)
        p := { p with mallocs := p.mallocs.insert (fname, v) fixed }
      | _, _ => pure ()
  -- `alloca`s in order within each function's frame.
  for f in h.module.funcs do
    let mut off := 0
    for b in f.blocks do
      for st in b.body do
        if let .base (.alloca ty) := st.inst then
          p := { p with allocaOff := p.allocaOff.insert (f.name, st.site) off }
          off := off + (H.sizeOf h.module.structs H.sizeFuel ty).getD 0
  return p

def machOracle (p : Placement) : Oracle where
  addr i := match i.kind with
    | .alloca => (p.frameBase.getD i.func p.arenaBase) + p.allocaOff.getD (i.func, i.site) 0
    | .malloc => match p.mallocs.get? (i.func, i.site) with
      | some (_, some base) => base
      | some (minBase, none) => max (p.freePtr + i.heapReq) minBase
      | none => p.freePtr + i.heapReq
  fresh i k := UInt8.ofNat (1 + (i.id * 37 + k * 11) % 255)

def farOracle : Oracle where
  addr i := 2 ^ 255 - (i.id + 1) * 2 ^ 180
  fresh i k := UInt8.ofNat (255 - (i.id + k) % 7)

def zeroOracle : Oracle where
  addr i := 0x60 + 32 * i.id
  fresh _ _ := 0

def oracles (p : Placement) : List (String × Oracle) :=
  [("mach", machOracle p), ("far", farOracle), ("zero", zeroOracle)]

/-! ## Comparing -/

def toExecuteEq : ToExecute → ToExecute → Bool
  | .Code a, .Code b => a == b
  | .Precompiled a, .Precompiled b => a == b
  | _, _ => false

def blocksEq (a b : ProcessedBlocks) : Bool :=
  a.size == b.size && (a.toList.zip b.toList).all fun (x, y) =>
    x.hash == y.hash && x.blockHeader == y.blockHeader && x.σ == y.σ

/-- Two recorded calls or creations are the same: every input passed to `Θ` or `Lambda`. -/
def madeEq : Made → Made → Bool
  | .theta T, .theta T' =>
    T.σ == T'.σ && T.σ₀ == T'.σ₀ && T.A == T'.A && T.s == T'.s && T.o == T'.o && T.r == T'.r &&
      toExecuteEq T.c T'.c && T.g == T'.g && T.p == T'.p && T.v == T'.v && T.v' == T'.v' &&
      T.d == T'.d && T.e == T'.e && T.H == T'.H && T.bvh == T'.bvh &&
      blocksEq T.blocks T'.blocks && T.w == T'.w
  | .lambda L, .lambda L' =>
    L.σ == L'.σ && L.σ₀ == L'.σ₀ && L.A == L'.A && L.s == L'.s && L.o == L'.o && L.g == L'.g &&
      L.p == L'.p && L.v == L'.v && L.i == L'.i && L.e == L'.e && L.ζ == L'.ζ && L.H == L'.H &&
      L.bvh == L'.bvh && blocksEq L.blocks L'.blocks && L.w == L'.w
  | _, _ => false

/-- The recorded calls are the same, in order (`EndsAs`'s `w'.calls = w.calls`). -/
def callsEq (a b : List Made) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => madeEq x y

def exitEq : Exit World → Exit World → Bool
  | .revert a, .revert b => a == b
  | .panic a, .panic b => a == b
  | .static, .static | .trap, .trap | .oob, .oob => true
  | .stop a w, .stop b w' => a == b && w.accounts == w'.accounts && w.logs == w'.logs &&
      callsEq w.calls w'.calls
  | _, _ => false

/-- `EndsAs (some a) (some b)`, decided. -/
def endsAs : Except (Exit World) (ByteArray × World) → Except (Exit World) (ByteArray × World) →
    Bool
  | .error (.stop o w), .ok (o', w') | .ok (o, w), .ok (o', w')
  | .ok (o, w), .error (.stop o' w') =>
    o == o' && w.accounts == w'.accounts && w.logs == w'.logs && callsEq w.calls w'.calls
  | .error (.panic c), .error (.revert d) => d == panicData c
  | .error e, .error e' => exitEq e e'
  | _, _ => false

def describeR : Except (Exit World) (ByteArray × World) → String
  | r => (observe (some r)).describe

def describeH : RRes (List H.Val × H.State) → String
  | .halt (.ends r) _ => describeR r
  | .halt .ub at_ => s!"ub at {at_}"
  | .halt .exhausted at_ => s!"exhausted at {at_}"
  | .stuck why => s!"stuck: {why}"
  | .diverge at_ => s!"the model library diverges at {at_}"
  | .fuel => "out of fuel"
  | .badOracle why => s!"bad oracle: {why}"
  | .ok _ => "returns from the section entry"

/-- A short key of an outcome, to compare oracles. -/
def keyH : RRes (List H.Val × H.State) → String
  | .halt (.ends r) _ => describeR r
  | .halt .ub _ => "ub"
  | .halt .exhausted _ => "exhausted"
  | .stuck _ => "stuck"
  | .diverge _ => "diverge"
  | .fuel => "fuel"
  | .badOracle _ => "badOracle"
  | .ok _ => "ok"

/-- The instruction or terminator a halt's `where` names. -/
def located (h : HSection) (at_ : String) : Option (H.HBlock × Option HInst) := do
  let head := (at_.splitOn ": ").headD ""
  match head.splitOn " " with
  | [fname, blk, pos] =>
    let f ← h.module.func? fname
    let b ← f.block? (← (blk.drop 5).toString.toNat?)
    if pos == "terminator" then return (b, none)
    let k ← (pos.drop 1).toString.toNat?
    return (b, (b.body[k]?.map (·.inst)))
  | _ => none

def literal : Operand → Bool
  | .imm _ _ => true
  | _ => false

/-- The cause of a `ub` at `at_` in section `sec`. -/
def ubCause (sec : String) (h : HSection) (at_ : String) : String :=
  match located h at_ with
  | some (b, i) =>
    let panicBlock := b.term matches .base (.evmRevert (.imm _ 0) (.imm _ 36))
    let lit := match i with
      | some (.base (.mstore a _ _)) | some (.base (.mload a _)) => literal a
      | some (.base (.evm _ (a :: _))) => literal a
      | some _ => false
      | none => match b.term with
        | .base (.evmRevert a l) | .base (.evmReturn a l) => literal a && l != .imm 256 0
        | _ => false
    let handoff := sec == "init" && (match i with
      | some (.base (.mstore (.imm _ 0) (.var _) (.int 256))) => (b.term matches .base (.ret []))
      | some (.base (.mload (.imm _ 0) (.int 256))) => true
      | _ => false)
    if lit && panicBlock then "panic"
    else if handoff then "immutables"
    else if lit then "literal"
    else "OTHER"
  | none => "OTHER"

/-! ## Calls -/

structure Tally where
  frames : Nat := 0
  outOfGas : Nat := 0
  /-- Frames every oracle's H run ends as the machine IR's does. -/
  agree : Nat := 0
  /-- Per oracle run: -/
  runs : Nat := 0
  ends : Nat := 0
  disagree : Nat := 0
  ub : Std.HashMap String Nat := {}
  exhausted : Nat := 0
  stuck : Nat := 0
  diverge : Nat := 0
  fuel : Nat := 0
  badOracle : Nat := 0
  oracleDisagree : Nat := 0
  machineDiverges : Nat := 0
  machineVsBytes : Nat := 0
  /-- Frames the machine IR's model ends successfully. -/
  success : Nat := 0

def Tally.add (a b : Tally) : Tally where
  frames := a.frames + b.frames
  outOfGas := a.outOfGas + b.outOfGas
  agree := a.agree + b.agree
  runs := a.runs + b.runs
  ends := a.ends + b.ends
  disagree := a.disagree + b.disagree
  ub := b.ub.fold (fun m k v => m.insert k (m.getD k 0 + v)) a.ub
  exhausted := a.exhausted + b.exhausted
  stuck := a.stuck + b.stuck
  diverge := a.diverge + b.diverge
  fuel := a.fuel + b.fuel
  badOracle := a.badOracle + b.badOracle
  oracleDisagree := a.oracleDisagree + b.oracleDisagree
  machineDiverges := a.machineDiverges + b.machineDiverges
  machineVsBytes := a.machineVsBytes + b.machineVsBytes
  success := a.success + b.success

def Tally.fields (t : Tally) : String :=
  let ubs := t.ub.toList.mergeSort (fun a b => a.1 ≤ b.1) |>.map fun (k, v) => s!"ub_{k}={v}"
  s!"frames={t.frames} outOfGas={t.outOfGas} agree={t.agree} runs={t.runs} ends={t.ends} \
    disagree={t.disagree} {" ".intercalate ubs} exhausted={t.exhausted} stuck={t.stuck} \
    diverge={t.diverge} fuel={t.fuel} badOracle={t.badOracle} oracleDisagree={t.oracleDisagree} \
    machineDiverges={t.machineDiverges} machineVsBytes={t.machineVsBytes} success={t.success}"

def hFuel : Nat := 20000000

/-- Compare one frame: the bytes ran from `σ`, `A`, `I`; the machine IR's model `model` and H
    (`hrun` under each oracle) run from the world the bytes' run feeds. -/
def frame (file sec input : String) (h : HSection) (os : List (String × Oracle))
    (σ : AccountMap) (A : Substate) (I : ExecutionEnv) (model : FeM ByteArray)
    (hrun : Oracle → ExecutionEnv → World → RRes (List H.Val × H.State)) :
    IO (Tally × Except ExecutionException (ExecutionResult State)) := do
  let r := run (fresh σ σ generatedGas A I) generatedSteps
  match r.result with
  | .error .OutOfGass | .error .OutOfFuel | .error .StackOverflow =>
    return ({ outOfGas := 1 }, r.result)
  | _ =>
    let w := World.init σ A (r.events.toList.map supply)
    let m := model.exec I w
    let mut t : Tally := { frames := 1 }
    if !(compare r.result m matches .agree _) then t := { t with machineVsBytes := 1 }
    let mdesc := (observe m).describe
    if m matches some (.ok _) || m matches some (.error (.stop ..)) then
      t := { t with success := 1 }
    let mut allAgree := true
    let mut keys : List String := []
    for (oname, O) in os do
      let hr := hrun O I w
      keys := keys ++ [keyH hr]
      t := { t with runs := t.runs + 1 }
      let say (verdict : String) : IO Unit :=
        IO.println s!"CALL {file} {sec} {oname} {verdict} {input}: M {mdesc} | H {describeH hr}"
      match hr, m with
      | .halt (.ends hres) _, some mres =>
        if endsAs hres mres then t := { t with ends := t.ends + 1 }
        else
          allAgree := false
          t := { t with disagree := t.disagree + 1 }
          say "DISAGREE"
      | .halt (.ends _) _, none =>
        allAgree := false
        t := { t with machineDiverges := t.machineDiverges + 1 }
        say "MACHINE-DIVERGES"
      | .halt .ub at_, _ =>
        allAgree := false
        let cause := ubCause sec h at_
        t := { t with ub := t.ub.insert cause (t.ub.getD cause 0 + 1) }
        IO.println s!"UB {file} {sec} {oname} {cause} {at_}"
        if cause == "OTHER" || cause == "literal" then say s!"UB-{cause.toUpper}"
      | .halt .exhausted _, _ =>
        allAgree := false
        t := { t with exhausted := t.exhausted + 1 }
        say "EXHAUSTED"
      | .stuck _, _ =>
        allAgree := false
        t := { t with stuck := t.stuck + 1 }
        say "STUCK"
      | .diverge _, _ =>
        allAgree := false
        t := { t with diverge := t.diverge + 1 }
        say "DIVERGE"
      | .fuel, _ =>
        allAgree := false
        t := { t with fuel := t.fuel + 1 }
        say "FUEL"
      | .badOracle _, _ =>
        allAgree := false
        t := { t with badOracle := t.badOracle + 1 }
        say "BADORACLE"
      | .ok _, _ =>
        allAgree := false
        t := { t with stuck := t.stuck + 1 }
        say "ENTRY-RETURNS"
    if allAgree then t := { t with agree := 1 }
    if keys.eraseDups.length > 1 then
      t := { t with oracleDisagree := 1 }
      IO.println s!"ORACLES {file} {sec} {input}: {keys}"
    return (t, r.result)

/-- One generated sequence (as `Fe.EVM.Diff.sequence`): deploy, then `calls` calls. -/
def sequenceH (file : String) (s : Sidecar) (hobj : H.Object) (json : Json) (interface : Interface)
    (index calls : Nat) : IO Tally := do
  let creation := (s.section? "init").map (·.bytecode) |>.getD .empty
  let model := s.model .machine
  let initOs := oracles (placementOf json "init" hobj.init)
  let runOs := oracles (placementOf json "runtime" hobj.runtime)
  let mut g := mkStdGen index
  let gen {α : Type} (m : Gen α) (g : StdGen) : α × StdGen := m.run g
  let actors := [0xa11ce, 0xb0b, 0xca401]
  let contract := 0xfe
  let mut known : Known := { addresses := [0, contract] ++ actors }
  let address : AccountAddress := Fin.ofNat _ contract
  let mut σ : AccountMap := actors.foldl
    (fun σ a => σ.insert (Fin.ofNat _ a) { (default : Account) with balance := .ofNat (10 ^ 24) }) ∅
  let A : Substate := (default : Substate).addAccessedAccount address
  let mut tally : Tally := {}
  let mut deployed := false
  for _ in [:4] do
    let (creator, g1) := gen (pick actors) g
    let (pays, g2) := gen (do if interface.initPayable then oneIn 2 else oneIn 16) g1
    let (amount, g3) := gen genAmount g2
    let (args, g4) := gen (do mutate known 0 (← genInputs known interface.init)) g3
    g := g4
    let value : UInt256 := .ofNat (if pays then amount else 0)
    let account := σ.getD (Fin.ofNat _ creator) default
    let σ₁ := σ.insert (Fin.ofNat _ creator)
        { account with balance := account.balance - value, nonce := account.nonce + ⟨1⟩ }
      |>.insert address { (default : Account) with nonce := ⟨1⟩, balance := value }
    let I : ExecutionEnv :=
      { env with
          codeOwner := address, sender := Fin.ofNat _ creator, source := Fin.ofNat _ creator,
          weiValue := value, code := creation ++ args, perm := true }
    let (t, result) ← frame file "init" s!"init {shortHex args}" hobj.init initOs σ₁
      { A with createdAccounts := A.createdAccounts.insert address } I
      (model.init args >>= fun tail => pure (ByteArray.empty ++ tail))
      (fun O I w => H.runDeploy hFuel O hobj I w)
    tally := tally.add t
    if let .ok (.success st code) := result then
      σ := st.accountMap.insert address { st.accountMap.getD address default with code := code }
      deployed := true
      break
  if deployed then
    for _ in [:calls] do
      known := { known with words := (σ.getD address default).storage.values.map (·.toNat) }
      let (sender, g1) := gen (pick actors) g
      let arms := interface.arms
      let (arm?, g2) := gen (do if ← oneIn 8 then pure none else pure arms[← below arms.length]?) g1
      let (input, g3) := gen (match arm? with
        | some arm => do
          mutate known 4 ((Diff.word arm.selector).extract 28 32 ++ (← genInputs known arm.inputs))
        | none => do genBytes (← pick [0, 1, 3, 4, 36, 68])) g2
      let (static, g4) := gen (oneIn 16) g3
      let (pays, g5) := gen (do if arm?.any (·.payable) then oneIn 2 else oneIn 16) g4
      let (amount, g6) := gen genAmount g5
      g := g6
      let value : UInt256 := .ofNat (if pays && !static then amount else 0)
      let senderA : AccountAddress := Fin.ofNat _ sender
      let payer := σ.getD senderA default
      let σ₁ := σ.insert senderA { payer with balance := payer.balance - value }
      let payee := σ₁.getD address default
      let σ₁ := σ₁.insert address { payee with balance := payee.balance + value }
      let I : ExecutionEnv :=
        { env with
            codeOwner := address, sender := senderA, source := senderA, weiValue := value,
            calldata := input, code := payee.code, perm := !static }
      let how := if static then "static " else ""
      let (t, result) ← frame file "runtime" s!"{how}{shortHex input} value {value.toNat}"
        hobj.runtime runOs σ₁ A I model.runtime (fun O I w => H.runRuntime hFuel O hobj I w)
      tally := tally.add t
      if let .ok (.success st _) := result then σ := st.accountMap
  return tally

/-- The selectors a section's dispatcher tests: the `br_table` keys below `2 ^ 32` of its
    functions. -/
def dispatchInterface (h : HSection) : Interface :=
  let keys := h.module.funcs.flatMap fun f => f.blocks.flatMap fun b => match b.term with
    | .base (.brTable _ _ cases) => cases.filterMap fun (o, _) => match o with
      | .imm _ v => if v < 2 ^ 32 then some v else none
      | _ => none
    | _ => []
  { arms := keys.eraseDups.map fun k => ⟨k, "", false⟩ }

partial def files (dir : System.FilePath) (suffix : String) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← files e.path suffix)
    else if e.fileName.endsWith suffix then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

def main : IO Unit := do
  let some dir ← IO.getEnv "HDIFF_DIR" | throw (IO.userError "HDIFF_DIR is not set")
  let seqs := ((← IO.getEnv "HDIFF_SEQ").bind String.toNat?).getD 4
  let calls := ((← IO.getEnv "HDIFF_CALLS").bind String.toNat?).getD 16
  let abis ← files "FeProofs" ".abi.json"
  let mut total : Tally := {}
  let mut wf : Std.HashMap String Nat := {}
  let mut sections := 0
  let mut accepted := 0
  for path in ← files dir ".sidecar.json" do
    let file := path.fileName.getD path.toString
    let text ← IO.FS.readFile path
    let json := (Json.parse text).toOption.getD .null
    match Parse.parseSidecar text, H.Parse.objectOfSidecar text with
    | .error e, _ => IO.println s!"UNREAD {file}: {e}"
    | _, .error e => IO.println s!"HUNREAD {file}: {e}"
    | .ok s, .ok hobj =>
      for (name, sec) in [("init", hobj.init), ("runtime", hobj.runtime)] do
        sections := sections + 1
        let rs := H.wfReasons sec
        if rs.isEmpty then
          accepted := accepted + 1
          IO.println s!"WF {file} {name} accepted"
        for (k, w) in rs do
          IO.println s!"WF {file} {name} rejected {k} {w}"
        for k in (rs.map (·.1)).eraseDups do wf := wf.insert k (wf.getD k 0 + 1)
      let dirName := (path.parent.bind (·.fileName)).getD ""
      let abi := abis.find? fun p => p.fileName == some s!"{s.object}.abi.json"
        || p.fileName == some s!"Fe{s.object}.abi.json" || p.fileName == some s!"{dirName}.abi.json"
      let interface ← match abi with
        | some p => match interfaceOfAbi (← IO.FS.readFile p) with
          | .ok i => pure i
          | .error _ => pure (dispatchInterface hobj.runtime)
        | none => pure (dispatchInterface hobj.runtime)
      let mut t : Tally := {}
      for index in [:seqs] do
        t := t.add (← sequenceH file s hobj json interface index calls)
      IO.println s!"SUM {file} abi={abi.isSome} {t.fields}"
      total := total.add t
  let reasons := wf.toList.mergeSort (fun a b => a.1 ≤ b.1) |>.map fun (k, v) => s!"{k}={v}"
  IO.println s!"WFTOTAL sections={sections} accepted={accepted} rejectedBy: {" ".intercalate reasons}"
  IO.println s!"TOTAL {total.fields}"

end HDiff

#eval HDiff.main
