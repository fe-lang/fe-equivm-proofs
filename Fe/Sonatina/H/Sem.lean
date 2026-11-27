import Fe.Sonatina.H.Inst
import Fe.EVM.Refine

/-!
# The relational semantics of H (design §3.1, §3.3, §7.2)

H is an inductive big-step relation (§3.1).  `ExecBody`, `ExecBlocks` and `ExecFunc` are the
runs of a function's statements, of its blocks from one block, and of a whole function, under
the section's program; their outcomes are a continuation (`BOut.cont`), a return
(`FOut.ret`), or a halt with an `Outcome`.  Every instruction but `alloca`, `evm_malloc` and
`call` steps by the function `stepInst` (`H/Inst.lean`); `call` runs the callee's `ExecFunc`
(the least fixpoint of §3.1's `ExecFuncO`, so calls need no oracle); the allocations are the
rules that choose:

- `alloca T`: a block of `sizeOf T` bytes, any address word `addr` with `AddrOk addr size`
  (§3.3, decision 2), any fresh bytes (R2).  Not counted in the budget (§3.3).
- `evm_malloc n`: if `heapReq + align32 n < 2 ^ 255`, a block of `n` bytes chosen the same way,
  and `heapReq` grows by `align32 n`; otherwise the run ends `exhausted` (§3.3, decision 3).

A run that reaches what H does not define (`IRes.stuck`, `TRes.stuck`, an operand of the wrong
type at a binding, a missing block or function, a section entry that returns) has no
derivation, so a gap in H makes a check fail, never pass (§3.7).  A run that does not end has
none either (§3.1: partial correctness needs only terminating runs), nor one in which the model
library's run does not terminate (`IRes.diverge`, `TRes.diverge`).

`Object.Runtime` and `Object.Deploy` are §7.2's: some run of the section's entry, from the
world `w` (whose feed it consumes) and empty memory, ends in `out`.  `Matches` and
`ImplementsH` are §7.2's statements, as written there; `ImplementsDeployH` takes the runtime
bytes the model's result is put after and the arguments it is stated for, as
`ImplementsDeployPSame` and `RefinesDeployFut` do (`Fe/Sonatina/RealFeed.lean`; review 24, M4),
so that it composes with `RefinesDeployFut` for any of them (`H/Compose.lean`).

## Interpretations of §3 (each a question for the design; the reading taken is named here)

- **I1** Fresh block ids: a new block's id is `blocks.size`, not an arbitrary unused id.  Ids
  are not observable (an `Outcome` holds none), so this is the same set of outcomes.
- **I2** Fresh bytes are plain bytes, never pointer fragments (R2: arbitrary concrete bytes).
- **I3** An instruction decides its failures other than memory first, in the order the model
  library and the EVM decide them, and resolves its memory ranges (`State.range`, `ub` out of a
  block) after (review 24, M2; checked against `Fe/Sonatina/Interp.lean`, `Fe/EVM/World.lean`
  and `Fe/EVM/Calls.lean`, where memory never fails).  Per instruction:
  - `evm_log`: a static call exits `static` (the one failure of `logData`, whose read of
    memory cannot fail), then the data range.
  - `evm_return_data_copy dst off len`: `off + len` past the return data exits `oob`
    (`returndatacopy` decides it before it writes), then the destination range.
  - `evm_create`, `evm_create2`: a static call exits `static`, then more than 49152 bytes of
    init code diverges (`createWith` decides both before it reads memory), then the init code
    range, then the feed (`createCore`).
  - `evm_call`: a static call moving value exits `static` (`call` decides it before
    `message`), then the input range, then the output range, then the feed (`messageCore`).
  - `evm_static_call`, `evm_delegate_call`, `evm_call_code`: the input range, then the output
    range, then the feed.  The model's `message` takes the feed first, but an exhausted feed is
    the model's divergence, which no real feed reaches, so the order is not observable.
  - `evm_mcopy`: the destination range, then the source range.  The machine IR's `mcopyIR`
    diverges where a range ends past `2 ^ 256`, which a range in a block never does.
  - `evm_mload_bytes a len`: `len > 32` is `ub` (U5a), then `len = 0` gives 0, then the range.
  - Every other instruction or terminal that touches memory (`mload`, `mstore`, `evm_mload`,
    `evm_mstore`, `evm_mstore8`, `memzero`, `evm_keccak256`, the copies from calldata, code and
    external code, `evm_return`, `evm_revert`) fails in no other way: its ranges only.
- **I4** `evm_mstore p v` writes `v`'s cells, fragments for a pointer, as `mstore p v i256`
  does; `evm_mload` is a typed load at `i256` (§3.4 names `evm_mload`, not `evm_mstore`).
- **I5** `bitcast` of a pointer to a pointer type or to `i256` keeps its origin, as `ptr_to_int`
  to `i256` does: Sonatina's verifier admits `bitcast *T i256` (both one word) and
  `lower_bitcast` lowers it to the value itself, and S5 treats it as non-observing (review 24,
  H1; design §3.2 corrected to say so).  `bitcast` of a pointer to a narrow integer gives the
  integer of its word; `bitcast` between integer types truncates or zero-extends the unsigned
  value, as Sonatina's interpreter and machine lowering do (§3.2 is silent).  The corpus has
  `bitcast i1 → i256`, `i256 → i1` and `*T → *U` only.
- **I6** `gep` indices are read as unsigned words, as machine lowering reads a dynamic index;
  Sonatina's interpreter sign-extends a narrow one.  A struct index past the fields is stuck.
- **I7** `black_box v` is `v`, origin included (§3.2's table does not list it).
- **I8** Generic `udiv`/`sdiv`/`umod`/`smod` are stuck, not `ub` and not zero: §3.6 puts them
  outside the subset on EVM, and `wfH` rejects them.
- **I9** `select` is defined as §3.6 says (an operand, unchanged), with both arms evaluated, so
  an arm with no value is stuck whichever is taken (review 24, L1); `wfH` rejects it until
  #625.
- **I10** A value bound to a declaration of another type (`Val.fits`) is stuck: H is typed;
  the machine IR's interpreter coerces (`Val.as`).
- **I11** The deploy outcome ignores the argument bytes, as the machine IR's model does
  (`Sidecar.model`): the init code reads them from `I.code`.
-/

namespace Fe.Sonatina.H

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/-- The context of a section's instructions. -/
def HSection.ctx (s : HSection) : Ctx := ⟨(s.symbols.lookup ·), s.module.structs⟩

/-- Bind each value to its id, if each is of the id's declared type (I10). -/
def bindVals (env : HEnv) (dsts : List (Nat × Ty)) (vals : List Val) : Option HEnv :=
  if dsts.length == vals.length && (dsts.zip vals).all (fun (d, v) => v.fits d.2) then
    some ((dsts.zip vals).foldl (fun env (d, v) => env.insert d.1 v) env)
  else none

/-- Enter block `b` from block `prev`: each phi takes, at once, its operand for `prev`. -/
def enter (env : HEnv) (prev : Option Nat) (b : HBlock) : Option HEnv := do
  let vals ← b.phis.mapM fun phi => do
    let p ← prev
    let (o, _) ← phi.incoming.find? (·.2 == p)
    evalOp env o
  bindVals env (b.phis.map fun phi => (phi.dst, phi.ty)) vals

/-- How a run of statements ends: it goes on, in an environment and a state, or halts. -/
inductive BOut where
  | cont (env : HEnv) (st : State)
  | halt (o : Outcome)

/-- How a run of a function ends: it returns values in a state, or halts. -/
inductive FOut where
  | ret (vals : List Val) (st : State)
  | halt (o : Outcome)

mutual

/-- A run of statements of section `P`'s functions in the environment `I`. -/
inductive ExecBody (P : HSection) (I : ExecutionEnv) :
    HEnv → List HStmt → State → BOut → Prop
  | nil {env : HEnv} {st : State} : ExecBody P I env [] st (.cont env st)
  | step {env env' : HEnv} {s : HStmt} {rest : List HStmt} {st st' : State} {vals : List Val}
      {o : BOut}
      (hi : stepInst P.ctx I env st s.inst = .ok vals st')
      (hb : bindVals env s.dsts vals = some env')
      (hr : ExecBody P I env' rest st' o) :
      ExecBody P I env (s :: rest) st o
  | exit {env : HEnv} {s : HStmt} {rest : List HStmt} {st : State} {e : Exit World}
      (hi : stepInst P.ctx I env st s.inst = .exit e) :
      ExecBody P I env (s :: rest) st (.halt (.ends (.error e)))
  | ub {env : HEnv} {s : HStmt} {rest : List HStmt} {st : State}
      (hi : stepInst P.ctx I env st s.inst = .ub) :
      ExecBody P I env (s :: rest) st (.halt .ub)
  /-- `alloca T`: a block of `T`'s size at any address word that does not wrap, holding any
      bytes (§3.3). -/
  | alloca {env env' : HEnv} {s : HStmt} {rest : List HStmt} {st : State} {ty : Ty}
      {n addr : Nat} {fresh : List UInt8} {o : BOut}
      (hs : s.inst = .base (.alloca ty))
      (hn : sizeOf P.module.structs sizeFuel ty = some n)
      (ha : AddrOk addr n) (hf : fresh.length = n)
      (hb : bindVals env s.dsts [.ptr st.blocks.size 0] = some env')
      (hr : ExecBody P I env' rest (st.alloc .alloca n addr fresh) o) :
      ExecBody P I env (s :: rest) st o
  /-- `evm_malloc n` within the budget: a block of `n` bytes, chosen as for `alloca`, and the
      request counted (§3.3). -/
  | malloc {env env' : HEnv} {s : HStmt} {rest : List HStmt} {st : State} {a : Operand}
      {v : Val} {addr : Nat} {fresh : List UInt8} {o : BOut}
      (hs : s.inst = .base (.malloc a)) (hv : evalOp env a = some v)
      (hbud : st.heapReq + align32 (st.word v) < heapBudget)
      (ha : AddrOk addr (st.word v)) (hf : fresh.length = st.word v)
      (hb : bindVals env s.dsts [.ptr st.blocks.size 0] = some env')
      (hr : ExecBody P I env' rest
        { st.alloc .malloc (st.word v) addr fresh with
          heapReq := st.heapReq + align32 (st.word v) } o) :
      ExecBody P I env (s :: rest) st o
  /-- `evm_malloc n` past the budget ends the run (§3.3, decision 3). -/
  | exhausted {env : HEnv} {s : HStmt} {rest : List HStmt} {st : State} {a : Operand} {v : Val}
      (hs : s.inst = .base (.malloc a)) (hv : evalOp env a = some v)
      (hbud : heapBudget ≤ st.heapReq + align32 (st.word v)) :
      ExecBody P I env (s :: rest) st (.halt .exhausted)
  | call {env env' : HEnv} {s : HStmt} {rest : List HStmt} {st st' : State} {callee : String}
      {args : List Operand} {vs vals : List Val} {o : BOut}
      (hs : s.inst = .base (.call callee args)) (ha : args.mapM (evalOp env) = some vs)
      (hc : ExecFunc P I callee vs st (.ret vals st'))
      (hb : bindVals env s.dsts vals = some env')
      (hr : ExecBody P I env' rest st' o) :
      ExecBody P I env (s :: rest) st o
  | callHalt {env : HEnv} {s : HStmt} {rest : List HStmt} {st : State} {callee : String}
      {args : List Operand} {vs : List Val} {o : Outcome}
      (hs : s.inst = .base (.call callee args)) (ha : args.mapM (evalOp env) = some vs)
      (hc : ExecFunc P I callee vs st (.halt o)) :
      ExecBody P I env (s :: rest) st (.halt o)

/-- A run of function `f` from block `id`, entered from `prev`. -/
inductive ExecBlocks (P : HSection) (I : ExecutionEnv) :
    HFunc → HEnv → Option Nat → Nat → State → FOut → Prop
  | goto {f : HFunc} {env env₁ env₂ : HEnv} {prev : Option Nat} {id dest : Nat} {st st₂ : State}
      {b : HBlock} {o : FOut}
      (hb : f.block? id = some b) (he : enter env prev b = some env₁)
      (hbody : ExecBody P I env₁ b.body st (.cont env₂ st₂))
      (ht : stepTerm I env₂ st₂ b.term = .goto dest)
      (hr : ExecBlocks P I f env₂ (some id) dest st₂ o) :
      ExecBlocks P I f env prev id st o
  | ret {f : HFunc} {env env₁ env₂ : HEnv} {prev : Option Nat} {id : Nat} {st st₂ : State}
      {b : HBlock} {vals : List Val}
      (hb : f.block? id = some b) (he : enter env prev b = some env₁)
      (hbody : ExecBody P I env₁ b.body st (.cont env₂ st₂))
      (ht : stepTerm I env₂ st₂ b.term = .ret vals) :
      ExecBlocks P I f env prev id st (.ret vals st₂)
  | halt {f : HFunc} {env env₁ env₂ : HEnv} {prev : Option Nat} {id : Nat} {st st₂ : State}
      {b : HBlock} {o : Outcome}
      (hb : f.block? id = some b) (he : enter env prev b = some env₁)
      (hbody : ExecBody P I env₁ b.body st (.cont env₂ st₂))
      (ht : stepTerm I env₂ st₂ b.term = .halt o) :
      ExecBlocks P I f env prev id st (.halt o)
  | bodyHalt {f : HFunc} {env env₁ : HEnv} {prev : Option Nat} {id : Nat} {st : State}
      {b : HBlock} {o : Outcome}
      (hb : f.block? id = some b) (he : enter env prev b = some env₁)
      (hbody : ExecBody P I env₁ b.body st (.halt o)) :
      ExecBlocks P I f env prev id st (.halt o)

/-- A run of function `name` of section `P` on `args`. -/
inductive ExecFunc (P : HSection) (I : ExecutionEnv) : String → List Val → State → FOut → Prop
  | mk {name : String} {args : List Val} {st : State} {f : HFunc} {e : HBlock} {env : HEnv}
      {o : FOut}
      (hf : P.module.func? name = some f) (he : f.blocks.head? = some e)
      (hp : bindVals {} f.params args = some env)
      (hr : ExecBlocks P I f env none e.id st o) :
      ExecFunc P I name args st o

end

/-- Some run of the runtime section from world `w` (whose feed it consumes) ends in `out`
    (§7.2).  The section's entry ends the call itself: one that returns has no derivation. -/
def Object.Runtime (h : Object) (I : ExecutionEnv) (w : World) (out : Outcome) : Prop :=
  ExecFunc h.runtime I h.runtime.entry [] (State.init w) (.halt out)

/-- Some run of the constructor on argument bytes `args` ends in `out` (§7.2); on
    `.ends (.error (.stop code w))` `code` is the whole deployed code.  The init section reads
    its arguments from the running code, `I.code`, as the machine IR's model does (I11). -/
def Object.Deploy (h : Object) (_args : ByteArray) (I : ExecutionEnv) (w : World)
    (out : Outcome) : Prop :=
  ExecFunc h.init I h.init.entry [] (State.init w) (.halt out)

/-- The handover outcome `out` excuses, or ends as, the machine result `r` (§7.2). -/
def Matches (out : Outcome) (r : Except (Exit World) (ByteArray × World)) : Prop :=
  out = .ub ∨ out = .exhausted ∨ ∃ r', out = .ends r' ∧ EndsAs (some r') (some r)

/-- Partial correctness against H, under one feed (§7.2): every run of `ir` that ends, under a
    feed, is matched by some run of `h` on the same call and the same feed.  A machine run that
    does not end is admitted by the hypothesis `= some r`, as `EndsAsP` admits `none`. -/
def ImplementsH (h : Object) (ir : ContractModel) (admits : ExecutionEnv → Prop) : Prop :=
  ∀ I σ A feed r, OwnerExists σ I → admits I →
    ir.runtime.exec I (World.init σ A feed) = some r →
    ∃ out, h.Runtime I (World.init σ A feed) out ∧ Matches out r

/-- `ImplementsH` for deployment (§7.2), in the shape of `ImplementsDeployPSame`: every run of
    `ir`'s constructor on arguments `validArgs` admits, its result put after `irRuntime`, that
    ends under a feed is matched by some run of `h`'s init section under the same feed.  The
    machine IR's model of a sidecar takes `irRuntime := .empty` (its init section never
    returns, `Sidecar.runSection`). -/
def ImplementsDeployH (h : Object) (ir : ContractModel) (creation irRuntime : ByteArray)
    (validArgs : ByteArray → Prop) : Prop :=
  ∀ I σ A feed args r, validArgs args → I.code = creation ++ args → OwnerExists σ I →
    I.perm = true →
    (ir.init args >>= fun tail => pure (irRuntime ++ tail)).exec I (World.init σ A feed)
      = some r →
    ∃ out, h.Deploy args I (World.init σ A feed) out ∧ Matches out r

end Fe.Sonatina.H
