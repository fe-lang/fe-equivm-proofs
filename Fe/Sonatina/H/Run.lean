import Fe.Sonatina.H.Sem

/-!
# An executable reference for H (design §3.1)

`runFunc` runs H with an explicit `Oracle` for its choices, the address word and the fresh
bytes of each allocation, and fuel: every statement, block and call spends one unit.  It returns
an `RRes`: a result, a halt with the outcome (and where it arose, for the reports), or why it
stopped short: a construct H does not define (`stuck`), a run of the model library that does
not terminate (`diverge`, where it arose), no fuel left, or an oracle that chose an address word
H does not allow (`badOracle`, `AddrOk`).

`runH_sound` proves it a sub-relation of H: a result or a halt `runFunc` returns is a run of
`ExecFunc` (likewise `runBlocks`, `runBody`); `runRuntime_sound` and `runDeploy_sound` give
`Object.Runtime` and `Object.Deploy`.  Whatever the oracle, so H's nondeterminism is exercised
by running it under different oracles (`scripts/HDiff.lean`).

It uses ordinary compiled evaluation in scripts; the kernel never evaluates it.
-/

namespace Fe.Sonatina.H

open Ethereum Ethereum.EVM Fe Fe.EVM Fe.Sonatina

/-- What the oracle is told of an allocation: the function and the value it defines, its kind
    and size, the id its block gets, and the heap requests before it. -/
structure AllocInfo where
  func : String
  site : Nat
  kind : BlockKind
  size : Nat
  id : Nat
  heapReq : Nat

/-- The choices of a run: each allocation's address word and the fresh byte at each offset, and
    the largest block it will materialize (a larger one stops the run as `badOracle`). -/
structure Oracle where
  addr : AllocInfo → Nat
  fresh : AllocInfo → Nat → UInt8
  maxSize : Nat := 2 ^ 24

/-- How a run of `runFunc` ends. -/
inductive RRes (α : Type) where
  | ok (a : α)
  /-- A halt, and where it arose. -/
  | halt (o : Outcome) (at_ : String)
  | stuck (why : String)
  /-- The model library's run does not terminate, and where. -/
  | diverge (at_ : String)
  | fuel
  | badOracle (why : String)

def RRes.bind {α β : Type} : RRes α → (α → RRes β) → RRes β
  | .ok a, k => k a
  | .halt o w, _ => .halt o w
  | .stuck w, _ => .stuck w
  | .diverge w, _ => .diverge w
  | .fuel, _ => .fuel
  | .badOracle w, _ => .badOracle w

/-- The instructions the relation runs itself. -/
inductive Special where
  | alloca (ty : Ty)
  | malloc (size : Operand)
  | call (callee : String) (args : List Operand)
  | none

def HInst.special : HInst → Special
  | .base (.alloca ty) => .alloca ty
  | .base (.malloc a) => .malloc a
  | .base (.call c args) => .call c args
  | _ => .none

theorem HInst.special_alloca {i : HInst} {ty : Ty} (h : i.special = .alloca ty) :
    i = .base (.alloca ty) := by
  cases i with
  | base i => cases i <;> simp_all [HInst.special]
  | _ => simp [HInst.special] at h

theorem HInst.special_malloc {i : HInst} {a : Operand} (h : i.special = .malloc a) :
    i = .base (.malloc a) := by
  cases i with
  | base i => cases i <;> simp_all [HInst.special]
  | _ => simp [HInst.special] at h

theorem HInst.special_call {i : HInst} {c : String} {args : List Operand}
    (h : i.special = .call c args) : i = .base (.call c args) := by
  cases i with
  | base i => cases i <;> simp_all [HInst.special]
  | _ => simp [HInst.special] at h

/-- The value a statement defines first, naming its allocation site for the oracle. -/
def HStmt.site (s : HStmt) : Nat := (s.dsts.head?.map (·.1)).getD 0

mutual

/-- Run the statements `ss` of block `bid` of `f`, the first being the `k`th. -/
def runBody (P : HSection) (O : Oracle) (I : ExecutionEnv) (f : HFunc) (bid : Nat) :
    Nat → Nat → HEnv → List HStmt → State → RRes (HEnv × State)
  | 0, _, _, _, _ => .fuel
  | _ + 1, _, env, [], st => .ok (env, st)
  | fuel + 1, k, env, s :: rest, st =>
    let at_ : String := s!"{f.name} block{bid} #{k}: {(repr s.inst).pretty 100000}"
    match s.inst.special with
    | .alloca ty => match sizeOf P.module.structs sizeFuel ty with
      | none => .stuck s!"an alloca of a type with no size at {at_}"
      | some n =>
        let info : AllocInfo := ⟨f.name, s.site, .alloca, n, st.blocks.size, st.heapReq⟩
        let addr := O.addr info
        if AddrOk addr n ∧ n ≤ O.maxSize then
          match bindVals env s.dsts [.ptr st.blocks.size 0] with
          | some env' => runBody P O I f bid fuel (k + 1) env' rest
              (st.alloc .alloca n addr ((List.range n).map (O.fresh info)))
          | none => .stuck s!"ill-typed result at {at_}"
        else .badOracle s!"address word {addr} for {n} bytes at {at_}"
    | .malloc a => match evalOp env a with
      | none => .stuck s!"an operand with no value at {at_}"
      | some v =>
        let n := st.word v
        if heapBudget ≤ st.heapReq + align32 n then .halt .exhausted at_
        else
          let info : AllocInfo := ⟨f.name, s.site, .malloc, n, st.blocks.size, st.heapReq⟩
          let addr := O.addr info
          if AddrOk addr n ∧ n ≤ O.maxSize then
            match bindVals env s.dsts [.ptr st.blocks.size 0] with
            | some env' => runBody P O I f bid fuel (k + 1) env' rest
                { st.alloc .malloc n addr ((List.range n).map (O.fresh info)) with
                  heapReq := st.heapReq + align32 n }
            | none => .stuck s!"ill-typed result at {at_}"
          else .badOracle s!"address word {addr} for {n} bytes at {at_}"
    | .call callee args => match args.mapM (evalOp env) with
      | none => .stuck s!"an operand with no value at {at_}"
      | some vs => (runFunc P O I fuel callee vs st).bind fun (vals, st') =>
        match bindVals env s.dsts vals with
        | some env' => runBody P O I f bid fuel (k + 1) env' rest st'
        | none => .stuck s!"ill-typed result at {at_}"
    | .none => match stepInst P.ctx I env st s.inst with
      | .ok vals st' => match bindVals env s.dsts vals with
        | some env' => runBody P O I f bid fuel (k + 1) env' rest st'
        | none => .stuck s!"ill-typed result at {at_}"
      | .exit e => .halt (.ends (.error e)) at_
      | .ub => .halt .ub at_
      | .stuck why => .stuck s!"{why} at {at_}"
      | .diverge => .diverge at_

/-- Run `f` from block `id`, entered from `prev`. -/
def runBlocks (P : HSection) (O : Oracle) (I : ExecutionEnv) :
    Nat → HFunc → HEnv → Option Nat → Nat → State → RRes (List Val × State)
  | 0, _, _, _, _, _ => .fuel
  | fuel + 1, f, env, prev, id, st =>
    match f.block? id with
    | none => .stuck s!"no block {id} in {f.name}"
    | some b => match enter env prev b with
      | none => .stuck s!"the phis of {f.name} block{id}"
      | some env₁ => (runBody P O I f id fuel 0 env₁ b.body st).bind fun (env₂, st₂) =>
        let at_ : String := s!"{f.name} block{id} terminator: {(repr b.term).pretty 100000}"
        match stepTerm I env₂ st₂ b.term with
        | .goto d => runBlocks P O I fuel f env₂ (some id) d st₂
        | .ret vals => .ok (vals, st₂)
        | .halt o => .halt o at_
        | .stuck why => .stuck s!"{why} at {at_}"
        | .diverge => .diverge at_

/-- Run function `name` on `args`. -/
def runFunc (P : HSection) (O : Oracle) (I : ExecutionEnv) :
    Nat → String → List Val → State → RRes (List Val × State)
  | 0, _, _, _ => .fuel
  | fuel + 1, name, args, st =>
    match P.module.func? name with
    | none => .stuck s!"no function {name}"
    | some f => match f.blocks.head? with
      | none => .stuck s!"{name} has no blocks"
      | some e => match bindVals {} f.params args with
        | none => .stuck s!"ill-typed arguments of {name}"
        | some env => runBlocks P O I fuel f env none e.id st

end

/-- What a result of `runFunc` and its kin says: a result `Q` holds of, or a halt `H` holds of;
    the other ends say nothing. -/
def RRes.Sound {α : Type} (Q : α → Prop) (H : Outcome → Prop) : RRes α → Prop
  | .ok a => Q a
  | .halt o _ => H o
  | _ => True

theorem RRes.Sound.bind {α β : Type} {Q : α → Prop} {H H' : Outcome → Prop} {Q' : β → Prop}
    {r : RRes α} {k : α → RRes β} (hr : r.Sound Q H) (hk : ∀ a, Q a → (k a).Sound Q' H')
    (hh : ∀ o, H o → H' o) : (r.bind k).Sound Q' H' := by
  cases r <;> simp_all [RRes.bind, RRes.Sound]

theorem RRes.Sound.mono {α : Type} {Q Q' : α → Prop} {H H' : Outcome → Prop} {r : RRes α}
    (h : r.Sound Q H) (hq : ∀ a, Q a → Q' a) (hh : ∀ o, H o → H' o) : r.Sound Q' H' := by
  cases r <;> simp_all [RRes.Sound]

/-- `runBody`, `runBlocks` and `runFunc` are runs of H, whatever the oracle. -/
theorem runH_sound (P : HSection) (O : Oracle) (I : ExecutionEnv) :
    ∀ fuel,
      (∀ f bid k env ss st, (runBody P O I f bid fuel k env ss st).Sound
        (fun r => ExecBody P I env ss st (.cont r.1 r.2)) (fun o => ExecBody P I env ss st (.halt o)))
      ∧ (∀ f env prev id st, (runBlocks P O I fuel f env prev id st).Sound
        (fun r => ExecBlocks P I f env prev id st (.ret r.1 r.2))
        (fun o => ExecBlocks P I f env prev id st (.halt o)))
      ∧ (∀ name args st, (runFunc P O I fuel name args st).Sound
        (fun r => ExecFunc P I name args st (.ret r.1 r.2))
        (fun o => ExecFunc P I name args st (.halt o))) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ => ?_, fun _ _ _ => ?_⟩ <;>
      simp [runBody, runBlocks, runFunc, RRes.Sound]
  | succ fuel ih =>
    obtain ⟨ihBody, ihBlocks, ihFunc⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro f bid k env ss st
      cases ss with
      | nil => simpa [runBody, RRes.Sound] using ExecBody.nil
      | cons s rest =>
        rw [runBody]
        cases hsp : s.inst.special with
        | alloca ty =>
          have hs := HInst.special_alloca hsp
          dsimp only
          cases hn : sizeOf P.module.structs sizeFuel ty with
          | none => simp [RRes.Sound]
          | some n =>
            dsimp only
            generalize hi : (⟨f.name, s.site, .alloca, n, st.blocks.size, st.heapReq⟩ : AllocInfo)
              = info
            by_cases ha : AddrOk (O.addr info) n ∧ n ≤ O.maxSize
            · rw [if_pos ha]
              cases hb : bindVals env s.dsts [.ptr st.blocks.size 0] with
              | none => simp [RRes.Sound]
              | some env' =>
                dsimp only
                exact (ihBody f bid (k + 1) env' rest _).mono
                  (fun _ h => ExecBody.alloca hs hn ha.1 (by simp) hb h)
                  (fun _ h => ExecBody.alloca hs hn ha.1 (by simp) hb h)
            · rw [if_neg ha]; simp [RRes.Sound]
        | malloc a =>
          have hs := HInst.special_malloc hsp
          dsimp only
          cases hv : evalOp env a with
          | none => simp [RRes.Sound]
          | some v =>
            dsimp only
            by_cases hbud : heapBudget ≤ st.heapReq + align32 (st.word v)
            · rw [if_pos hbud]; simpa [RRes.Sound] using ExecBody.exhausted hs hv hbud
            · rw [if_neg hbud]
              have hbud' := Nat.lt_of_not_le hbud
              generalize hi : (⟨f.name, s.site, .malloc, st.word v, st.blocks.size, st.heapReq⟩ :
                AllocInfo) = info
              by_cases ha : AddrOk (O.addr info) (st.word v) ∧ st.word v ≤ O.maxSize
              · rw [if_pos ha]
                cases hb : bindVals env s.dsts [.ptr st.blocks.size 0] with
                | none => simp [RRes.Sound]
                | some env' =>
                  dsimp only
                  exact (ihBody f bid (k + 1) env' rest _).mono
                    (fun _ h => ExecBody.malloc hs hv hbud' ha.1 (by simp) hb h)
                    (fun _ h => ExecBody.malloc hs hv hbud' ha.1 (by simp) hb h)
              · rw [if_neg ha]; simp [RRes.Sound]
        | call callee args =>
          have hs := HInst.special_call hsp
          dsimp only
          cases hvs : args.mapM (evalOp env) with
          | none => simp [RRes.Sound]
          | some vs =>
            dsimp only
            refine RRes.Sound.bind (ihFunc callee vs st) ?_ (fun o ho => ExecBody.callHalt hs hvs ho)
            rintro ⟨vals, st'⟩ hc
            dsimp only
            cases hb : bindVals env s.dsts vals with
            | none => simp [RRes.Sound]
            | some env' =>
              dsimp only
              exact (ihBody f bid (k + 1) env' rest st').mono
                (fun _ h => ExecBody.call hs hvs hc hb h) (fun _ h => ExecBody.call hs hvs hc hb h)
        | none =>
          dsimp only
          cases hi : stepInst P.ctx I env st s.inst with
          | ok vals st' =>
            dsimp only
            cases hb : bindVals env s.dsts vals with
            | none => simp [RRes.Sound]
            | some env' =>
              dsimp only
              exact (ihBody f bid (k + 1) env' rest st').mono
                (fun _ h => ExecBody.step hi hb h) (fun _ h => ExecBody.step hi hb h)
          | exit e => simpa [RRes.Sound] using ExecBody.exit hi
          | ub => simpa [RRes.Sound] using ExecBody.ub hi
          | stuck _ => simp [RRes.Sound]
          | diverge => simp [RRes.Sound]
    · intro f env prev id st
      rw [runBlocks]
      cases hb : f.block? id with
      | none => simp [RRes.Sound]
      | some b =>
        dsimp only
        cases he : enter env prev b with
        | none => simp [RRes.Sound]
        | some env₁ =>
          dsimp only
          refine RRes.Sound.bind (ihBody f id 0 env₁ b.body st) ?_
            (fun o ho => ExecBlocks.bodyHalt hb he ho)
          rintro ⟨env₂, st₂⟩ hbody
          dsimp only
          cases ht : stepTerm I env₂ st₂ b.term with
          | goto d =>
            dsimp only
            exact (ihBlocks f env₂ (some id) d st₂).mono
              (fun _ h => ExecBlocks.goto hb he hbody ht h) (fun _ h => ExecBlocks.goto hb he hbody ht h)
          | ret vals => simpa [RRes.Sound] using ExecBlocks.ret hb he hbody ht
          | halt o => simpa [RRes.Sound] using ExecBlocks.halt hb he hbody ht
          | stuck _ => simp [RRes.Sound]
          | diverge => simp [RRes.Sound]
    · intro name args st
      rw [runFunc]
      cases hf : P.module.func? name with
      | none => simp [RRes.Sound]
      | some f =>
        dsimp only
        cases he : f.blocks.head? with
        | none => simp [RRes.Sound]
        | some e =>
          dsimp only
          cases hp : bindVals {} f.params args with
          | none => simp [RRes.Sound]
          | some env =>
            dsimp only
            exact (ihBlocks f env none e.id st).mono
              (fun _ h => ExecFunc.mk hf he hp h) (fun _ h => ExecFunc.mk hf he hp h)

/-- Run the runtime section of `h` from world `w`, under the oracle, with the fuel. -/
def runRuntime (fuel : Nat) (O : Oracle) (h : Object) (I : ExecutionEnv) (w : World) :
    RRes (List Val × State) :=
  runFunc h.runtime O I fuel h.runtime.entry [] (State.init w)

/-- Run the init section of `h` from world `w`, under the oracle, with the fuel. -/
def runDeploy (fuel : Nat) (O : Oracle) (h : Object) (I : ExecutionEnv) (w : World) :
    RRes (List Val × State) :=
  runFunc h.init O I fuel h.init.entry [] (State.init w)

/-- An outcome `runRuntime` finds, with any oracle, is one of H's (§7.2). -/
theorem runRuntime_sound {fuel : Nat} {O : Oracle} {h : Object} {I : ExecutionEnv} {w : World}
    {out : Outcome} {at_ : String} (hr : runRuntime fuel O h I w = .halt out at_) :
    h.Runtime I w out := by
  have := (runH_sound h.runtime O I fuel).2.2 h.runtime.entry [] (State.init w)
  unfold runRuntime at hr
  rw [hr] at this
  exact this

/-- An outcome `runDeploy` finds, with any oracle, is one of H's (§7.2). -/
theorem runDeploy_sound {fuel : Nat} {O : Oracle} {h : Object} {args : ByteArray}
    {I : ExecutionEnv} {w : World} {out : Outcome} {at_ : String}
    (hr : runDeploy fuel O h I w = .halt out at_) : h.Deploy args I w out := by
  have := (runH_sound h.init O I fuel).2.2 h.init.entry [] (State.init w)
  unfold runDeploy at hr
  rw [hr] at this
  exact this

end Fe.Sonatina.H
