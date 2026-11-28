import Fe.Sonatina.Stage3.Place.Sidecar
import Fe.Sonatina.Stage3.Place.FixQ

/-!
# The deployed code is the runtime the runtime half is about

`slice1_sound` says the init bytes deploy as H's init section does, and the runtime bytes run as
H's runtime section does, but nothing in its three hypotheses ties what the init section
returns, `evm_return_code o l`, a slice of the running code (`I.code.readWithPadding o l`), to
`s.code "runtime"` (review 27, H2).  This file adds that link, without changing a definition or
statement of the chain:

- `Sidecar.embedsRuntime s`: the init section's symbol for the embedded runtime section (`embed
  .runtime as &sym` in the object), `(off, size)` in its symbol table, lies in the init bytes,
  and the init bytes there are `s.code "runtime"` (`embedsRuntime_read`: any code that starts
  with the init bytes reads the runtime bytes there).
- `HSection.deployReturns hs sym`: a syntactic check of H's init section: no function has an
  `evm_return`, `evm_stop` or `evm_self_destruct` (`evm_revert_word` reverts, and is allowed), every EVM operation is one of a list that
  never stops the run (no message call or creation, whose callee's stop H passes on), and every
  `evm_return_code` ends its block as `v = sym_addr sym; v' = sym_size sym; evm_return_code v
  v'`.  `deploy_stop_data`: every run of H's init section that stops returns the code at the
  symbol.
- `slice1_deploy_runtime`: under `slice1_sound`'s hypotheses and `Sidecar.deployCheck` (both
  checks), on every deployment the run of H's init section that the bytes agree with, if it
  stops, returns `s.code "runtime"`; and `slice1_deploy_code`: a deployment by the init bytes
  that succeeds returns `s.code "runtime"`, unless H's run is `ub` or `exhausted`.

Immutables are outside: the model has none (`immutables := 0`), and `RefinesOnH` asks for no
code after the runtime bytes.  A constructor that appends immutables would return more than the
symbol's slice, and the check would have to say where they go and the runtime half would have
to take a tail.
-/

namespace Fe.Sonatina.Stage3.Place

open Fe Fe.EVM Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Steps Ethereum Ethereum.EVM

/-! ## The init bytes embed the runtime bytes -/

/-- The symbol under which the init section of the sidecar's object embeds its runtime section
    (`embed .runtime as &sym`). -/
def _root_.Fe.Sonatina.Sidecar.runtimeSym (s : Sidecar) : Option String :=
  ((s.objects.find? (·.name == s.object)).bind (·.sections.find? (·.name == "init"))).bind
    fun sec => (sec.embeds.find? (·.2 == "runtime")).map (·.1)

/-- The place and size of the runtime section's symbol in the init section's symbol table. -/
def _root_.Fe.Sonatina.Sidecar.runtimeAt (s : Sidecar) : Option (Nat × Nat) :=
  s.runtimeSym.bind fun sym => (((s.section? "init").map (·.symbols)).getD []).lookup sym

/-- The init bytes hold the runtime bytes at the runtime section's symbol.  The bytes are
    compared as lists, which the kernel evaluates (it does not get through `ByteArray.extract`
    in reasonable time). -/
def _root_.Fe.Sonatina.Sidecar.embedsRuntime (s : Sidecar) : Bool :=
  match s.runtimeAt with
  | some (off, size) => decide (off + size ≤ (s.code "init").size) &&
      ((s.code "init").data.toList.drop off).take size == (s.code "runtime").data.toList
  | none => false

theorem getD_eq_getElem {a : Array UInt8} {i : Nat} (h : i < a.size) : a.getD i 0 = a[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- A read inside a prefix of the code. -/
theorem readWithPadding_prefix (M T : ByteArray) {a n : Nat} (h : a + n ≤ M.size) :
    (M ++ T).readWithPadding a n = M.extract a (a + n) := by
  have hs : ((M ++ T).readWithPadding a n).data.size = n := Check.readWithPadding_size' _ _ _
  have he : (M.extract a (a + n)).data.size = n := by
    simp only [ByteArray.data_extract, Array.size_extract]
    have : M.size = M.data.size := rfl
    omega
  apply ByteArray.ext
  apply Array.ext (hs.trans he.symm)
  intro i h1 h2
  have hi : i < n := hs ▸ h1
  have hM : a + i < M.data.size := by change a + i < M.size; omega
  rw [← getD_eq_getElem h1, Check.readWithPadding_getD _ _ _ _ hi, ByteArray.data_append,
    Array.getD_eq_getD_getElem?, Array.getElem?_append_left hM, Array.getElem?_eq_getElem hM,
    Option.getD_some]
  simp [ByteArray.data_extract, Array.getElem_extract]

/-- With `embedsRuntime`, any code that starts with the init bytes reads the runtime bytes at the
    runtime section's symbol. -/
theorem embedsRuntime_read {s : Sidecar} (he : s.embedsRuntime = true) :
    ∃ off size, s.runtimeAt = some (off, size) ∧
      ∀ args : ByteArray, (s.code "init" ++ args).readWithPadding off size = s.code "runtime" := by
  unfold Sidecar.embedsRuntime at he
  split at he
  · next off size hat =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    refine ⟨off, size, hat, fun args => ?_⟩
    rw [readWithPadding_prefix _ _ he.1]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      Nat.add_sub_cancel_left]
    exact he.2
  · cases he

/-! ## H's init section returns the code at the symbol -/

/-- The EVM operations of H that never end the run with `stop`: no message call or creation (H
    passes the callee's stop on), and among the memory-free ones, those whose model does not
    stop (`NoStop`). -/
def _root_.Fe.Sonatina.EvmOp.noStop : EvmOp → Bool
  | .address | .origin | .caller | .callValue | .calldataLoad | .calldataSize | .codeSize
  | .sload | .sstore | .addMod | .mulMod => true
  | .mload | .mstore | .mstore8 | .keccak256 | .mcopy | .log _ | .calldataCopy | .codeCopy
  | .extCodeCopy | .returnDataCopy => true
  | _ => false

/-- An instruction of H that never ends the run with `stop`. -/
def _root_.Fe.Sonatina.H.HInst.noStop : HInst → Bool
  | .base (.evm op _) => op.noStop
  | _ => true

/-- A terminator other than `evm_return`, `evm_stop` and `evm_self_destruct`. -/
def _root_.Fe.Sonatina.Term.noStop : Term → Bool
  | .evmReturn .. | .evmStop | .evmSelfDestruct _ => false
  | _ => true

/-- The block ends `v = sym_addr sym; v' = sym_size sym; evm_return_code v v'`. -/
def _root_.Fe.Sonatina.H.HBlock.returnsSym (b : HBlock) (sym : String) : Bool :=
  match b.term, b.body.reverse with
  | .returnCode (.var a) (.var l),
      ⟨[(l', _)], .base (.symSize s₂)⟩ :: ⟨[(a', _)], .base (.symAddr s₁)⟩ :: _ =>
    a == a' && l == l' && a != l && s₁ == sym && s₂ == sym
  | _, _ => false

/-- Every function of the section: no statement that may stop the run, no `evm_return`,
    `evm_stop` or `evm_self_destruct`, and every `evm_return_code` returns the code at `sym`
    (`HBlock.returnsSym`). -/
def _root_.Fe.Sonatina.H.HSection.deployReturns (hs : HSection) (sym : String) : Bool :=
  hs.module.funcs.all fun f => f.blocks.all fun b => b.body.all (·.inst.noStop) &&
    match b.term with
    | .base t => t.noStop
    | .returnCode .. => b.returnsSym sym
    | .revertWord .. => true

theorem noStop_stuck {α : Type} : (stuck : FeM α).NoStop := by
  intro _ _ _ _ h; cases h

theorem noStop_selfAddress : Fe.EVM.selfAddress.NoStop := by
  unfold Fe.EVM.selfAddress; no_stop_core
theorem noStop_origin : Fe.EVM.origin.NoStop := by unfold Fe.EVM.origin; no_stop_core
theorem noStop_callvalue : Fe.EVM.callvalue.NoStop := by unfold Fe.EVM.callvalue; no_stop_core
theorem noStop_calldataload (o : UInt256) : (Fe.EVM.calldataload o).NoStop := by
  unfold Fe.EVM.calldataload; no_stop_core
theorem noStop_calldatasize : Fe.EVM.calldatasize.NoStop := by
  unfold Fe.EVM.calldatasize; no_stop_core
theorem noStop_codesize : Fe.EVM.codesize.NoStop := by unfold Fe.EVM.codesize; no_stop_core

/-- A memory-free EVM operation of the list never stops the run. -/
theorem run_noStop {op : EvmOp} (h : op.noStop = true) (args : List UInt256) :
    op.memFree = true → (op.run args).NoStop := by
  intro hm
  cases op <;> (try (exfalso; revert h; decide)) <;> (try (exfalso; revert hm; decide)) <;>
    (try (simp [EvmOp.memFree] at hm; done)) <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, args⟩⟩⟩⟩ <;> (unfold EvmOp.run; dsimp only) <;>
    first
      | exact noStop_stuck
      | exact Fe.M.NoStop.pure _
      | (refine Fe.M.NoStop.bind ?_ fun _ => Fe.M.NoStop.pure _
         first
          | with_reducible exact noStop_selfAddress | with_reducible exact noStop_origin
          | with_reducible exact noStop_caller | with_reducible exact noStop_callvalue
          | with_reducible exact noStop_calldataload _
          | with_reducible exact noStop_calldatasize | with_reducible exact noStop_codesize
          | with_reducible exact noStop_sload _ | with_reducible exact noStop_sstore _ _)

/-- A run of the model library that `liftFe` lifts ends the run only as the computation ends. -/
theorem liftFe_exit {α : Type} {I : ExecutionEnv} {st : H.State} {m : FeM α}
    {k : α → H.State → IRes} {e : Exit World} (hk : ∀ a st', k a st' ≠ .exit e)
    (h : liftFe I st m k = .exit e) : m.exec I st.world = some (.error e) := by
  unfold liftFe at h
  split at h
  · cases h
  · next e' he => cases h; exact he
  · next a w _ => exact absurd h (hk _ _)

/-- An EVM operation of the list never stops the run. -/
theorem evmH_noStop {I : ExecutionEnv} {st : H.State} {op : EvmOp} {vs : List H.Val}
    (h : op.noStop = true) {d : ByteArray} {w : World} : evmH I st op vs ≠ .exit (.stop d w) := by
  intro he
  unfold evmH at he
  split at he
  · cases he
  split at he
  · next hm =>
    refine run_noStop h _ hm I st.world d w (liftFe_exit (fun _ _ => ?_) he)
    split <;> simp
  · cases op <;> simp only [EvmOp.noStop] at h <;> (repeat' split at he) <;>
      simp_all [liftFe] <;> (repeat' split at he) <;> simp_all
    all_goals exact noStop_emit _ _ I _ d w ‹_›

/-- An instruction of the list never stops the run. -/
theorem stepInst_noStop {c : H.Ctx} {I : ExecutionEnv} {env : HEnv} {st : H.State} {i : HInst}
    (h : i.noStop = true) {d : ByteArray} {w : World} : stepInst c I env st i ≠ .exit (.stop d w) := by
  intro he
  cases i with
  | base i =>
    cases i with
    | evm op args =>
      simp only [stepInst] at he
      split at he
      · exact evmH_noStop h he
      · cases he
    | _ =>
      simp only [stepInst] at he
      repeat' split at he
      all_goals cases he
  | _ =>
    simp only [stepInst] at he
    repeat' split at he
    all_goals cases he

/-- A terminator of the list never stops the run. -/
theorem stepTerm_noStop {I : ExecutionEnv} {env : HEnv} {st : H.State} {t : Term}
    (h : t.noStop = true) {d : ByteArray} {w : World} :
    stepTerm I env st (.base t) ≠ .halt (.ends (.error (.stop d w))) := by
  intro he
  cases t <;> simp only [Term.noStop] at h <;> simp only [stepTerm] at he <;>
    (repeat' split at he) <;> simp_all

/-- No terminator ends the call by returning: a halt of H is an exit. -/
theorem stepTerm_not_ok {I : ExecutionEnv} {env : HEnv} {st : H.State} {t : Term}
    {r : ByteArray × World} : stepTerm I env st (.base t) ≠ .halt (.ends (.ok r)) := by
  intro he
  cases t <;> simp only [stepTerm] at he <;> (repeat' split at he) <;> simp_all

/-- `evm_revert_word` reverts: it never returns or stops. -/
theorem stepTerm_revertWord {I : ExecutionEnv} {env : HEnv} {st : H.State} {a b : Operand}
    {d : ByteArray} {w : World} :
    stepTerm I env st (.revertWord a b) ≠ .halt (.ends (.ok (d, w))) ∧
      stepTerm I env st (.revertWord a b) ≠ .halt (.ends (.error (.stop d w))) := by
  constructor <;> intro he <;> simp only [stepTerm] at he <;> (repeat' split at he) <;> simp_all

/-! ## What H's runs of such a section return -/

/-- A run of statements that goes on is a run of a prefix and then of the rest. -/
theorem execBody_append {P : HSection} {I : ExecutionEnv} :
    ∀ {xs ys : List HStmt} {env env₂ : HEnv} {st st₂ : H.State},
      ExecBody P I env (xs ++ ys) st (.cont env₂ st₂) →
      ∃ env₁ st₁, ExecBody P I env xs st (.cont env₁ st₁) ∧
        ExecBody P I env₁ ys st₁ (.cont env₂ st₂)
  | [], _, _, _, _, _, h => ⟨_, _, .nil, h⟩
  | _ :: _, _, _, _, _, _, h => by
    cases h with
    | step hi hb hr =>
      obtain ⟨_, _, h1, h2⟩ := execBody_append hr; exact ⟨_, _, .step hi hb h1, h2⟩
    | alloca hs hn ha hf hb hr =>
      obtain ⟨_, _, h1, h2⟩ := execBody_append hr; exact ⟨_, _, .alloca hs hn ha hf hb h1, h2⟩
    | malloc hs hv hbud ha hf hb hr =>
      obtain ⟨_, _, h1, h2⟩ := execBody_append hr
      exact ⟨_, _, .malloc hs hv hbud ha hf hb h1, h2⟩
    | call hs ha hc hb hr =>
      obtain ⟨_, _, h1, h2⟩ := execBody_append hr; exact ⟨_, _, .call hs ha hc hb h1, h2⟩

/-- A statement `x = sym_addr sym` or `x = sym_size sym` binds `x` to the symbol's place or
    size. -/
theorem execBody_sym {P : HSection} {I : ExecutionEnv} {env env' : HEnv} {st st' : H.State}
    {x : Nat} {t : Ty} {sym : String} {off size : Nat}
    (hsym : P.symbols.lookup sym = some (off, size)) :
    (ExecBody P I env [⟨[(x, t)], .base (.symAddr sym)⟩] st (.cont env' st') →
      env' = env.insert x (.int 256 off)) ∧
    (ExecBody P I env [⟨[(x, t)], .base (.symSize sym)⟩] st (.cont env' st') →
      env' = env.insert x (.int 256 size)) := by
  constructor <;> intro h <;> obtain ⟨vals, hb, hi | ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, _, hi⟩⟩ :=
    execBody_one h <;> (try cases hi) <;>
    simp only [stepInst, HSection.ctx, hsym, IRes.ok.injEq] at hi <;> obtain ⟨rfl, -⟩ := hi <;>
    exact (bindVals_one hb).2

/-- A block body that ends `a = sym_addr sym; l = sym_size sym` leaves `a` and `l` bound to the
    symbol's place and size. -/
theorem execBody_symTail {P : HSection} {I : ExecutionEnv} {env env₂ : HEnv} {st st₂ : H.State}
    {pre : List HStmt} {a l : Nat} {ta tl : Ty} {sym : String} {off size : Nat}
    (hsym : P.symbols.lookup sym = some (off, size)) (hne : a ≠ l)
    (h : ExecBody P I env (pre ++ [⟨[(a, ta)], .base (.symAddr sym)⟩,
      ⟨[(l, tl)], .base (.symSize sym)⟩]) st (.cont env₂ st₂)) :
    env₂[a]? = some (.int 256 off) ∧ env₂[l]? = some (.int 256 size) := by
  obtain ⟨_, _, -, h2⟩ := execBody_append h
  obtain ⟨_, _, h3, h4⟩ := execBody_append (xs := [_]) (ys := [_]) h2
  rw [(execBody_sym hsym).2 h4, (execBody_sym hsym).1 h3]
  refine ⟨?_, Std.TreeMap.getElem?_insert_self⟩
  rw [Std.TreeMap.getElem?_insert]
  simp only [compare_eq_iff_eq, Ne.symm hne, ↓reduceIte]
  exact Std.TreeMap.getElem?_insert_self

/-- The block's statements and terminator as `deployReturns` checks them. -/
theorem deployReturns_block {hs : HSection} {sym : String} (hd : hs.deployReturns sym = true)
    {f : HFunc} (hf : f ∈ hs.module.funcs) {b : HBlock} (hb : b ∈ f.blocks) :
    (∀ s ∈ b.body, s.inst.noStop = true) ∧ (match b.term with
      | .base t => t.noStop
      | .returnCode .. => b.returnsSym sym
      | .revertWord .. => true) = true := by
  unfold HSection.deployReturns at hd
  simp only [List.all_eq_true, Bool.and_eq_true] at hd
  exact hd f hf b hb

/-- A block `returnsSym` accepts. -/
theorem returnsSym_spec {b : HBlock} {sym : String} (h : b.returnsSym sym = true) :
    ∃ a l ta tl pre, b.term = .returnCode (.var a) (.var l) ∧ a ≠ l ∧
      b.body = pre ++ [⟨[(a, ta)], .base (.symAddr sym)⟩, ⟨[(l, tl)], .base (.symSize sym)⟩] := by
  unfold HBlock.returnsSym at h
  split at h
  · rename_i a l l' tl s₂ a' ta s₁ rest ht hb
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, hne⟩, rfl⟩, rfl⟩ := h
    refine ⟨a, l, ta, tl, rest.reverse, ht, hne, ?_⟩
    rw [← List.reverse_reverse b.body, hb]
    simp
  · cases h

/-- A run that ends the call successfully, by returning or stopping, does so with data `R`. -/
def StopsWith (R : ByteArray) (o : Outcome) : Prop :=
  ∀ d w, o = .ends (.ok (d, w)) ∨ o = .ends (.error (.stop d w)) → d = R

/-- A run of statements that halts stops with `R`, if it stops. -/
def _root_.Fe.Sonatina.H.BOut.stops (R : ByteArray) : BOut → Prop
  | .halt o => StopsWith R o
  | .cont .. => True

/-- A run of a function that halts stops with `R`, if it stops. -/
def _root_.Fe.Sonatina.H.FOut.stops (R : ByteArray) : FOut → Prop
  | .halt o => StopsWith R o
  | .ret .. => True

/-- Every run of a function of a section `deployReturns` accepts that stops returns the code at
    the symbol. -/
theorem func_stops {P : HSection} {I : ExecutionEnv} {sym : String} {off size : Nat}
    (hd : P.deployReturns sym = true) (hsym : P.symbols.lookup sym = some (off, size))
    {name : String} {args : List H.Val} {st : H.State} {o : FOut}
    (h : ExecFunc P I name args st o) : o.stops (I.code.readWithPadding off size) :=
  ExecFunc.rec
    (motive_1 := fun _ body _ o _ => (∀ s ∈ body, s.inst.noStop = true) →
      o.stops (I.code.readWithPadding off size))
    (motive_2 := fun f _ _ _ _ o _ => f ∈ P.module.funcs → o.stops (I.code.readWithPadding off size))
    (motive_3 := fun _ _ _ o _ => o.stops (I.code.readWithPadding off size))
    (nil := fun _ => trivial)
    (step := fun _ _ _ ih hb => ih fun s hs => hb s (List.mem_cons_of_mem _ hs))
    (exit := fun hi hb d w he => by
      rcases he with he | he <;> cases he
      exact absurd hi (stepInst_noStop (hb _ List.mem_cons_self)))
    (ub := fun _ _ d w he => by rcases he with he | he <;> cases he)
    (alloca := fun _ _ _ _ _ _ ih hb => ih fun s hs => hb s (List.mem_cons_of_mem _ hs))
    (malloc := fun _ _ _ _ _ _ _ ih hb => ih fun s hs => hb s (List.mem_cons_of_mem _ hs))
    (exhausted := fun _ _ _ _ d w he => by rcases he with he | he <;> cases he)
    (call := fun _ _ _ _ _ _ ih hb => ih fun s hs => hb s (List.mem_cons_of_mem _ hs))
    (callHalt := fun _ _ _ ih _ => ih)
    (goto := fun _ _ _ _ _ _ ih hf => ih hf)
    (ret := fun _ _ _ _ _ _ => trivial)
    (halt := fun hb _ hbody ht _ hf d w he => by
      obtain ⟨-, hterm⟩ := deployReturns_block hd hf (List.mem_of_find?_eq_some hb)
      split at hterm
      · next t heq =>
        rw [heq] at ht
        rcases he with rfl | rfl
        · exact absurd ht stepTerm_not_ok
        · exact absurd ht (stepTerm_noStop hterm)
      · obtain ⟨a, l, ta, tl, pre, hrc, hne, hbd⟩ := returnsSym_spec hterm
        rw [hbd] at hbody
        obtain ⟨ha, hl⟩ := execBody_symTail hsym hne hbody
        rw [hrc] at ht
        simp only [stepTerm, evalOp, ha, hl, TRes.halt.injEq] at ht
        rcases he with rfl | rfl
        · simp at ht
        · simp only [Outcome.ends.injEq, Except.error.injEq, Exit.stop.injEq] at ht
          rw [← ht.1]
          rfl
      · next a b heq =>
        rw [heq] at ht
        rcases he with rfl | rfl
        · exact absurd ht stepTerm_revertWord.1
        · exact absurd ht stepTerm_revertWord.2)
    (bodyHalt := fun hb _ _ ih hf =>
      ih (deployReturns_block hd hf (List.mem_of_find?_eq_some hb)).1)
    (mk := fun hf _ _ _ ih => ih (List.mem_of_find?_eq_some hf))
    h

/-- Every run of H's init section that `deployReturns` accepts and that stops returns the code
    at the symbol. -/
theorem deploy_stop_data {h : H.Object} {sym : String} {off size : Nat}
    (hd : h.init.deployReturns sym = true) (hsym : h.init.symbols.lookup sym = some (off, size))
    {args : ByteArray} {I : ExecutionEnv} {w : World} {out : Outcome}
    (hr : h.Deploy args I w out) : StopsWith (I.code.readWithPadding off size) out :=
  func_stops hd hsym hr

/-! ## Slice 1 with the deployed code -/

/-- The init bytes embed the runtime bytes at the runtime section's symbol (`embedsRuntime`),
    and H's init section returns the code there (`deployReturns`). -/
def _root_.Fe.Sonatina.Sidecar.deployCheck (s : Sidecar) (h : H.Object) : Bool :=
  s.embedsRuntime && match s.runtimeSym with
    | some sym => h.init.deployReturns sym
    | none => false

/-- The section that `placeSec` accepts has H's section's symbols. -/
theorem placeSec_symbols {t : Sidecar} {hs : HSection} {name : String} {rec : Record}
    (hp : placeSec t hs name rec = true) : (t.section? name).map (·.symbols) = some hs.symbols := by
  unfold placeSec at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · split at hp
      · cases hp
      · next code hcode =>
        split at hp
        · cases hp
        · simp only [Bool.and_eq_true, beq_iff_eq] at hp
          rw [hcode, Option.map_some, hp.1.1.2]

/-- `asLowered` keeps each section's symbols. -/
theorem asLowered_symbols (s : Sidecar) (n : String) :
    (s.asLowered.section? n).map (·.symbols) = (s.section? n).map (·.symbols) := by
  simp only [Sidecar.asLowered, Sidecar.lowered, withMachine_section?, Option.map_map]
  congr 1
  funext c
  simp only [Function.comp]
  split <;> split <;> rfl

/-- With `placeCheck` and `deployCheck`, every run of H's init section on code that starts with
    the init bytes that returns or stops does so with the runtime bytes. -/
theorem deploy_runtime {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hp : s.placeCheck h rr ri = true) (hd : s.deployCheck h = true) {args : ByteArray}
    {I : ExecutionEnv} {w : World} {out : Outcome} (hI : I.code = s.code "init" ++ args)
    (hr : h.Deploy args I w out) : StopsWith (s.code "runtime") out := by
  simp only [Sidecar.deployCheck, Bool.and_eq_true] at hd
  obtain ⟨off, size, hat, hread⟩ := embedsRuntime_read hd.1
  unfold Sidecar.runtimeAt at hat
  cases hsym : s.runtimeSym with
  | none => rw [hsym] at hat; cases hat
  | some sym =>
    rw [hsym] at hat hd
    simp only [Option.bind_some] at hat
    simp only [Sidecar.placeCheck, Bool.and_eq_true] at hp
    have hsy := placeSec_symbols hp.2
    rw [asLowered_symbols] at hsy
    rw [hsy, Option.getD_some] at hat
    have := deploy_stop_data hd.2 hat hr
    rwa [hI, hread] at this

/-- Slice 1 with the deployed code: under `slice1_sound`'s hypotheses and `deployCheck`, the
    runtime bytes refine the handover object, and on every deployment by the init bytes, the
    bytes run out of gas or of stack, or, under the call's real feed, some run of H's init
    section is `ub` or `exhausted` or ends as the bytes do, and returns or stops, if it does, with
    the runtime bytes. -/
theorem slice1_deploy_runtime {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hv : s.validate = true) (hc : Fe.Sonatina.Check.check s = true)
    (hp : s.placeCheck h rr ri = true) (hd : s.deployCheck h = true) :
    RefinesOnH .P1 (s.code "runtime") h CalldataFits ∧
      ∀ σ σ₀ g A I args, I.code = s.code "init" ++ args → OwnerExists σ I → I.perm = true →
        CalldataFits I →
        Exhausted (Ξ σ σ₀ g A I) ∨
          ∃ feed, RealFeed σ σ₀ g A I feed ∧ ∃ out, h.Deploy args I (World.init σ A feed) out ∧
            StopsWith (s.code "runtime") out ∧
            (out = .ub ∨ out = .exhausted ∨
              ∃ r, out = .ends r ∧ Agrees .P1 (Ξ σ σ₀ g A I) (some r)) := by
  obtain ⟨hR, hD⟩ := slice1_sound hv hc hp
  refine ⟨hR, fun σ σ₀ g A I args hI ho hperm hcf => ?_⟩
  rcases hD σ σ₀ g A I args trivial hI ho hperm hcf with hx | ⟨feed, hreal, out, hout, hag⟩
  · exact .inl hx
  · exact .inr ⟨feed, hreal, out, hout, deploy_runtime hp hd hI hout, hag⟩

/-- A deployment by the init bytes that succeeds returns the runtime bytes as the code, unless,
    under the call's real feed, H's init section has a run that is `ub` or `exhausted`. -/
theorem slice1_deploy_code {s : Sidecar} {h : H.Object} {rr ri : Record}
    (hv : s.validate = true) (hc : Fe.Sonatina.Check.check s = true)
    (hp : s.placeCheck h rr ri = true) (hd : s.deployCheck h = true)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {args : ByteArray}
    (hI : I.code = s.code "init" ++ args) (ho : OwnerExists σ I) (hperm : I.perm = true)
    (hcf : CalldataFits I) {accounts : AccountMap} {g' : UInt256} {A' : Substate}
    {code : ByteArray} (hx : Ξ σ σ₀ g A I = .ok (.success (accounts, g', A') code)) :
    code = s.code "runtime" ∨ ∃ feed, RealFeed σ σ₀ g A I feed ∧
      (h.Deploy args I (World.init σ A feed) .ub ∨
        h.Deploy args I (World.init σ A feed) .exhausted) := by
  rcases (slice1_deploy_runtime hv hc hp hd).2 σ σ₀ g A I args hI ho hperm hcf with
    hex | ⟨feed, hreal, out, hout, hstop, hcase⟩
  · rcases hex with hex | hex <;> rw [hx] at hex <;> cases hex
  rcases hcase with rfl | rfl | ⟨r, rfl, hag⟩
  · exact .inr ⟨feed, hreal, .inl hout⟩
  · exact .inr ⟨feed, hreal, .inr hout⟩
  · left
    rcases r with e | ⟨d, w⟩
    · cases e with
      | stop d w =>
        obtain ⟨_, _, he, -⟩ := hag
        rw [hx] at he
        cases he
        exact hstop _ _ (.inr rfl)
      | revert => obtain ⟨_, _, he, -⟩ := hag; rw [hx] at he; cases he
      | panic => obtain ⟨_, _, he, -⟩ := hag; rw [hx] at he; cases he
      | _ => simp only [Agrees] at hag; rw [hx] at hag; cases hag
    · obtain ⟨_, _, he, -⟩ := hag
      rw [hx] at he
      cases he
      exact hstop _ _ (.inl rfl)

end Fe.Sonatina.Stage3.Place
