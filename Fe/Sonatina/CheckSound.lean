import Fe.Sonatina.Check
import Fe.Sonatina.Interp
import Fe.Sonatina.Refine
import Reasoning.EVMWord

/-!
# Towards the soundness of the checker

What `check` is to imply, and the first lemmas of its proof.

`Sound s` is the statement `check_sound` is to prove of every sidecar `s` with `check s = true`:
the runtime bytes refine the machine IR's runtime, and the init bytes its constructor.  It is
at profile `P0` here; `P1` holds by the same proof once the block lemmas carry the substate (logs)
and the revert output, which EVMLean's `XstepN_X_halt_success` and `XstepN_X_halt_revert` give.

`Expr.eval` is the meaning of the checker's expressions in a frame: an atom is the word the
environment `env` gives the machine value, a constant itself, an operation what `Xstep`
computes of the operands.  `eval_mkOp` is the soundness of the checker's constant folding.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM Fe Fe.EVM

/-- The bytes of a section of the sidecar. -/
def _root_.Fe.Sonatina.Sidecar.code (s : Sidecar) (name : String) : ByteArray :=
  ((s.section? name).map (·.bytecode)).getD .empty

/-- What `check s = true` is to imply. -/
def Sound (s : Sidecar) : Prop :=
  RefinesOn .P0 (s.code "runtime") (s.model .machine) CalldataFits
    ∧ RefinesDeploy .P0 (s.code "init") .empty (s.model .machine) (fun _ => True)

/-- An opcode of the environment, as `Xstep` pushes it in the frame `ee`. -/
def envOp (ee : ExecutionEnv) : Operation → List UInt256 → Option UInt256
  | .CALLVALUE, [] => some ee.weiValue
  | .CALLER, [] => some (.ofNat ee.source.val)
  | .ADDRESS, [] => some (.ofNat ee.codeOwner.val)
  | .ORIGIN, [] => some (.ofNat ee.sender.val)
  | .CALLDATASIZE, [] => some (.ofNat ee.calldata.size)
  | .CODESIZE, [] => some (.ofNat ee.code.size)
  | .CALLDATALOAD, [a] => some (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32))
  | _, _ => none

/-- A pure opcode on words in the frame `ee`. -/
def opEval (ee : ExecutionEnv) (op : Operation) (args : List UInt256) : Option UInt256 :=
  evalOp op args <|> envOp ee op args

/-- The word an expression denotes in the frame `ee`, where machine value `id` is `env id`. -/
def Expr.eval (ee : ExecutionEnv) (env : Nat → UInt256) : Expr → Option UInt256
  | .atom id => some (env id)
  | .const v => some (UInt256.ofNat v)
  | .op0 op => opEval ee op []
  | .op1 op a => do opEval ee op [← a.eval ee env]
  | .op2 op a b => do opEval ee op [← a.eval ee env, ← b.eval ee env]
  | .op3 op a b c => do opEval ee op [← a.eval ee env, ← b.eval ee env, ← c.eval ee env]

theorem constWords_eval {ee : ExecutionEnv} {env : Nat → UInt256} :
    ∀ {args : List Expr} {words : List UInt256}, args.mapM constWord = some words →
      args.mapM (·.eval ee env) = some words
  | [], words, h => by simpa using h
  | a :: rest, words, h => by
    cases a with
    | const v =>
      cases hr : rest.mapM constWord with
      | none => simp [constWord, hr] at h
      | some tl =>
        simp only [List.mapM_cons, constWord, hr, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        simp [Expr.eval, constWords_eval hr]
    | _ => simp [constWord] at h

/-- Folding is sound: the constant is what the operation computes of its operands. -/
theorem foldConst_eval {ee : ExecutionEnv} {env : Nat → UInt256} {op : Operation}
    {args : List Expr} {e : Expr} (h : foldConst op args = some e) :
    e.eval ee env = (args.mapM (·.eval ee env)) >>= opEval ee op := by
  unfold foldConst at h
  cases hw : args.mapM constWord with
  | none => simp [hw] at h
  | some words =>
    cases hev : evalOp op words with
    | none => simp [hw, hev] at h
    | some w =>
      simp only [hw, hev, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      simp [constWords_eval hw, Expr.eval, opEval, hev, Reasoning.Theory.u256_ofNat_toNat]

end Fe.Sonatina.Check
