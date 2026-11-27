import Fe.Sonatina.H.Run
import Fe.Sonatina.H.Wf

/-!
# Tests of H

Small sections, each run by `runRuntime` under two oracles (blocks far apart, and blocks at
one address word), checking the outcome: the rules of §3.2–§3.4 and §3.7 one at a time, and
that `wfH` rejects what §3.7 lists.  Each `#guard` evaluates when the module builds.
-/

namespace Fe.Sonatina.H.Tests

open Ethereum Fe Fe.EVM Fe.Sonatina

/-- A runtime section of the module text, entered at `%main`. -/
def obj (text : String) : Object :=
  let m := (Parse.parseModule text).toOption.getD default
  let s : HSection := ⟨m, "main", [(".", 0, 0)]⟩
  ⟨s, s⟩

def apart : Oracle := { addr := fun i => 2 ^ 200 * (i.id + 1), fresh := fun _ _ => 0xab }
def same : Oracle := { addr := fun _ => 0x80, fresh := fun _ _ => 0 }

/-- The outcome in a few words, of a run in a call that may change state (`perm`) or not: the
    return data's first byte, or the kind of halt. -/
def outcomeOf (perm : Bool) (o : Oracle) (h : Object) : String :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with header.fork := .Osaka, perm }
  match runRuntime 100000 o h I
      (World.init ((∅ : AccountMap).insert I.codeOwner default) default) with
  | .halt (.ends (.error (.stop d _))) _ => s!"return {d.toList}"
  | .halt (.ends (.error (.revert d))) _ => s!"revert {d.toList}"
  | .halt (.ends (.error .trap)) _ => "trap"
  | .halt (.ends (.error .oob)) _ => "oob"
  | .halt (.ends (.error .static)) _ => "static"
  | .halt (.ends _) _ => "ends"
  | .halt .ub _ => "ub"
  | .halt .exhausted _ => "exhausted"
  | .stuck w => s!"stuck {w}"
  | .diverge _ => "diverge"
  | .fuel => "fuel"
  | .badOracle w => s!"badOracle {w}"
  | .ok _ => "returns"

def outcome (o : Oracle) (text : String) : String := outcomeOf true o (obj text)

/-- Return the byte `v` (a word below 256) as one byte. -/
def ret1 (v : String) : String :=
  s!"        v90.*i256 = alloca i256;\n        mstore v90 {v} i256;\n        v91.i256 = ptr_to_int v90 i256;\n        v92.i256 = add v91 31.i256;\n        evm_return v92 1.i256;\n"

def prog (body : String) : String := s!"func public %main() \{\n    block0:\n{body}}\n"

-- A store and a load of a word in a block.
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        mstore v1 7.i256 i256;\n        v2.i256 = mload v1 i256;\n" ++ ret1 "v2")) == "return [7]"

-- An access past the end of a block is `ub` (U1a), at any address word.
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        v2.*i256 = gep v1 1.i64;\n        mstore v2 7.i256 i256;\n        evm_stop;\n") == "ub"
#guard outcome same (prog "        v1.*i256 = alloca i256;\n        v2.*i256 = gep v1 1.i64;\n        mstore v2 7.i256 i256;\n        evm_stop;\n") == "ub"

-- An access through an integer address is `ub` (U1b), a zero-length one is not.
#guard outcome apart (prog "        mstore 0.i256 7.i256 i256;\n        evm_stop;\n") == "ub"
#guard outcome apart (prog "        evm_revert 0.i256 0.i256;\n") == "revert []"
#guard outcome apart (prog "        evm_revert 0.i256 36.i256;\n") == "ub"

-- A pointer stored to memory and loaded back keeps its origin (E3, §3.4) ...
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        v2.**i256 = alloca *i256;\n        mstore v2 v1 *i256;\n        v3.*i256 = mload v2 *i256;\n        mstore v3 9.i256 i256;\n        v4.i256 = mload v1 i256;\n" ++ ret1 "v4")) == "return [9]"
-- ... and through `evm_mcopy` (review 22 H2) ...
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        v2.**i256 = alloca *i256;\n        v5.**i256 = alloca *i256;\n        mstore v2 v1 *i256;\n        evm_mcopy v5 v2 32.i256;\n        v3.*i256 = mload v5 *i256;\n        mstore v3 9.i256 i256;\n        v4.i256 = mload v1 i256;\n" ++ ret1 "v4")) == "return [9]"
-- ... but not through storage, where it is a word (E3).
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        v2.i256 = ptr_to_int v1 i256;\n        evm_sstore 0.i256 v2;\n        v3.i256 = evm_sload 0.i256;\n        v4.*i256 = int_to_ptr v3 *i256;\n        mstore v4 9.i256 i256;\n        evm_stop;\n") == "ub"

-- Pointer arithmetic keeps the origin; a null test of a pointer into its block is false.
#guard outcome same (prog ("        v1.*i256 = alloca [i256; 2];\n        v2.i256 = ptr_to_int v1 i256;\n        v3.i256 = add v2 32.i256;\n        v4.*i256 = int_to_ptr v3 *i256;\n        mstore v4 5.i256 i256;\n        v5.i256 = sub v3 32.i256;\n        v6.i1 = is_zero v5;\n        v7.i256 = zext v6 i256;\n" ++ ret1 "v7")) == "return [0]"

-- Comparing pointers into different blocks depends on the address words (decision 2).
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        v2.*i256 = alloca i256;\n        v3.i1 = eq v1 v2;\n        v4.i256 = zext v3 i256;\n" ++ ret1 "v4")) == "return [0]"
#guard outcome same (prog ("        v1.*i256 = alloca i256;\n        v2.*i256 = alloca i256;\n        v3.i1 = eq v1 v2;\n        v4.i256 = zext v3 i256;\n" ++ ret1 "v4")) == "return [1]"

-- Blocks never overlap in H, whatever their words.
#guard outcome same (prog ("        v1.*i256 = alloca i256;\n        v2.*i256 = alloca i256;\n        mstore v1 1.i256 i256;\n        mstore v2 2.i256 i256;\n        v3.i256 = mload v1 i256;\n" ++ ret1 "v3")) == "return [1]"

-- Fresh bytes are the oracle's (R2).
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        v2.i256 = mload v1 i256;\n        v3.i256 = and v2 255.i256;\n" ++ ret1 "v3")) == "return [171]"

-- A narrow load of a word with upper bits set is `ub` (U2b).
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        mstore v1 2.i256 i256;\n        v2.i1 = mload v1 i1;\n        evm_stop;\n") == "ub"
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        mstore v1 1.i256 i256;\n        v2.i1 = mload v1 i1;\n        evm_stop;\n") == "return []"

-- `trunc_nuw` of a word with a dropped bit set is `ub` (U2c).
#guard outcome apart (prog "        v1.i1 = trunc_nuw 2.i256 i1;\n        evm_stop;\n") == "ub"

-- `evm_mload_bytes` reads at most 32 bytes (U5a), zero bytes without memory.
#guard outcome apart (prog "        v1.*i256 = alloca [i256; 2];\n        v2.i256 = evm_mload_bytes v1 33.i256;\n        evm_stop;\n") == "ub"
#guard outcome apart (prog ("        v2.i256 = evm_mload_bytes 0.i256 0.i256;\n" ++ ret1 "v2")) == "return [0]"
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        mstore v1 258.i256 i256;\n        v4.i256 = ptr_to_int v1 i256;\n        v5.i256 = add v4 30.i256;\n        v2.i256 = evm_mload_bytes v5 1.i256;\n" ++ ret1 "v2")) == "return [1]"

-- The heap budget: a request of `2 ^ 255` bytes exhausts it (§3.3).
#guard outcome apart (prog "        v1.*i256 = evm_malloc 57896044618658097711785492504343953926634992332820282019728792003956564819968.i256;\n        evm_stop;\n") == "exhausted"

-- `evm_return_code` returns code, touching no memory (E5); `unreachable` traps.
#guard outcome apart (prog "        evm_return_code 0.i256 2.i256;\n") == "return [0, 0]"
#guard outcome apart (prog "        unreachable;\n") == "trap"

-- A section entry that returns has no outcome.
#guard outcome apart (prog "        return;\n") == "returns"

-- `wfH` rejects what H does not define (§3.7).
def reasons (text : String) : List String := (wfReasons (obj text).runtime).map (·.1)

#guard reasons (prog "        evm_stop;\n") == []
#guard reasons (prog "        v1.i256 = evm_msize;\n        evm_stop;\n") == ["msize"]
#guard reasons (prog "        v1.i256 = udiv 1.i256 0.i256;\n        evm_stop;\n") == ["genericDiv"]
#guard reasons (prog "        v1.i256 = select 1.i1 1.i256 0.i256;\n        evm_stop;\n") == ["select"]
#guard reasons (prog "        return;\n") == ["entryReturns"]
#guard reasons (prog "        call %nowhere;\n        evm_stop;\n") == ["callSig"]
#guard reasons (prog "        br_table 0.i256 (0.i256 block0);\n") == ["cfg", "brTable"]

/-! ## Review 24 -/

-- `bitcast *T i256` keeps the origin, as `ptr_to_int` does (H1).
#guard outcome apart (prog ("        v1.*i256 = alloca i256;\n        v2.i256 = bitcast v1 i256;\n        v3.*i256 = int_to_ptr v2 *i256;\n        mstore v3 9.i256 i256;\n        v4.i256 = mload v1 i256;\n" ++ ret1 "v4")) == "return [9]"
#guard outcome same (prog ("        v1.*i256 = alloca i256;\n        v2.i256 = bitcast v1 i256;\n        v3.*i256 = int_to_ptr v2 *i256;\n        mstore v3 9.i256 i256;\n        v4.i256 = mload v1 i256;\n" ++ ret1 "v4")) == "return [9]"
-- `bitcast` to a narrow integer is on the word: no origin.
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        v2.i64 = bitcast v1 i64;\n        v3.i256 = zext v2 i256;\n        v4.*i256 = int_to_ptr v3 *i256;\n        mstore v4 9.i256 i256;\n        evm_stop;\n") == "ub"

-- Failures other than memory come first (M2): a read past the return data exits `oob`, a log,
-- a creation or a call moving value under a static call exits `static`, too much init code
-- diverges, all at an integer address that would be `ub`.
#guard outcome apart (prog "        evm_return_data_copy 0.i256 0.i256 1.i256;\n        evm_stop;\n") == "oob"
#guard outcome apart (prog "        v1.*i256 = alloca i256;\n        evm_return_data_copy v1 0.i256 0.i256;\n        evm_stop;\n") == "return []"
#guard outcomeOf false apart (obj (prog "        evm_log0 0.i256 32.i256;\n        evm_stop;\n")) == "static"
#guard outcomeOf true apart (obj (prog "        evm_log0 0.i256 32.i256;\n        evm_stop;\n")) == "ub"
#guard outcomeOf false apart (obj (prog "        v1.i256 = evm_create 0.i256 0.i256 32.i256;\n        evm_stop;\n")) == "static"
#guard outcome apart (prog "        v1.i256 = evm_create 0.i256 0.i256 49153.i256;\n        evm_stop;\n") == "diverge"
#guard outcome apart (prog "        v1.i256 = evm_create 0.i256 0.i256 49152.i256;\n        evm_stop;\n") == "ub"
#guard outcomeOf false apart (obj (prog "        v1.i256 = evm_call 0.i256 0.i256 1.i256 0.i256 32.i256 0.i256 0.i256;\n        evm_stop;\n")) == "static"
#guard outcomeOf false apart (obj (prog "        v1.i256 = evm_call 0.i256 0.i256 0.i256 0.i256 32.i256 0.i256 0.i256;\n        evm_stop;\n")) == "ub"

/-! Sections built directly, for what the reader does not produce. -/

def i256 : Ty := .int 256
def k (n : Nat) : Operand := .imm 256 n
def v (n : Nat) : Operand := .var n
def stop : HTerm := .base .evmStop
def func (name : String) (blocks : List HBlock) (params : List (Nat × Ty) := [])
    (rets : List Ty := []) : HFunc := ⟨name, params, rets, blocks⟩
def blk (id : Nat) (body : List HStmt) (term : HTerm) (phis : List Phi := []) : HBlock :=
  ⟨id, phis, body, term⟩
/-- A section of these functions and structs, entered at `main`. -/
def sec (funcs : List HFunc) (structs : List (String × List Ty) := [])
    (symbols : List (String × Nat × Nat) := [(".", 0, 0)]) : HSection :=
  ⟨⟨structs, funcs⟩, "main", symbols⟩
/-- A section whose `main` is one block. -/
def main1 (body : List HStmt) (term : HTerm := stop) : HSection := sec [func "main" [blk 0 body term]]
def rs (s : HSection) : List String := ((wfReasons s).map (·.1)).eraseDups
def run1 (body : List HStmt) (term : HTerm := stop) : String := outcomeOf true apart ⟨main1 body term, main1 body term⟩
def add1 : HStmt := ⟨[(1, i256)], .base (.bin .add (k 1) (k 2))⟩

#guard rs (main1 [add1]) == []
-- The entry has no parameters (it runs on none).
#guard rs (sec [func "main" [blk 0 [] stop] [(0, i256)]]) == ["entryParams"]
#guard (outcomeOf true apart (let s := sec [func "main" [blk 0 [] stop] [(0, i256)]]; ⟨s, s⟩)).startsWith "stuck"
#guard rs (sec [func "other" [blk 0 [] stop]]) == ["noEntry"]
-- Function and struct names are unique.
#guard rs (sec [func "main" [blk 0 [] stop], func "main" [blk 0 [] stop]]) == ["duplicateFunc"]
#guard rs (sec [func "main" [blk 0 [] stop], func "f" [blk 0 [] stop]]) == []
#guard rs (sec [func "main" [blk 0 [] stop]] [("s", [i256]), ("s", [.int 1])]) == ["duplicateStruct"]
#guard rs (sec [func "main" [blk 0 [] stop]] [("s", [i256]), ("t", [.int 1])]) == []
-- Symbols are in range, and exist.
#guard rs (sec [func "main" [blk 0 [] stop]] [] [(".", 2 ^ 256, 0)]) == ["symbolRange"]
#guard rs (sec [func "main" [blk 0 [] stop]] [] [(".", 0, 2 ^ 256)]) == ["symbolRange"]
#guard rs (sec [func "main" [blk 0 [] stop]] [] [(".", 2 ^ 256 - 1, 2 ^ 256 - 1)]) == []
#guard rs (main1 [⟨[(1, i256)], .base (.symAddr "nosuch")⟩]) == ["symbol"]
#guard rs (main1 [⟨[(1, i256)], .base (.symSize ".")⟩]) == []
-- Every value is defined once, and its definition dominates its uses.
#guard rs (main1 [add1, add1]) == ["duplicateDef"]
#guard rs (main1 [⟨[(2, i256)], .base (.bin .add (v 1) (k 1))⟩, add1]) == ["dominance"]
#guard rs (main1 [add1, ⟨[(2, i256)], .base (.bin .add (v 1) (k 1))⟩]) == []
#guard rs (sec [func "main" [blk 0 [] (.base (.br (.imm 1 1) 1 2)),
    blk 1 [add1] (.base (.jump 3)), blk 2 [] (.base (.jump 3)),
    blk 3 [⟨[(2, i256)], .base (.bin .add (v 1) (k 1))⟩] stop]]) == ["dominance"]
#guard rs (sec [func "main" [blk 0 [] (.base (.br (.imm 1 1) 1 2)),
    blk 1 [add1, ⟨[(2, i256)], .base (.bin .add (v 1) (k 1))⟩] (.base (.jump 3)),
    blk 2 [] (.base (.jump 3)), blk 3 [] stop]]) == []
-- A phi's operand is defined at the end of its predecessor.
#guard rs (sec [func "main" [blk 0 [] (.base (.jump 1)),
    blk 1 [add1] stop [⟨2, i256, [(v 1, 0)]⟩]]]) == ["dominance"]
#guard rs (sec [func "main" [blk 0 [add1] (.base (.jump 1)),
    blk 1 [] stop [⟨2, i256, [(v 1, 0)]⟩]]]) == []
-- Operands are declared, also in a block that never runs; immediates are of a width, in range.
#guard rs (main1 [⟨[(2, i256)], .base (.bin .add (v 9) (k 1))⟩]) == ["dominance", "undeclared"]
#guard rs (sec [func "main" [blk 0 [] stop, blk 1 [⟨[(2, i256)], .base (.bin .add (v 9) (k 1))⟩] stop]]) == ["undeclared"]
#guard rs (main1 [⟨[(1, .int 1)], .base (.cmp .eq (.imm 7 1) (.imm 7 1))⟩]) == ["imm"]
#guard rs (main1 [⟨[(1, .int 1)], .base (.cmp .eq (.imm 8 256) (.imm 8 1))⟩]) == ["imm"]
#guard rs (main1 [⟨[(1, .int 1)], .base (.cmp .eq (.imm 8 255) (.imm 8 1))⟩]) == []
#guard rs (main1 [] (.base (.evmRevert (.imm 256 (2 ^ 256)) (k 0)))) == ["imm"]
-- Operands taken at one width have it.
#guard rs (main1 [⟨[(1, i256)], .base (.bin .add (k 1) (.imm 8 1))⟩]) == ["operandType"]
#guard rs (main1 [⟨[(1, .int 1)], .base (.cmp .lt (k 1) (.imm 8 1))⟩]) == ["operandType"]
#guard rs (main1 [⟨[(1, i256), (2, .int 1)], .base (.ovf .uaddo (k 1) (.imm 8 1))⟩]) == ["operandType"]
#guard rs (main1 [⟨[(1, .int 8), (2, .int 1)], .base (.ovf .uaddo (.imm 8 1) (.imm 8 1))⟩]) == []
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca i256)⟩, ⟨[], .base (.mstore (v 1) (.imm 8 1) i256)⟩]) == ["operandType"]
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca i256)⟩, ⟨[], .base (.mstore (v 1) (.imm 8 1) (.int 8))⟩]) == []
-- A store of a value not of its type is stuck in H.
#guard (run1 [⟨[(1, .ptr i256)], .base (.alloca i256)⟩, ⟨[], .base (.mstore (v 1) (.imm 8 1) i256)⟩]).startsWith "stuck"
-- A statement binds the values its instruction gives, at their widths.
#guard rs (main1 [⟨[], .base (.bin .add (k 1) (k 2))⟩]) == ["results"]
#guard rs (main1 [⟨[(1, .int 8)], .base (.bin .add (k 1) (k 2))⟩]) == ["resultType"]
#guard rs (main1 [⟨[(1, i256)], .base (.cmp .eq (k 1) (k 2))⟩]) == ["resultType"]
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.bin .add (k 1) (k 2))⟩]) == []
#guard (run1 [⟨[(1, i256)], .base (.cmp .eq (k 1) (k 2))⟩]).startsWith "stuck"
-- A phi's operands have its width.
#guard rs (sec [func "main" [blk 0 [] (.base (.jump 1)), blk 1 [] stop [⟨2, .int 8, [(k 1, 0)]⟩]]]) == ["phiType"]
#guard rs (sec [func "main" [blk 0 [] (.base (.jump 1)), blk 1 [] stop [⟨2, .int 8, [(.imm 8 1, 0)]⟩]]]) == []
-- Calls, returns: arity and widths.
def callee : HFunc := func "f" [blk 0 [] (.base (.ret [v 0]))] [(0, i256)] [i256]
def caller (args : List Operand) (dsts : List (Nat × Ty)) : HSection :=
  sec [func "main" [blk 0 [⟨dsts, .base (.call "f" args)⟩] stop], callee]
#guard rs (caller [k 1] [(1, i256)]) == []
#guard rs (caller [.imm 8 1] [(1, i256)]) == ["callSig"]
#guard rs (caller [] [(1, i256)]) == ["callSig"]
#guard rs (caller [k 1] [(1, .int 8)]) == ["resultType"]
#guard rs (caller [k 1] []) == ["results"]
#guard rs (sec [func "main" [blk 0 [⟨[(1, i256)], .base (.call "f" [k 1])⟩] stop],
    func "f" [blk 0 [] (.base (.ret [.imm 8 1]))] [(0, i256)] [i256]]) == ["retType"]
#guard rs (sec [func "main" [blk 0 [⟨[(1, i256)], .base (.call "f" [k 1])⟩] stop],
    func "f" [blk 0 [] (.base (.ret []))] [(0, i256)] [i256]]) == ["ret"]
-- EVM operations have their exact number of operands, `evm_log` its topics (M1).
#guard rs (main1 [⟨[(1, i256)], .base (.evm .sload [])⟩]) == ["evmArity"]
#guard rs (main1 [⟨[], .base (.evm (.log 1) [k 0, k 0])⟩]) == ["evmArity"]
#guard rs (main1 [⟨[], .base (.evm (.log 5) [k 0, k 0, k 1, k 2, k 3, k 4, k 5])⟩]) == ["evmArity"]
#guard rs (main1 [⟨[], .base (.evm (.log 1) [k 0, k 0, k 7])⟩]) == []
#guard (run1 [⟨[], .base (.evm (.log 1) [k 0, k 0])⟩]).startsWith "stuck"
#guard run1 [⟨[], .base (.evm (.log 1) [k 0, k 0, k 7])⟩] == "return []"
#guard rs (main1 [⟨[], .base (.evm .sload [k 0])⟩]) == ["results"]
-- `evm_exp`, `evm_byte`, `evm_sign_extend` at `i256` only.
#guard rs (main1 [⟨[(1, .int 8)], .base (.bin .evmExp (.imm 8 2) (.imm 8 9))⟩]) == ["evmWidth"]
#guard (run1 [⟨[(1, .int 8)], .base (.bin .evmExp (.imm 8 2) (.imm 8 9))⟩]).startsWith "stuck"
#guard rs (main1 [⟨[(1, i256)], .base (.bin .evmExp (k 2) (k 9))⟩]) == []
-- Types of memory accesses and casts are value types; of `sat` and `trunc_nuw` integers (M1, L2).
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca i256)⟩, ⟨[], .base (.mstore (v 1) (.imm 256 1) (.int 7))⟩]) == ["memType"]
#guard rs (main1 [⟨[(1, i256)], .base (.cast .zext (.imm 1 1) .unit)⟩]) == ["castType"]
#guard rs (main1 [⟨[(1, i256)], .base (.cast .zext (.imm 1 1) i256)⟩]) == []
#guard rs (main1 [⟨[(1, i256)], .base (.sat .uadd (k 1) (k 2) .unit)⟩]) == ["satType"]
#guard rs (main1 [⟨[(1, i256)], .base (.sat .uadd (k 1) (k 2) (.ptr i256))⟩]) == ["satType"]
#guard (run1 [⟨[(1, i256)], .base (.sat .uadd (k 1) (k 2) .unit)⟩]).startsWith "stuck"
#guard rs (main1 [⟨[(1, i256)], .base (.sat .uadd (k 1) (k 2) (.int 8))⟩]) == []
#guard rs (main1 [⟨[(1, .ptr i256)], .truncNuw (k 1) (.ptr i256)⟩]) == ["truncNuw"]
#guard (run1 [⟨[(1, .ptr i256)], .truncNuw (k 1) (.ptr i256)⟩]).startsWith "stuck"
#guard rs (main1 [⟨[(1, .int 8)], .truncNuw (k 1) (.int 8)⟩]) == []
-- An `alloca` has a size some address word fits.
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca (.struct "nope"))⟩]) == ["allocaType"]
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca (.array i256 (2 ^ 251)))⟩]) == ["allocaSize"]
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca (.array i256 (2 ^ 250)))⟩]) == []
-- A `gep`'s base is declared at the type it carries.
#guard rs (main1 [⟨[(1, i256)], .base (.bin .add (k 1) (k 2))⟩,
    ⟨[(2, .ptr i256)], .gep (.ptr i256) (v 1) [k 0]⟩]) == ["gep"]
#guard rs (main1 [⟨[(1, .ptr i256)], .base (.alloca i256)⟩, ⟨[(2, .ptr i256)], .gep (.ptr i256) (v 1) [k 0]⟩]) == []
-- Values are of value types; no aggregates, no function pointers.
#guard rs (main1 [⟨[(1, .struct "s")], .base (.bin .add (k 1) (k 2))⟩]) == ["aggregateValue", "resultType"]
#guard rs (main1 [⟨[(1, i256)], .base (.funcPtr "main")⟩]) == ["funcPtr"]
#guard rs (main1 [⟨[(1, i256)], .base (.extractValue (k 0) (k 0))⟩]) == ["aggregate"]
#guard rs (sec [func "main" []]) == ["cfg"]
-- `select` evaluates both arms (L1), and stays rejected until #625; its arms have one width.
#guard (run1 [⟨[(1, i256)], .base (.select (.imm 1 1) (k 5) (v 9))⟩]).startsWith "stuck"
#guard rs (main1 [⟨[(1, i256)], .base (.select (.imm 1 1) (k 5) (k 6))⟩]) == ["select"]
#guard rs (main1 [⟨[(1, i256)], .base (.select (.imm 1 1) (k 5) (.imm 8 6))⟩]) == ["select", "operandType"]

end Fe.Sonatina.H.Tests
