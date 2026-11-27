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

/-- The outcome in a few words: the return data's first byte, or the kind of halt. -/
def outcome (o : Oracle) (text : String) : String :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with header.fork := .Osaka, perm := true }
  match runRuntime 100000 o (obj text) I
      (World.init ((∅ : AccountMap).insert I.codeOwner default) default) with
  | .halt (.ends (.error (.stop d _))) _ => s!"return {d.toList}"
  | .halt (.ends (.error (.revert d))) _ => s!"revert {d.toList}"
  | .halt (.ends (.error .trap)) _ => "trap"
  | .halt (.ends _) _ => "ends"
  | .halt .ub _ => "ub"
  | .halt .exhausted _ => "exhausted"
  | .stuck w => s!"stuck {w}"
  | .fuel => "fuel"
  | .badOracle w => s!"badOracle {w}"
  | .ok _ => "returns"

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

end Fe.Sonatina.H.Tests
