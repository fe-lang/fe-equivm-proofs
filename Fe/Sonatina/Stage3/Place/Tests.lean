import Fe.Sonatina.Stage3.Place.Fixture

/-!
# Tests of the S14 check

Real sections of corpus v6 (`-O0`), with placement records synthesized from their lowered
machine IR (`place/synth.py`, untrusted; the compiler's record does not exist yet), checked in
the kernel; and small hand-written sections, accepted, with a rejected mutant for each rule and
for each attack of design §5.5 that applies without free-pointer restores (attacks 10, 16–19,
21, 27 for S8, S5 and S1; 3, 8, 22 for S3; 7 and the call footprint for S7; 9 for S6).  The
small ones run by `#guard`.
-/

namespace Fe.Sonatina.Stage3.Place.Tests

open Fe.Sonatina Fe.Sonatina.H Fe.Sonatina.Stage3.Place

/-! ## Real sections -/

place_fixture feConstantRt "Fe/Sonatina/Stage3/Place/Tests/FeConstant.O0.sidecar.json" "runtime"
  "Fe/Sonatina/Stage3/Place/Tests/FeConstant.runtime.place.json"
place_fixture feErc20Rt "Fe/Sonatina/Stage3/Place/Tests/FeERC20.O0.sidecar.json" "runtime"
  "Fe/Sonatina/Stage3/Place/Tests/FeERC20.runtime.place.json"
place_fixture feErc20Init "Fe/Sonatina/Stage3/Place/Tests/FeERC20.O0.sidecar.json" "init"
  "Fe/Sonatina/Stage3/Place/Tests/FeERC20.init.place.json"

example : check feConstantRt.src feConstantRt.low feConstantRt.efp feConstantRt.rec = true := by
  decide +kernel
example : check feErc20Rt.src feErc20Rt.low feErc20Rt.efp feErc20Rt.rec = true := by
  decide +kernel
example : check feErc20Init.src feErc20Init.low feErc20Init.efp feErc20Init.rec = true := by
  decide +kernel

/-- A wrong word for one `alloca` of FeConstant's runtime is a rejection. -/
def feConstantBadWord : Record :=
  { feConstantRt.rec with funcs := feConstantRt.rec.funcs.map fun fr =>
      { fr with allocas := fr.allocas.map fun (x, l) => (x, .scratch (l.word + 1)) } }

#guard (diagnose feConstantRt.src feConstantRt.low feConstantRt.efp feConstantBadWord).isSome

/-! ## Small sections -/

/-- The first rule `diagnose` names for the section `src` (entry `%main`) lowered to `mach`. -/
def run (src mach : String) (r : Record) (efp : Option Nat := none) : Option String :=
  match H.Parse.parseModule src, Fe.Sonatina.Parse.parseModule mach with
  | .ok hm, .ok mm =>
    let s : HSection := ⟨hm, "main", [(".", 0, 0)]⟩
    diagnose s mm efp (r.withHints s mm)
  | .error e, _ => some s!"source: {e}"
  | _, .error e => some s!"machine: {e}"

/-- `run` with the section's symbols. -/
def runSyms (syms : List (String × Nat × Nat)) (src mach : String) (r : Record)
    (efp : Option Nat := none) : Option String :=
  match H.Parse.parseModule src, Fe.Sonatina.Parse.parseModule mach with
  | .ok hm, .ok mm =>
    let s : HSection := ⟨hm, "main", syms⟩
    diagnose s mm efp (r.withHints s mm)
  | .error e, _ => some s!"source: {e}"
  | _, .error e => some s!"machine: {e}"

/-- The rule a rejection names: the part of its reason before the colon. -/
def rule (d : Option String) : String :=
  match d with
  | some s => (s.splitOn ":").headD s
  | none => "accepted"

def fr (name : String) (allocas : List (Nat × Loc) := []) (mallocs : List (Nat × Malloc) := [])
    : FuncRec := { name, allocas, mallocs }

def rec1 (arena : Nat) (fs : List FuncRec) : Record := { arenaBase := arena, funcs := fs }

/-- An `alloca`, a store, a load, and a return of the cell. -/
def s1 : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        mstore v1 7.i256 i256;
        v2.i256 = mload v1 i256;
        evm_return v1 32.i256;
}
"
def m1 : String := "
func public %main() {
    block0:
        evm_mstore 160.i256 7.i256;
        v0.i256 = evm_mload 160.i256;
        evm_return 160.i256 32.i256;
}
"
def r1 : Record := rec1 160 [fr "main" [(1, .scratch 0)]]

#guard rule (run s1 m1 r1) == "accepted"
-- The machine stores at another word than the record's.
#guard rule (run s1 (m1.replace "evm_mstore 160" "evm_mstore 192") r1) == "translation"
-- No location for the `alloca`.
#guard rule (run s1 m1 (rec1 160 [fr "main"])) == "S2"
-- The machine loads from another address.
#guard rule (run s1 (m1.replace "evm_mload 160" "evm_mload 192") r1) == "translation"
-- The machine returns a different length.
#guard rule (run s1 (m1.replace "evm_return 160.i256 32" "evm_return 160.i256 64") r1) == "translation"

/-! ### S1, S2, S4, S5 -/

/-- A heap malloc of 64 bytes, a store into it, and a return of it. -/
def s2 : String := "
func public %main() {
    block0:
        v1.*i256 = evm_malloc 64.i256;
        mstore v1 7.i256 i256;
        evm_return v1 32.i256;
}
"
def m2 : String := "
func public %main() {
    block0:
        v0.i256 = evm_mload 64.i256;
        v1.i256 = add v0 64.i256;
        evm_mstore 64.i256 v1;
        evm_mstore v0 7.i256;
        evm_return v0 32.i256;
}
"
def r2 : Record := rec1 160 [fr "main" [] [(1, .heap 128 none true)]]

#guard rule (run s2 m2 r2 (some 128)) == "accepted"
-- Attack 27: a heap site without an entry free pointer (its block would be at 0, under the
-- free-pointer slot).
#guard rule (run s2 m2 (rec1 160 [fr "main" [] [(1, .heap 0 none true)]])) == "S1"
#guard rule (run s2 m2 r2 (some 0x40)) == "S1"
-- Attack 21: an entry free pointer of 2^40.
#guard rule (run s2 m2 r2 (some (2 ^ 40))) == "S5"
-- A free-pointer restore; a transient and an exact-base heap malloc (the stage-1 switch); a
-- fixed malloc that is not terminal.
#guard rule (run s2 m2 { r2 with funcs := [{ fr "main" [] [(1, .heap 128 none true)] with restoresFp := true }] } (some 128)) == "S2"
#guard rule (run s2 m2 (rec1 160 [fr "main" [] [(1, .heap 128 none false)]]) (some 128)) == "stage 1"
#guard rule (run s2 m2 (rec1 160 [fr "main" [] [(1, .heap 128 (some 128) true)]]) (some 128)) == "stage 1"
#guard rule (run s2 m2 (rec1 160 [fr "main" [] [(1, .fixed 128 .program)]]) (some 128)) == "S2"
-- The machine does not bump the free pointer.
#guard rule (run s2 (m2.replace "evm_mstore 64.i256 v1;" "") r2 (some 128)) == "translation"
-- The bump is by the wrong size.
#guard rule (run s2 (m2.replace "add v0 64" "add v0 32") r2 (some 128)) == "translation"
-- A dynamic frame.
#guard rule (run s1 m1 { r1 with funcs := [{ fr "main" [(1, .scratch 0)] with dynFrame := true }] }) == "S1"

/-- S1 and S4 with an `alloca` and a heap site: the `alloca` meets the free-pointer slot, or
    lies above the heap floor. -/
def s3 : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        v2.*i256 = evm_malloc 32.i256;
        mstore v1 7.i256 i256;
        evm_return v2 32.i256;
}
"
def m3 (a : Nat) : String := s!"
func public %main() \{
    block0:
        v0.i256 = evm_mload 64.i256;
        v1.i256 = add v0 32.i256;
        evm_mstore 64.i256 v1;
        evm_mstore {a}.i256 7.i256;
        evm_return v0 32.i256;
}
"
#guard rule (run s3 (m3 160) (rec1 160 [fr "main" [(1, .scratch 0)] [(2, .heap 256 none true)]]) (some 256)) == "accepted"
#guard rule (run s3 (m3 64) (rec1 64 [fr "main" [(1, .scratch 0)] [(2, .heap 256 none true)]]) (some 256)) == "S1"
#guard rule (run s3 (m3 512) (rec1 160 [fr "main" [(1, .scratch 11)] [(2, .heap 256 none true)]]) (some 256)) == "S4"

/-! ### S3 -/

-- Attacks 3 and 22: an `alloca`'s address stored as data.
def s4 : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        v2.i256 = ptr_to_int v1 i256;
        mstore v1 v2 i256;
        evm_return v1 32.i256;
}
"
def m4 : String := "
func public %main() {
    block0:
        evm_mstore 160.i256 160.i256;
        evm_return 160.i256 32.i256;
}
"
#guard rule (run s4 m4 r1) == "S3"

-- Attack 8: an `alloca`'s address returned (through a parameter that carries it).
def s5 : String := "
func private %f(v0.*i256) -> *i256 {
    block0:
        return v0;
}

func public %main() {
    block0:
        v1.*i256 = alloca i256;
        v2.*i256 = call %f v1;
        v3.i256 = mload v2 i256;
        evm_return v1 32.i256;
}
"
def m5 : String := "
func private %f(v0.i256) -> i256 {
    block0:
        return v0;
}

func public %main() {
    block0:
        v0.i256 = call %f 160.i256;
        v1.i256 = evm_mload v0;
        evm_return 160.i256 32.i256;
}
"
#guard rule (run s5 m5 (rec1 160 [fr "f", fr "main" [(1, .scratch 0)]])) == "S3"

/-! ### S7 -/

-- Attack 7: a loop's phi keeps the previous iteration's `alloca` while it runs again.
def s6 : String := "
func public %main() {
    block0:
        v9.*i256 = alloca i256;
        jump block1;

    block1:
        v1.*i256 = phi (v9 block0) (v2 block1);
        v2.*i256 = alloca i256;
        mstore v2 1.i256 i256;
        mstore v1 2.i256 i256;
        v3.i256 = evm_calldata_size;
        br v3 block1 block2;

    block2:
        evm_stop;
}
"
def m6 : String := "
func public %main() {
    block0:
        jump block1;

    block1:
        v0.i256 = phi (192.i256 block0) (160.i256 block1);
        evm_mstore 160.i256 1.i256;
        evm_mstore v0 2.i256;
        v1.i256 = evm_calldata_size;
        br v1 block1 block2;

    block2:
        evm_stop;
}
"
#guard rule (run s6 m6 (rec1 160 [fr "main" [(9, .scratch 1), (2, .scratch 0)]])) == "S7"

-- An `alloca` live across a call whose callee's frame is at the same word.
def s7 : String := "
func private %f() {
    block0:
        v1.*i256 = alloca i256;
        mstore v1 5.i256 i256;
        return;
}

func public %main() {
    block0:
        v1.*i256 = alloca i256;
        mstore v1 7.i256 i256;
        call %f;
        evm_return v1 32.i256;
}
"
def m7 (a : Nat) : String := s!"
func private %f() \{
    block0:
        evm_mstore 160.i256 5.i256;
        return;
}

func public %main() \{
    block0:
        evm_mstore {a}.i256 7.i256;
        call %f;
        evm_return {a}.i256 32.i256;
}
"
#guard rule (run s7 (m7 160) (rec1 160 [fr "f" [(1, .scratch 0)], fr "main" [(1, .scratch 0)]])) == "S7"
#guard rule (run s7 (m7 192) (rec1 160 [fr "f" [(1, .scratch 0)], fr "main" [(1, .stable 1)]])) == "accepted"

/-! ### S6 -/

-- Attack 9: a terminal buffer's suffix reads memory.
def s8 (extra : String) : String := s!"
func public %main() \{
    block0:
        v1.*i256 = evm_malloc 64.i256;
        mstore v1 7.i256 i256;
{extra}        evm_revert v1 32.i256;
}
"
def m8 (extra : String) : String := s!"
func public %main() \{
    block0:
        evm_mstore 512.i256 7.i256;
{extra}        evm_revert 512.i256 32.i256;
}
"
def r8 : Record := rec1 160 [fr "main" [] [(1, .fixed 512 .terminal)]]
#guard rule (run (s8 "") (m8 "") r8) == "accepted"
#guard rule (run (s8 "        v2.i256 = mload v1 i256;\n") (m8 "        v0.i256 = evm_mload 512.i256;\n") r8) == "S6"
#guard rule (run (s8 "        v2.i256 = evm_calldata_size;\n        evm_sstore 0.i256 v2;\n")
  (m8 "        v0.i256 = evm_calldata_size;\n        evm_sstore 0.i256 v0;\n") r8) == "S6"

/-! ### S8 (an `alloca` at address 0) -/

def s9 (uses : String) : String := s!"
func public %main() \{
    block0:
        v1.*i256 = alloca i256;
        v2.i256 = ptr_to_int v1 i256;
{uses}        evm_stop;
}
"
def m9 (uses : String) : String := s!"
func public %main() \{
    block0:
{uses}        evm_stop;
}
"
def r9 : Record := rec1 0 [fr "main" [(1, .scratch 0)]]
-- Only as an address: accepted.
#guard rule (run (s9 "        mstore v1 1.i256 i256;\n") (m9 "        evm_mstore 0.i256 1.i256;\n") r9) == "accepted"
-- Attack 10: a null test of the address.
#guard rule (run (s9 "        v3.i1 = is_zero v2;\n") (m9 "        v0.i256 = is_zero 0.i256;\n") r9) == "S8"
-- Attack 16: `sub 0 p`.
#guard rule (run (s9 "        v3.i256 = sub 0.i256 v2;\n") (m9 "        v0.i256 = sub 0.i256 0.i256;\n") r9) == "S8"
-- Attack 17: `add p p`.
#guard rule (run (s9 "        v3.i256 = add v2 v2;\n") (m9 "        v0.i256 = add 0.i256 0.i256;\n") r9) == "S8"
-- Attack 18: the address as the value of a store (S3 rejects it first).
#guard rule (run (s9 "        mstore v1 v2 i256;\n") (m9 "        evm_mstore 0.i256 0.i256;\n") r9) == "S3"
-- Attack 18 through `evm_mstore8`, which S3 allows: S8 rejects it.
#guard rule (run (s9 "        evm_mstore8 v1 v2;\n") (m9 "        evm_mstore8 0.i256 0.i256;\n") r9) == "S8"
-- Attack 19: a narrow `ptr_to_int`.
#guard rule (run (s9 "        v3.i1 = ptr_to_int v1 i1;\n") (m9 "        v0.i256 = and 0.i256 1.i256;\n") r9) == "S8"
-- The same null test with the `alloca` off 0 is no observation that matters: accepted.
#guard rule (run (s9 "        v3.i1 = is_zero v2;\n") (m9 "        v0.i256 = is_zero 160.i256;\n")
  (rec1 160 [fr "main" [(1, .scratch 0)]])) == "accepted"

/-! ### Translation and typing -/

-- An `i1` addition: H wraps at width 1, the machine at 256.
def s10 (op : String) : String := s!"
func public %main() \{
    block0:
        v1.i256 = evm_calldata_size;
        v2.i1 = is_zero v1;
        v3.i1 = {op} v2 v2;
        br v3 block1 block2;

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
def m10 (op : String) : String := s!"
func public %main() \{
    block0:
        v0.i256 = evm_calldata_size;
        v1.i256 = is_zero v0;
        v2.i256 = {op} v1 v1;
        br v2 block1 block2;

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
#guard rule (run (s10 "xor") (m10 "xor") (rec1 0 [])) == "accepted"
#guard rule (run (s10 "add") (m10 "add") (rec1 0 [])) == "translation"
-- A machine branch to the other block.
#guard rule (run (s10 "xor") ((m10 "xor").replace "br v2 block1 block2" "br v2 block2 block1") (rec1 0 [])) == "translation"
-- `ne` is lowered as `is_zero (eq …)`.
def s11 : String := "
func public %main() {
    block0:
        v1.i256 = evm_calldata_size;
        v2.i1 = ne v1 4.i256;
        br v2 block1 block2;

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
def m11 : String := "
func public %main() {
    block0:
        v0.i256 = evm_calldata_size;
        v1.i256 = eq v0 4.i256;
        v2.i256 = is_zero v1;
        br v2 block1 block2;

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
#guard rule (run s11 m11 (rec1 0 [])) == "accepted"
#guard rule (run s11 (m11.replace "is_zero v1" "is_zero v0") (rec1 0 [])) == "translation"
-- A default-less `br_table` (a miss on a word has no rule in H).
def s12 (dflt : String) : String := s!"
func public %main() \{
    block0:
        v1.i256 = evm_calldata_size;
        br_table v1 {dflt}(0.i256 block1) (1.i256 block2);

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
def m12 : String := "
func public %main() {
    block0:
        v0.i256 = evm_calldata_size;
        br_table v0 block2 (0.i256 block1);

    block1:
        evm_stop;

    block2:
        evm_invalid;
}
"
#guard rule (run (s12 "") m12 (rec1 0 [])) == "translation"

/-! ## Review 25: unsound acceptances of the first checker

Each was accepted by the checker before the fix (checked once) and is rejected now. -/

-- C1: `sub p p` is an integer in H, and `add` of it and another block's pointer points there:
-- neither is a pointer into the terminal buffer.  M returns 99, H 42.
def c1s : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        mstore v1 42.i256 i256;
        v2.*i256 = evm_malloc 32.i256;
        mstore v2 99.i256 i256;
        v3.i256 = sub v2 v2;
        v4.i256 = ptr_to_int v1 i256;
        v5.i256 = add v3 v4;
        evm_return v5 32.i256;
}
"
def c1m : String := "
func public %main() {
    block0:
        evm_mstore 160.i256 42.i256;
        evm_mstore 160.i256 99.i256;
        v0.i256 = sub 160.i256 160.i256;
        v1.i256 = add v0 160.i256;
        evm_return v1 32.i256;
}
"
#guard rule (run c1s c1m (rec1 160 [fr "main" [(1, .scratch 0)] [(2, .fixed 160 .terminal)]])) == "S6"

-- C2: a machine value defined twice: the heap malloc's new free pointer in its base's id.
def c2s : String := "
func public %main() {
    block0:
        v1.*i256 = evm_malloc 32.i256;
        v2.*i256 = evm_malloc 32.i256;
        mstore v1 42.i256 i256;
        mstore v2 99.i256 i256;
        v3.i256 = mload v1 i256;
        mstore v1 v3 i256;
        evm_return v1 32.i256;
}
"
def c2m : String := "
func public %main() {
    block0:
        v10.i256 = evm_mload 64.i256;
        v10.i256 = add v10 32.i256;
        evm_mstore 64.i256 v10;
        v11.i256 = evm_mload 64.i256;
        v12.i256 = add v11 32.i256;
        evm_mstore 64.i256 v12;
        evm_mstore v10 42.i256;
        evm_mstore v11 99.i256;
        v13.i256 = evm_mload v10;
        evm_mstore v10 v13;
        evm_return v10 32.i256;
}
"
#guard rule (run c2s c2m (rec1 160 [fr "main" [] [(1, .heap 160 none true), (2, .heap 160 none true)]])
  (some 160)) == "translation"
-- C2: two machine parameters of one id.
def c2ps : String := "
func private %f(v1.i256, v2.i256) -> i256 {
    block0:
        return v1;
}

func public %main() {
    block0:
        v1.i256 = call %f 42.i256 99.i256;
        v2.*i256 = alloca i256;
        mstore v2 v1 i256;
        evm_return v2 32.i256;
}
"
def c2pm : String := "
func private %f(v0.i256, v0.i256) -> i256 {
    block0:
        return v0;
}

func public %main() {
    block0:
        v0.i256 = call %f 42.i256 99.i256;
        evm_mstore 160.i256 v0;
        evm_return 160.i256 32.i256;
}
"
#guard rule (run c2ps c2pm (rec1 160 [fr "f", fr "main" [(2, .scratch 0)]])) == "translation"

-- C4: a source value defined twice: the second `alloca v1`, of no bytes, hides the first's range
-- from S7.
def c4s : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        v2.*i256 = bitcast v1 *i256;
        v1.*[i256;0] = alloca [i256;0];
        v3.*i256 = alloca i256;
        mstore v2 42.i256 i256;
        mstore v3 99.i256 i256;
        v4.i256 = mload v2 i256;
        v5.*i256 = alloca i256;
        mstore v5 v4 i256;
        evm_return v5 32.i256;
}
"
def c4m : String := "
func public %main() {
    block0:
        evm_mstore 160.i256 42.i256;
        evm_mstore 160.i256 99.i256;
        v0.i256 = evm_mload 160.i256;
        evm_mstore 192.i256 v0;
        evm_return 192.i256 32.i256;
}
"
#guard rule (run c4s c4m (rec1 160 [fr "main" [(1, .scratch 0), (3, .scratch 0), (5, .scratch 1)]])) == "translation"

-- C5a: two source blocks of one id: the checks read the second, H runs the first.
def c5as : String := "
func public %main() {
    block0:
        v1.*i256 = alloca i256;
        v5.*i256 = alloca i256;
        mstore v1 42.i256 i256;
        jump block1;

    block1:
        v10.*i256 = bitcast v1 *i256;
        v11.*i256 = bitcast v1 *i256;
        v12.*i256 = bitcast v1 *i256;
        v13.*i256 = bitcast v1 *i256;
        v3.*i256 = alloca i256;
        mstore v3 99.i256 i256;
        v4.i256 = mload v1 i256;
        mstore v5 v4 i256;
        evm_return v5 32.i256;

    block1:
        mstore v1 99.i256 i256;
        v6.i256 = mload v1 i256;
        mstore v5 v6 i256;
        evm_return v5 32.i256;
}
"
def c5am : String := "
func public %main() {
    block0:
        evm_mstore 160.i256 42.i256;
        jump block1;

    block1:
        evm_mstore 160.i256 99.i256;
        v0.i256 = evm_mload 160.i256;
        evm_mstore 192.i256 v0;
        evm_return 192.i256 32.i256;
}
"
#guard rule (run c5as c5am (rec1 160 [{ fr "main" [(1, .scratch 0), (3, .scratch 0), (5, .scratch 1)] with
  blockMap := some [(0, 0), (1, 1)] }])) == "translation"

-- C5b: two source blocks mapped to one machine block: the machine takes a phi's operand from it
-- on an edge H's phi has none for.
def c5bs : String := "
func public %main() {
    block0:
        v1.i256 = evm_calldata_size;
        br v1 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v2.i256 = phi (42.i256 block1);
        v3.*i256 = alloca i256;
        mstore v3 v2 i256;
        evm_return v3 32.i256;
}
"
def c5bm : String := "
func public %main() {
    block0:
        v0.i256 = evm_calldata_size;
        br v0 block1 block1;

    block1:
        jump block2;

    block2:
        v1.i256 = phi (42.i256 block1);
        evm_mstore 160.i256 v1;
        evm_return 160.i256 32.i256;
}
"
#guard rule (run c5bs c5bm (rec1 160 [{ fr "main" [(3, .scratch 0)] with
  blockMap := some [(0, 0), (1, 1), (2, 1), (3, 2)] }])) == "translation"

-- H1: a symbol offset of `2 ^ 256`: H is stuck binding it, the machine wraps it to 0.
def h1s : String := "
func public %main() {
    block0:
        v1.i256 = sym_addr &big;
        v2.*i256 = alloca i256;
        mstore v2 v1 i256;
        evm_return v2 32.i256;
}
"
def h1m : String := "
func public %main() {
    block0:
        v0.i256 = sym_addr &big;
        evm_mstore 160.i256 v0;
        evm_return 160.i256 32.i256;
}
"
#guard rule (runSyms [("&big", 2 ^ 256, 0)] h1s h1m (rec1 160 [fr "main" [(2, .scratch 0)]])) == "translation"
#guard rule (runSyms [("&big", 2 ^ 255, 0)] h1s h1m (rec1 160 [fr "main" [(2, .scratch 0)]])) == "accepted"

-- H2: `int_to_ptr` to an integer type reads the address word (1 in H, 0 in the machine).
#guard rule (run (s9 "        v3.i1 = int_to_ptr v1 i1;\n") (m9 "        v0.i256 = and 0.i256 1.i256;\n") r9) == "S8"

-- M1: a clamp diamond whose two arms are one block: the machine's phi always takes the first
-- operand.
def m1s : String := "
func public %main() {
    block0:
        v1.*i256 = evm_malloc 32.i256;
        mstore v1 7.i256 i256;
        evm_return v1 32.i256;
}
"
def m1m : String := "
func public %main() {
    block0:
        v0.i256 = evm_mload 64.i256;
        v1.i256 = gt v0 255.i256;
        br v1 block1 block1;

    block1:
        jump block2;

    block2:
        v2.i256 = phi (v0 block1) (256.i256 block1);
        v3.i256 = add v2 32.i256;
        evm_mstore 64.i256 v3;
        evm_mstore v2 7.i256;
        evm_return v2 32.i256;
}
"
#guard rule (run m1s m1m (rec1 160 [fr "main" [] [(1, .heap 256 none true)]]) (some 128)) == "translation"

-- M2: a `br_table` case on the terminal buffer's address.
def m2s : String := "
func public %main() {
    block0:
        v1.*i256 = evm_malloc 64.i256;
        mstore v1 7.i256 i256;
        v2.i256 = ptr_to_int v1 i256;
        br_table 5.i256 block1 (v2 block2);

    block1:
        evm_revert v1 32.i256;

    block2:
        evm_revert v1 32.i256;
}
"
def m2m : String := "
func public %main() {
    block0:
        evm_mstore 512.i256 7.i256;
        br_table 5.i256 block1 (512.i256 block2);

    block1:
        evm_revert 512.i256 32.i256;

    block2:
        evm_revert 512.i256 32.i256;
}
"
#guard rule (run m2s m2m r8) == "S6"

-- L1: two placements for one `alloca`.
#guard rule (run s1 m1 (rec1 160 [fr "main" [(1, .scratch 0), (1, .scratch 1)]])) == "S2"

end Fe.Sonatina.Stage3.Place.Tests
