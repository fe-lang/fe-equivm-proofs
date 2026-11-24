# Schema library for the M1 checker: notes

Design: `fe-correctness-scratch/provable-pipeline/m1/design.md` §4.13 (schemas), §3.3 (known
and demanded bits), §9 ruling 8 (fact-check direction), §10 rows H-7, C-2, L-2, with
`reviews/review-1-m1-design.md` (finding H-7). Rust: `sonatina/provable-part-a` at `664cd128`.

Everything is in namespace `Fe.Sonatina.Steps.Schemas`. Nothing outside these files is changed.
`lake build Fe.Sonatina.Steps.SchemasTests` builds all of it (the tests import every module).

**Checker entry points** (after review 9, `SchemasCheck.lean`): `checkExact`, `checkDemand`,
`checkBranchOn`, each with a soundness lemma under `FactsOn` (facts of the atoms of the terms
compared only). The per-schema lemmas below (`checkI_sound` …) keep the global `FactsHold` and
are what the entry points are proved from.

## Modules

| Module | Contents |
| --- | --- |
| `SchemasWord.lean` | `W = 2^256`, `M = W - 1`; `Op1`/`Op2`/`Op3` (the 26 pure machine-IR ops) and `.eval` on words; `Op2.eval_eq_bin`, `Op2.eval_eq_cmp`, `Op1.eval_*`, `addMod_toNat`, `mulMod_toNat`, `exp_toNat`, `byteAt_toNat`, `signextend_toNat`, `sar_eq`; `PureInst`, `pureInst?`, `ArgsAre`, `runInst_pure`, `runInst_clz`, `Val.as_word` |
| `EvalConst.lean` | `Op`, `evalConst`, `evalConst_sound`, `evalConst_clz` |
| `KnownBits.lean` | `KB` (`kz`, `ko`), `KB.Sat`, `KB.valid`, `KB.le`, `KB.meet`, `KB.exact`, `KB.exactVal?`; `transfer1/2/3` and `transfer1/2/3_sound`, `meet_sound`, `KB.Sat.le` |
| `SchemasTerm.lean` | `Term` (`atom`/`lit`/`op1`/`op2`/`op3`), `Term.eval`, `Term.fact`, `Term.fact_sat`, `FactsHold`, `Term.const?`, `isC`, `Term.constEval`, `Term.fold`, `pow2Shift?` |
| `SchemasI.lean` | identities I1–I21 (no I6): `schemaAdd` … `schemaNotNot`, `checkI`, `checkI_sound` |
| `SchemasS.lean` | `scalar_canonicalize` S1–S15: `foldBitwisePair`, `canonByte`, `canonSignextend`, `foldConstCmp`, `eqZero`, `mulPow2`, `mergeShifts`, `mergeDivs`, `divPow2`, `checkS`, `checkS_sound` |
| `SchemasG.lean` | GVN G2–G6 (`subAdd`, `addSub`, `checkG`, `checkG_sound`); branches B1–B3 (`truthy`, `peelIsZero`, `checkBranch`, `checkBranch_sound`, `checkBranch_target`) |
| `KnownBitsDemand.lean` | `Agree`, `Agree.mono`; `demand1/2/3` and `demand1/2/3_sound` |
| `SchemasD.lean` | D1–D3: `checkD`, `checkD_sound` |
| `SchemasCheck.lean` | `Op2.comm`, `Term.norm`, `Term.norm_eval`, `Term.commEq`, `Term.nf`, `Term.hasAtom`, `Term.hasClz`; `FactsOn`, `restrict`, `factsHold_restrict`, `envWord`, `factsOn_env`, `eval_atom_env`; `checkExact`, `checkDemand`, `checkBranchOn` and their soundness |
| `SchemasTests.lean` | `decide +kernel` tests, the H-7 counterexamples as rejected cases, `#print axioms` |

## Axioms

Every lemma printed in `SchemasTests.lean` (`evalConst_sound`, `runInst_clz`, `transfer2_sound`,
`checkI_sound`, `checkS_sound`, `checkG_sound`, `checkBranch_sound`, `demand2_sound`,
`checkD_sound`, `Term.fold_eval`) depends on `propext`, `Classical.choice`, `Quot.sound` only. No
`sorry`, no `native_decide`, no `bv_decide`. The tests use `decide +kernel` (kernel reduction,
no extra axiom).

## Item 1: word semantics and the bridge

Words are `Nat` below `W`. The word functions reduce in the kernel: `evm_exp` is a 256-step
square-and-multiply (`expLoop`), not `UInt256.pow`, whose `powAux` is well-founded; the
others are `Nat` arithmetic and bitwise operations (`Nat.log2` for `clz`).

The equalities with `Interp.lean`, for operands below `W`:
- `Op2.eval_eq_bin`: `BinOp.eval op 256 x y = o.eval x y` for the 16 non-comparisons (`add sub
  mul evm_udiv evm_sdiv evm_umod evm_smod evm_exp shl shr sar and or xor evm_byte
  evm_signextend`);
- `Op2.eval_eq_cmp`: `ofBool (CmpOp.eval op 256 x y) = o.eval x y` for `lt gt slt sgt eq`;
- `Op1.eval_not`, `Op1.eval_isZero`, `Op1.eval_clz` (definitional), `Op1.eval_clz_evm` (agrees
  with EVMLean's `UInt256.clz`); `addMod_toNat`, `mulMod_toNat` for `EvmOp.run .addMod/.mulMod`.

`runInst_pure`: for `p : PureInst` other than `clz`, with `ArgsAre env p.args xs` (each operand
evaluates to `.int 256 x` with `x < W`), `runInst c env p.toInst = pure [.int p.bits
(p.evalOn xs)]`. `p.bits` is 1 for comparisons and `is_zero` (the interpreter's `bool`), 256
otherwise; `Val.as_word` turns either into the bound `.int 256 _` (`bind` applies `Val.as` at the
declared `i256`). `pureInst? i = some p → p.toInst = i` (`pureInst?_toInst`). `runInst_clz`: `clz`
gives the word on Osaka and `.error .trap` on every other fork.

Corners, all as the interpreter computes them and checked in the tests: shift amounts ≥ 256
(`shl`/`shr` 0, `sar` all sign bits); `evm_udiv/umod/sdiv/smod` by 0 give 0; `sdiv MIN (-1) =
MIN`; `smod` takes the dividend's sign; `signextend b x = x` for `b ≥ 31`; `byte i x = 0` for
`i ≥ 32`; `addmod`/`mulmod` do not wrap the sum/product and give 0 for modulus 0; `clz 0 = 256`;
comparisons and `is_zero` give the words 0/1.

**Where the interpreter's pure instructions are partial** (`stuck`, a run that does not
terminate), from `Interp.lean`:
- every operand: `.var id` unbound in `env`; an aggregate where an integer is read (`evalInt`);
- `bin`, `cmp`: the two operands of different widths (`evalPair`);
- `is_zero`, `not`, `clz`: no width check (any integer);
- `evm_add_mod`, `evm_mul_mod`: an argument list of the wrong length (`EvmOp.run`'s last arm); the
  operands go through `evalWord` (`UInt256.ofNat`, reduced modulo `W`, no width check);
- `clz` is not stuck but traps before Osaka.

Not partial but beyond the word lemmas: an immediate `.imm 256 v` with `v ≥ W` is used as is, and
an operand of another width is computed at that width; `wf` (review C-6) must exclude both.
`Term.eval` reduces literals and atoms modulo `W`, so terms agree with the interpreter exactly
when `wf` holds.

**Machine-IR operations not covered**: `evm_uaddsat`, `evm_saddsat`, `evm_usubsat`,
`evm_ssubsat`, `evm_umulsat`, `evm_smulsat`, `get_function_ptr`, `black_box` (absent from
`Syntax.lean`/`Parse.lean`, so the Lean side rejects them; `fold_evm_saturating` is out of
scope), and `evm_keccak256` (reads memory). The non-EVM `udiv`/`sdiv`/`umod`/`smod`, `neg`,
`ctz`, casts, `ovf`, `select`, `le`/`ge`/`sle`/`sge`/`ne` are not machine IR.

## Item 2: `evalConst`

`evalConst : Op → List Nat → Option Nat`, `none` on wrong arity or an argument ≥ `W`.
`evalConst_sound`: `pureInst? i = some p`, `p` not `clz`, `ArgsAre env p.args xs`,
`evalConst p.op xs = some r` give `runInst c env i = pure [.int p.bits r]`. `clz` folds only on
Osaka (`evalConst_clz`); a checker must not accept a `clz` fold, or a term with `clz`, for an
earlier fork (review H-2). `Term.constEval` and `Term.fold` (sound for every environment:
`constEval_eval`, `fold_eval`) do "constant-fold both" of design §4.2.

## Item 4: known bits

`KB.Sat f x := x &&& f.kz = 0 ∧ x &&& f.ko = f.ko`. The fact type carries no proof of
`kz &&& ko = 0`; `KB.valid` checks it (and both masks `< W`) for exported facts. No soundness
lemma needs it.

The fact check (design §3.3 with ruling 8): a claimed fact `c` for an instruction result passes
if `KB.le c (transferN o (facts of the operands))`, and for a phi if `KB.le c` the `KB.meet` of
all incoming facts. `KB.Sat.le` gives the claim from the derived fact. Immediates' facts are
`KB.exact w`; missing facts `KB.unknown`.

The transfers follow `known_bits.rs` at `i256`: `and`/`or`/`xor`/`not` exactly; `is_zero`
(`exact_bool` / `bool_shape`); `clz` (only the low 9 bits); `shl`/`shr`/`sar` by a constant (≥ 256
included); `evm_byte` (8 bits); `evm_signextend` by a constant (`b ≥ 32` and `b = 31` give the
value's fact); the five comparisons (exact on exact operands, `eq` false on conflicting facts,
else `bool_shape`); everything else unknown (`add`, `sub`, `mul`, the divisions, `exp`,
`addmod`, `mulmod`). **One deliberate difference**: where the Rust needs the shift amount,
byte, or comparison operand to be an *immediate*, the Lean transfer takes it whenever the
operand's fact is exact. On every input the Lean fact contains the Rust one, so every fact the
Rust exports passes; none is weaker.

## Item 5: demanded bits

`Agree m x y := x &&& m = y &&& m`. `demand1 o d`, `demand2 o imm d` (a pair: first operand,
second operand), `demand3 o d` follow `demanded_bits.rs`: a zero demand (after masking to 256
bits) propagates nothing; `and`/`or`/`xor` pass `d`; `not` passes `d`; `is_zero`, `clz`, the
comparisons, `add` … `exp`, `byte` and non-constant shifts demand everything; constant `shl`,
`shr`, `sar` (sign bit for fill) and `signextend` (sign bit for the high part, nothing on the
byte operand) as in the Rust. `imm` is the first operand's word when it is an immediate (the
Rust's `constant_shift`), else `none`. `evm_add_mod`/`evm_mul_mod` are `Opaque` in Sonatina,
hence external uses: `demand3` is all bits always. Soundness `demand2_sound`: if `imm = some n`
then both first operands are `n`; operands agreeing on the demands give results agreeing on
`d`. Check direction: a claimed operand demand `D(o)` passes if it contains the computed one,
`B &&& D(o) = B`; `Agree.mono` turns agreement on `D(o)` into agreement on `B`. The external-use
seeding (branches, opaque, `mstore8` value `0xff`, its address full; review L-2) is the
checker's.

## Item 3: the schemas

Input form: `l r : Term` (the unfolded `T_in`, `T_out`), `kb : Nat → KB` the facts of atoms
(value ids), `KB.unknown` where there is none. Every check's soundness lemma:
`FactsHold kb ρ → check kb l r = true → l.eval ρ = r.eval ρ` (`checkD`: `Agree d`), where
`FactsHold kb ρ := ∀ v, (kb v).Sat (ρ v % W)`. `factsHold_unknown` gives it for no facts.

**"Known to be a constant"** (`isC kb t n`): `t`'s fact (literals exact, transfers above
the atoms' facts) fixes it to `n`. The Rust asks `known_imm` (an immediate, or SCCP's constant in
`sccp_fold`); `isC` accepts every such case and more. Value-id equality (`lhs == rhs`) is term
equality; GVN's congruence is the checker's representative substitution.

Final side conditions (`c`, `k`, `n` are constants per `isC`/`const?`):

| # | Check | Rust | Condition |
| --- | --- | --- | --- |
| I1 | `schemaAdd` | `simplify_binary_with_facts` Add | `add 0 x`, `add x 0 → x` |
| I2 | `schemaSub` | Sub | `sub x x → 0`; `sub x 0 → x` |
| I3 | `schemaMul` | Mul | `mul 0 _`, `mul _ 0 → 0`; `mul 1 x`, `mul x 1 → x` |
| I4, I5 | `schemaAnd` | And, `simplify_and_copy_with_facts` | `and 0 _`/`_ 0 → 0`; `and M x`/`x M → x`; `and x x → x`; `and x m`, `and m x → x` if `kz(x) ⊇ M ^^^ m` |
| I7, I8 | `schemaOr` | Or, `simplify_or_copy_with_facts` | `or M _`/`_ M → M`; `or 0 x`/`x 0 → x`; `or x x → x`; `or x m`, `or m x → x` if `ko(x) ⊇ m` |
| I9 | `schemaXor` | Xor | `xor 0 x`/`x 0 → x`; `xor x x → 0` |
| I10, I11 | `schemaDiv` | Udiv … EvmSmod | `evm_udiv`/`evm_sdiv x 1 → x`; `evm_umod`/`evm_smod x 1 → 0` |
| I12 | `schemaEq` | Eq | `eq x x → 1`; `eq x y → 0` on conflicting facts |
| I13 | `schemaCmp` | Gt/Lt/Slt/Sgt | `lt`/`gt`/`slt`/`sgt x x → 0`; `gt 0 x → 0`; `lt x 0 → 0` |
| I14, I15 | `schemaShift` | Shl/Shr/Sar, `undo_inverse_shift` | value 0 `→ 0`; amount 0 `→` value; `shl`/`shr` by ≥ 256 `→ 0`; `shr c (shl c x) → x` if `c < 256` and the top `c` bits of `x` known zero; `shl c (shr c x) → x` if `c < 256` and the low `c` bits known zero |
| I16, I17 | `schemaEvm` | `simplify_evm_signextend_known`, `…_copy_with_facts` | `signextend _ 0 → 0`; `signextend b x → x` if `b ≥ 31`, or sign bit `8b+7` and all bits above known all zero or all one |
| I18 | `schemaEvm` | `simplify_evm_exp_known` | `exp _ 0 → 1`; `exp 1 _ → 1`; `exp 0 e → 0` if `e` constant ≠ 0 |
| I19 | `schemaEvm` | `simplify_evm_byte_known` | `byte _ 0 → 0` |
| I20 | `schemaNotNot` | `simplify_unary_with_same_inner` | `not (not x) → x` |
| I21 | `schemaModop` | `simplify_evm_modop_known` | `addmod _ _ 0`, `mulmod _ _ 0 → 0` (H-7) |
| S1 | `foldBitwisePair` | `fold_bitwise_pair` | `o (a x y) (b u v) → h x y` (output operands either order), `{u,v} = {x,y}`, `(o,a,b) ↦ h` in the Rust table (16 ordered entries) |
| S2 | `canonByte` | `canonicalize_evm_byte` | `shr 248 x → evm_byte 0 x` |
| S3 | `canonByte` | same | `and (shr c x) 255`, `and 255 (shr c x) → evm_byte (31 - c/8) x`, `0 < c ≤ 248`, `c % 8 = 0` |
| S4 | `canonSignextend` | `canonicalize_evm_signextend` | `sar c (shl c x) → evm_signextend (31 - c/8) x`, same `c` |
| S5–S8 | `foldConstCmp` | `fold_constant_comparison` | `eq (o p q) k` and `eq k (o p q)`, `o ∈ {add, sub, xor}`: constant `q` → `eq p k'` with `k' = k - q`, `k + q`, `k ^ q`; constant `p` → `eq q k'` with `k' = k - p`, `p - k`, `k ^ p` (mod `W`); `is_zero (o p q)` as `k = 0` |
| S9 (G4) | `eqZero` | `canonicalize_binary_inst` Eq, GVN | `eq x 0`, `eq 0 x → is_zero x` |
| S11 (G6) | `mulPow2` | `mul_pow2_rewrite`, GVN | `mul (2^k) x`, `mul x (2^k) → shl k x`, `1 ≤ k < 256` |
| S12 | `mergeShifts` | `merge_shifts` | `o a (o b x) → o t x`, `o ∈ {shl, shr, sar}`, `t = min (min a 256 + min b 256) L`, `L = 256` (255 for `sar`) |
| S13 | `mergeDivs` | `merge_unsigned_divisions` | `evm_udiv (evm_udiv x a) b → evm_udiv x (a·b)`, `a, b ≠ 0`, neither a nontrivial power of two, `a·b < W` |
| S14, S15 | `divPow2` | `canonicalize_binary_inst` | `evm_udiv x (2^k) → shr k x`; `evm_umod x (2^k) → and x (2^k-1)` (mask either side); `1 ≤ k < 256` |
| G2 | `subAdd` | `simplify_sub_add_cancellation` | `sub (add a b) b → a`, `sub (add a b) a → b` |
| G3 | `addSub` | `simplify_add_sub_cancellation` | `add (sub a b) b`, `add b (sub a b) → a` |
| B1–B3 | `checkBranch kb c c' swap` | `branch_canonicalize`, `branch_conditions` | `c = is_zero^k c₀`; `c' = c₀` with `swap = odd k`, or `c' = is_zero x` with `c₀ ∈ {eq x 0, eq 0 x}` and `swap = odd k`, or `c₀ ∈ {gt x 0, lt 0 x}` and `swap = even k` |
| D1 | `checkD kb d` | `simplify_binary_with_demanded_bits` | `and a b`, `and b a → a` if `d &&& (M ^^^ ko(b)) = 0` |
| D2, D3 | `checkD kb d` | same | `or`/`xor a b`, `b a → a` if `d &&& (M ^^^ kz(b)) = 0` |

`checkBranch_sound`: `truthy (c'.eval ρ) = (truthy (c.eval ρ) ^^ swap)`; `checkBranch_target`: the
branch on `c` to `nz`, `z` goes where the branch on `c'` goes to `z`, `nz` if `swap`
(`branchTarget w nz z := if w != 0 then nz else z`, as `runBlocks`).

**Differences from design §4.13**:
- I5, I8 in both operand orders (the Rust tries both); I10/I11 for the EVM forms only (machine
  IR); I21 added (H-7); I6 not done (range facts).
- S3, S4: `0 < c ≤ 248`, `c % 8 = 0` (H-7; `c = 0` is the Rust's own exclusion); S11, S14, S15:
  `1 ≤ k < 256` (`nontrivial_pow2_shift`); S13: also the Rust's "neither divisor a nontrivial
  power of two" (not needed for soundness, kept); S5–S8 for both bound sides, both constant
  sides, and `is_zero` (H-7); S12 exactly the Rust's clamp.
- The structural heuristics of `scalar_canonicalize` (single use, same block, materialization
  cost) are not checked: they do not affect soundness. Deletions are the checker's.
- G4 and G6 are the same checks as S9 and S11. G5 (`neg`) is not machine IR. G7 (phi with equal
  incoming values) is not a word schema and is not here.
- B: per review M-3 (design §4.4 had the `is_zero` direction backwards).
- D1–D3 both operand orders (H-7).

## Rust findings

**No unsound rewrite or transfer function found** in the machine-IR scope: every schema above is
proved as the Rust applies it (with the side conditions the Rust has), every transfer function as
the Rust computes it (Lean's at least as precise), every backward demand function as the Rust
computes it.

**Compiler panic (not a miscompile)**: `fold_evm_signextend_raw` (`simplify_expr.rs:355-368`)
computes `(U256::one() << (sign_bit + 1)) - U256::one()` for a value whose sign bit is clear.
For `byte = 31`, `sign_bit + 1 = 256`; `primitive-types 0.14.0` (uint 0.10) gives `1 << 256 = 0`
and `0 - 1` panics with "arithmetic operation overflow" in every build profile (checked with a
standalone program against the pinned crate). Input: `evm_signextend 31.i256 5.i256` (both
operands constants, `5` nonzero with bit 255 clear) reaching any pass that calls
`simplify_evm_signextend_known` with both constants (SCCP folding, GVN, `known_bits_simplify`,
`simplify_binary_with_facts`). The other signextend paths (`…_copy_with_facts`, the known-bits
and demanded-bits functions) test `sign_width >= width` first and are fine. Fix: return `value`
for `byte >= 31`.

Known, not new: Sonatina folds and deletes `clz` on every fork; Lean traps before Osaka (review
M-5, H-2).

## Review 9 (`reviews/review-9-lean-schemas.md`)

- **Finding 3 (GVN), confirmed.** GVN keys `eq x 0` as `IsZero(x)` and `mul x 2^k` as
  `Shl(k, x)` (`gvn.rs:1000-1068`, `make_gvn_unary_key`/`make_gvn_binary_key`), and
  `RedundantCodeRemover` aliases the later instruction of a class to the dominating one
  (`gvn.rs:2409-2420`); `perform_symbolic_evaluation` sorts the operands of commutative ops by
  rank (`gvn.rs:935-937`, `is_commutative_binary`: `add mul and or xor eq` on machine IR).
  `checkG` now takes G4 and G6 both ways. `Term.norm` sorts commutative operands (and reduces
  literals); `checkExact` runs every schema on the terms and on their folded normal forms
  (`Term.nf`), so every term equality inside a schema is commutative equality, and
  `l.nf == r.nf` accepts a commuted copy.
- **Finding 4 (`scalar_canonicalize` compositions): single-round checks suffice, no normalizer.**
  `ScalarCanonicalize::run` (`scalar_canonicalize.rs:64-104`): each round first plans every
  instruction on the unmutated function (`plan_inst` takes `&Function`; one `Option<RewritePlan>`
  per instruction, so at most one rewrite per instruction per round), then applies the plans.
  On machine IR every plan is a `ReplaceInst` (the `Copy` plans come from `zext` and casts),
  `resolved` is empty, and `apply_replace_plan` builds the planned `InstSpec` without reading the
  function. So a round's rewrite reads only pre-round definitions. A rewrite may name, as an
  operand, a value whose own instruction is rewritten in the same round (it keeps its value id
  and its value); the checker must then treat that value id as an atom on both sides (it is
  justified by its own check), not unfold it through its new definition. Design §4.2 E3 says
  "atoms are output operands present in the input with the same definition": with that rule
  such a step would need a composition. `fold_constant_comparison` always emits `eq x k`
  (`InstSpec::Binary { kind: Eq, … }`, also from `is_zero`), never `is_zero x`; the `eq x 0 →
  is_zero x` is the next round's S9. So the one-round case the reviewer names does not arise.
- **Finding 5 (`FactsHold`), confirmed; localized (option a).** `FactsOn kb ρ ts` asks the facts
  of the atoms of `ts` only. `factsOn_env`: from `hinv : ∀ v x, env[v]? = some (.int 256 x) →
  (kb v).Sat x` and every atom bound to an `i256` word, `FactsOn kb (envWord env) ts`.
- **Finding 6 (`checkBranch`), confirmed.** `checkBranch = checkBranch1 || checkBranch2`;
  `checkBranch2` peels `is_zero` from both conditions (`swap = odd (k + k')` for equal cores,
  `odd (k + k') ^^ !s` through `zeroCmp`). The M-3 cases (`checkBranch1`) stay as tests.
- **Finding 8.** Done: `foldConstCmp` accepts its output's operands in either order; `Term.hasClz`;
  docstring `KB.Sat.le`. Not changed: `Term.fold` does not read `kb` (give SCCP constants as
  `lit`s; `isC` reads facts anyway); `KB.exact v` assumes `v < W` (every caller passes a word);
  I6 is live on machine IR when `known_bits_simplify` runs range analysis
  (`known_bits_simplify.rs:104-117`), so steps using it are rejected until range facts exist.
- **Findings 1, 2, 7 (Rust)** are handled elsewhere. Finding 1 (GVN edge predicates peel `not`
  on `i256`) is outside this library: edge predicates (G8/G9) are not schemas here. Finding 2
  adds a second copy of the signextend panic in `crates/ir/src/interpret/evm/mod.rs:120-131`.

Rust behaviour none of these checks accepts (seen while verifying): GVN's operand replacement
through edge predicates (`infer_value_at_block`), value phis and class leaders other than by
term equality (G7–G10, the checker's); I6 (range); `scalar_canonicalize` steps where an operand's
definition changed in the same round, if the checker unfolds it (above).

## For the checker authors

- Import `Fe.Sonatina.Steps.SchemasG` and `Fe.Sonatina.Steps.SchemasD` (they import the rest),
  `open Fe.Sonatina.Steps.Schemas`.
- Build `Term`s with `atom v` for value `v`, `lit w` for an immediate (or `undef`, as 0); map an
  instruction with `pureInst?`. Supply `kb v` = the verified known-bits fact of `v` (or
  `KB.unknown`); prove `FactsOn kb (envWord env) [l, r]` with `factsOn_env` from the known-bits
  invariant and the atoms being bound.
- Call `checkExact kb l r` (F, commutative equality, `checkI`, `checkS`, `checkG`; exact mode),
  or `checkDemand kb d l r` (D1–D3; demanded-bits mode only, review C-2), or
  `checkBranchOn kb c c' swap`. Soundness needs `FactsOn kb ρ [l, r]` only (`factsOn_env`).
- Relate terms to the interpreter with `runInst_pure` / `evalConst_sound`; for a term with
  `clz`, Osaka only.
- Every check is `Bool` and reduces in the kernel (no well-founded recursion); the tests run
  each by `decide +kernel` in a few seconds in total.
