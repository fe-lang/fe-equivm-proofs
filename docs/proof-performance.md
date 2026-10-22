# Proof-checking performance

The changes address two costs: evaluating concrete Keccak hashes in Lean's kernel, and
checking the same closed selector fact for more than one contract. They preserve the
selector values, theorem statements, compiled bytecode, and EVM semantics.

## Reproducing the optimized build

Use the repository's Lean 4.29.0 toolchain and existing dependency pins:

```sh
lake exe cache get
python3 scripts/apply_fast_keccak.py
lake build
lake env lean .lake/packages/evmlean/Ethereum/SpongeHash/Keccak256Tests.lean
lake env lean scripts/KeccakAudit.lean
lake env lean scripts/Audit.lean
lake env lean scripts/Tactics.lean
```

The helper applies a checked source patch to the downloaded EVMLean checkout. It verifies
the exact pinned revision and resulting file hashes, refuses unrelated tracked edits, and
can be run again safely. Lake rebuilds the changed module and its dependents normally.
Deleting or replacing the dependency checkout requires applying the patch again. The
project also builds without the patch, with slower kernel evaluation.

The public dependency pins remain unchanged: a local dependency commit would not be
fetchable by another checkout. A future upstream dependency update can replace this patch
once EquiVM supports the newer EVMLean revision. Do not apply the patch to another revision.

## Keccak patch provenance and proof boundary

`patches/evmlean-fast-keccak.patch` takes exactly these files from
[EVMLean PR #5](https://github.com/lefterislazar/EVMLean/pull/5), at
[`c4935be9d7d91c260a74c2aeaa5245d44194969b`](https://github.com/lefterislazar/EVMLean/commit/c4935be9d7d91c260a74c2aeaa5245d44194969b):

- `Ethereum/SpongeHash/Keccak256.lean`
- `Ethereum/SpongeHash/Keccak256Tests.lean`

The base is the manifest's EVMLean revision `fd4f5e6d6d6b4a18eb73f5a71ae2df909ac2b542`.
EVMLean's Apache 2.0 license and notice accompany the patch in
`patches/EVMLean.LICENSE` and `patches/EVMLean.NOTICE`.

Updating directly to the PR head would also change unrelated dependency code, including
instruction decoding. The pinned EquiVM's `decode_append_left` proof explicitly uses the
old `ByteArray.extract'` implementation; the newer decoder uses `readWithPadding`. This
backport leaves both definitions and that proof unchanged.

The optimized hash represents lanes as natural numbers and uses structural recursion so
Lean's kernel can reduce concrete hashes efficiently. `hash_eq_referenceHash` proves
equality with the previous UInt64 implementation for every input, including arbitrary
lengths and padding boundaries. Its `csimp` attribute keeps compiled code using the
reference implementation. The theorem's axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

The test module checks known hashes in compiled evaluation, plus kernel-checked examples
for empty input, an ABI selector, 135-byte input where suffix and padding share a byte, and
136-byte input requiring another block. These examples supplement the all-input proof.

## Shared selector facts

`FeProofs/Common/Selectors.lean` proves the six ABI hashes shared by ERC20 and WETH9 once.
Contract-local theorems connect these facts to their existing table positions. This removes
six repeated kernel evaluations without introducing native evaluation or a proof cache.
The other five WETH9 signatures remain locally checked.

Selector facts import only Keccak. The execution-environment predicate `selIs` lives in
each contract's `Common.lean`, retaining its namespace and definition. Code that needs this
predicate should import the contract's common prelude. This keeps concrete hash checking
independent of the EVM semantics and Mathlib import closure.

## Measuring changes

After building imports, run:

```sh
python3 scripts/bench_modules.py --repeat 3 \
  FeProofs.Common.Selectors FeProofs.ERC20.Selectors FeProofs.WETH9.Selectors \
  > /path/outside/source-tree/selectors.json
```

Every sample starts a fresh Lean process and rechecks the requested source, reusing built
imports. The JSON records source and Keccak hashes, dependency manifest hash, toolchain,
thread setting, elapsed time, and Lean's profiler output. Include the shared module when
comparing total work. These are source-recheck timings, not clean-build timings; startup,
imports, concurrent jobs, and filesystem caching affect the elapsed result. Kernel profile
time helps distinguish hash evaluation from import and elaboration overhead.

For a before measurement, build a checkout of `ca1c853` with its original dependencies and
without the Keccak patch. This branch's harness can check that other checkout directly:

```sh
python3 scripts/bench_modules.py --root /path/to/baseline-checkout --repeat 3 \
  FeProofs.ERC20.Selectors FeProofs.WETH9.Selectors
```

An isolated paired check on official Lean 4.29.0 (`98dc76e`), using two Lean worker threads,
rechecked the same eleven original WETH9 hash propositions with only the Keccak import.
Only the imported Keccak implementation changed between each pair:

| Implementation | First elapsed check | Second elapsed check | Kernel checking |
| --- | ---: | ---: | ---: |
| Pinned UInt64 implementation | 149.63 s | 148.21 s | 143 s / 142 s |
| Proved Nat-lane backport | 13.36 s | 9.41 s | 1.05 s / 0.895 s |

Other builds were active on the machine. These measurements isolate the implementation
change; they do not include lemma sharing and do not predict the whole-project speedup.
In the optimized samples imports alone took 11.4 s and 7.99 s.

The module benchmark above, run twice per module with the same toolchain and thread setting,
gave these medians after integrating both the patch and shared facts:

| Source rechecked | Original | Optimized |
| --- | ---: | ---: |
| Shared token facts | Included in the two contract files | 12.13 s |
| `FeProofs.ERC20.Selectors` | 119.13 s | 12.03 s |
| `FeProofs.WETH9.Selectors` | 205.41 s | 9.77 s |
| Sum of module medians | 324.55 s | 33.93 s |

This is about a 9.6-fold reduction for this source-recheck workload, including the cost of
checking the shared facts. The optimized kernel checks took 424/482 ms for the shared facts,
3.93/3.00 ms for ERC20's references, and 261/290 ms for WETH9. Other builds were active during
both measurements, so elapsed times should be treated as local observations.

The whole-project baseline is incomplete (2101 s, 3528/3703 build jobs, no proof failures).
There is no whole-project before/after speedup claim or completed baseline capstone axiom
audit. All 17 selector theorem axiom reports were compared and match exactly:
`propext` and `Quot.sound`. The final Keccak vectors and equivalence/shared-fact audits pass,
and generated C confirms that `KEC` calls `referenceHash`.

## Validation

The integrated `lake build` passed all 3704 jobs on official Lean 4.29.0, including all nine
whole-contract correctness theorems. It took 3059.33 s with six Lean worker threads; this is
a validation run, not a paired whole-project performance measurement.

`scripts/Audit.lean` passed for all nine contract theorems. Each reports only `propext`,
`Quot.sound`, and `Classical.choice` outside the existing `native_decide` dependencies:

| Contract | `native_decide` dependencies |
| --- | ---: |
| Constant | 135 |
| Identity | 161 |
| ScalarStore | 305 |
| NarrowAbi | 518 |
| PackedStore | 422 |
| IndexedPackedStore | 541 |
| Deposit | 2247 |
| ERC20 | 1259 |
| WETH9 | 2800 |

These are final audit counts, not a comparison with a completed baseline capstone audit.
The changes add no native evaluation, axioms, admitted proofs, or unchecked termination.
`scripts/Tactics.lean` also passed, and `lake --no-build build` confirmed that all build
outputs were current.

## Scope

These changes check the existing pinned bytecode. They do not rebuild the Fe compiler or
compare new compiler output, and they make no claim about compiler performance.
