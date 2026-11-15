# Fe EquiVM proofs

Machine-checked refinement proofs, in Lean 4 with
[EquiVM](https://github.com/argotorg/EquiVM), that EVM bytecode produced by the
[Fe](https://github.com/argotorg/fe) compiler behaves exactly like a high-level
specification written in EquiVM's specification language, Stele.

## Contracts

Compiled with the Sonatina backend, `-O 1`, Osaka: FeDeposit and WETH9 with Fe 26.6.0
(`aa5244d43`), the others with Fe 26.5.0 (`22b156fff`).

| Module | Contract | Theorem |
| --- | --- | --- |
| `FeProofs.Constant` | `answer() -> u256` returning 42 | `feConstantContractCorrect` |
| `FeProofs.Identity` | `identity(uint256)` | `feIdentityContractCorrect` |
| `FeProofs.NarrowAbi` | `uint8`/`int8`/`bool`/`address` echoes | `feNarrowAbiContractCorrect` |
| `FeProofs.ScalarStore` | one `u256` field with a `uint256` constructor | `feScalarStoreContractCorrect` |
| `FeProofs.PackedStore` | `StoragePackedArray<8>` lanes 0 and 1 | `fePackedStoreContractCorrect` |
| `FeProofs.IndexedPackedStore` | runtime-indexed `StoragePackedArray<8>`, `index < 64` | `feIndexedPackedStoreContractCorrect` |
| `FeProofs.Deposit` | [Fe deposit contract](https://github.com/argotorg/fe/blob/e4372c0d7/crates/fe/tests/fixtures/fe_test/deposit_contract.fe) | `feDepositContractCorrect` (calldata below 2^64 bytes) |
| `FeProofs.WETH9` | [canonical WETH9](https://github.com/gnosis/canonical-weth/blob/master/contracts/WETH9.sol) written in Fe | `feWETH9ContractCorrect` (string getters under a string-size precondition) |

Each theorem covers the constructor and the whole runtime: for every input, the deployed
bytecode returns the same data, reverts in the same cases and leaves the same accounts as the
contract's Stele specification (`SpecSyntax.lean`), unless it runs out of gas. EquiVM's refinement
relation does not compare event logs or revert payloads.

### The deposit contract

`feDepositContractCorrect` covers every entry point (`deposit`, `get_deposit_root`,
`get_deposit_count`, `supportsInterface`). What it assumes and does not claim:

- The specification mirrors the Fe source, statement by statement. The theorem
  does not compare the Fe contract with the Solidity mainnet contract, and does
  not prove properties of the Merkle tree itself, such as root correctness.
- Calldata is shorter than 2^64 bytes (`calldataBelow2pow64`). Fe's ABI decoder
  relies on its backend's calldata-size bound here; real transactions cannot
  come close.
- SHA-256 is specified as the bytecode's `STATICCALL` to precompile 2, so the
  theorem holds relative to whatever that precompile returns.
- The specification keeps the incremented deposit count in a local
  (`size = deposit_count + 1; deposit_count = size`), as the bytecode does,
  instead of reading the count back from storage.
- The proof is about the exact bytecode in `FeProofs/Deposit/creation.hex` and
  `runtime.hex`. A compiler change that alters that bytecode needs the affected
  proof steps redone.

### WETH9

`FeProofs/WETH9` is an ingot (`fe.toml`, `src/`): canonical WETH9 written in Fe, with WETH9's storage
layout (`name` and `symbol` as Solidity strings in slots 0 and 1, `decimals` in slot 2,
`balanceOf` and `allowance` in slots 3 and 4) and unchecked arithmetic, as in Solidity 0.5.
`src/sol_string.fe` has `SolString`, a storage field type with Solidity's string layout. Its
specification is EquiVM's WETH9 specification statement for statement; only the configuration
differs from EquiVM's solc proof:

- Strings use Solidity 0.8's storage semantics: a length header whose short/long flag contradicts
  the length reverts, where solc 0.5.16 reads any header.
- Calldata is decoded strictly: a non-canonical `address` argument reverts, where solc 0.5.16
  masks it.

`feWETH9ContractCorrect` covers the constructor (for any initial storage), all eleven entry points,
including `withdraw`'s value transfer to a caller that may re-enter, and the payable fallback. The
runtime theorem assumes `feWETH9StorageWF`: on a `name()` or `symbol()` call, the stored string's ABI
encoding is shorter than 2^64 bytes. Fe reverts above that size while the specification returns the
string. Only the constructor writes those slots, so a deployed contract satisfies it.

## Exported models

The Stele certificates above compare bytecode with a specification written by hand. A second
set of certificates compares it with a Lean model of the contract that the Fe compiler prints
(`fe-lean-export`, Fe branch `lean-export`, at the commit `fe.pin` names): each `init` and
`recv` arm, the entry code that decodes calldata and encodes results, and the core and std
functions those reach, as definitions in a monad over EVMLean's state.

`Refines p bytecode model` (`Fe/EVM/Refine.lean`) says that on every message call the bytecode
runs out of gas or of stack, or does what the model does, as far as profile `p` observes.
Profile `P0` compares the outcome, return data and accounts, as EquiVM's relation does; `P1`
adds event logs and revert payloads. `RefinesDeploy` is the same for the creation bytecode.
Both speak only of frames whose account, `I.codeOwner`, exists (`OwnerExists`), as in every frame
the EVM runs. Without the account EVMLean's `SSTORE` drops the write, so a load after a store
reads 0, while the compiler forwards a stored value to a later load of the same slot.

An exported contract's model is `{ init := deploy init_entry, runtime := entry runtime }`: the
deployment and runtime entries the exporter prints, each run after reserving low memory
(`reserve`), as the compiled entry code does when it stores the free pointer at `0x40`. The model
allocates at the end of memory (`alloc`), so without the reservation a call's first allocation
would be at address 0, which core's `try_alloc_bytes` reads as a failed allocation; the bytecode's
heap starts above it.

| Module | Hand-written model | Exported model |
| --- | --- | --- |
| `FeProofs.Constant` | `feConstantRefinesModel` | |
| `FeProofs.ScalarStore` | `feScalarStoreRefinesModel` | `feScalarStoreRefinesExported` |
| `FeProofs.CodeScalar` (one immutable `u256` field) | `feCodeScalarRefinesModel` | `feCodeScalarRefinesExported` |
| `FeProofs.PackedStore` | `fePackedStoreRefinesHandEntry` (exported arms, entry by hand) | `fePackedStoreRefinesExported` |
| `FeProofs.ERC20` (EquiVM's `ERC20` example token written in Fe) | `feERC20RefinesModel` (from `feERC20RefinesExportedP1`) | `feERC20RefinesExportedP1` (`P1` only) |
| `FeProofs.WETH9` | `feWETH9RefinesModel` | `feWETH9RefinesExported` |

Each has a `…Deploy…` twin for the constructor. All are at `P0`, but FeERC20's exported one.
FeScalarStore and FeERC20 have certificates of the exported model at `P1`, through the Sonatina
checker (`Fe/Sonatina/README.md`): `feScalarStoreRefinesExportedP1` and `feERC20RefinesExportedP1`,
each with its `…Deploy…` twin. FeERC20's are of the bytecode the pinned Fe commit compiles
(`FeProofs/ERC20/runtime.hex`, `FeERC20.build.json`), and its certificates of the hand-written model
are derived from them (`ModelCorrect.lean`): each exported entry ends as the model's does, so the
runtime one holds on calldata shorter than 2^64 bytes (`CalldataFits`), not on all calldata
(`Refines`) as the others' do. WETH9 has them too,
`feWETH9RefinesExportedP1` and `feWETH9DeployRefinesExportedP1` (`FeProofs/WETH9/Sonatina*.lean`),
of the same bytes as its `P0` ones and with no `native_decide`: its machine IR has loops with
bounds read from storage (the copy of a long string in `%load`, the zeroing of an old one's data
words in the constructor's `%store`), run by induction on the iterations left
(`runBlocks_loop`, `Fe/Sonatina/Run.lean`). The certificates of exported
models assume calldata shorter than 2^64 bytes (`CalldataFits`), as Fe's std does.
`call_conserves` and `deploy_conserves` (`FeProofs/ERC20/ConservationBytecode.lean`) are
properties of the ERC20 bytecode proved through the exported certificates: every successful call
keeps the balances of a list of holders equal to the supply, and a successful deployment makes
them so, in a frame whose account exists, under conditions on the holders (`Covers`, `CollisionFree`). They hold of any bytecode
with `P0` certificates of the exported model (`call_keeps`, `deploy_keeps`), here through
`RefinesOn.toP0` and `RefinesDeploy.toP0`.

### Invariants through reentrant calls

A certificate is about one message call. `Fe/EVM/Invariant.lean` proves, over EVMLean alone, what
turns it into a statement about the contract among others (`good`): every message call and
creation, at every depth, keeps an invariant on the account at an address, if each successful
frame that runs the contract's code there keeps it whenever the calls and creations below that
frame do. Code elsewhere changes the account only by calling it or by sending it value. The
conditions: the invariant tolerates any increase of the balance that does not wrap, the account
has code, and a `DELEGATECALL` from it runs only code the hypothesis covers. An invariant that
holds only for some calls is stated relative to admission: the conclusion is about executions in
which every successful frame at the address is admitted (`Admitted`). Which calls of a frame at the
address admission reaches is a parameter (`callsAt`): the bytecode's own calls (`XiOk`), a
description by the model (the calls it records, `ContractModel.callsAt`), or none. A frame at
the address knows how it was entered: from an account map where the invariant holds, by moving a
value, under an entry condition that is also a parameter (`Enters`). The condition must hold of
every entry from another account that moves the value it reports, which is what the walk checks
of code elsewhere and what the transaction's outermost call does; a frame at the address must
show it of its own calls to the address.

`Fe/EVM/RefineInvariant.lean` derives the per-frame hypothesis from a certificate and a property
of the model (`refinesOn_keeps`), and the base case from a deployment certificate
(`refinesDeploy_holds`). The pure layer also covers the transaction around the outermost call
(`tx_holds`): the sender has no code (EIP-3607, which EVMLean checks outside `Υ`), the outermost
call is admitted, and the invariant tolerates clearing transient storage. The account is never
erased as self-destructed: the same walk proves that no call or creation lists it among the
accounts the transaction created, which `SELFDESTRUCT` requires.

For the ERC20 token (`FeProofs/ERC20/Invariant.lean`): `deploy_conserves_token`, a successful
deployment by a holder that has an account makes the holders' balances add up to the supply at the new address (its
storage starts empty, as `Lambda` guarantees); `every_call_conserves` and
`every_transaction_conserves`, every message call, creation and transaction keeps that, where
every successful frame at the token has calldata shorter than 2^64 bytes and is covered by the
holders.
`feConstantKeepsStorage` is an instance without a condition. An invariant may bound the
balance from below: no balance increase wraps, because every call and transaction keeps the sum of
all balances from growing, given that it is below 2^256 where the transaction starts and the
transaction is valid (the sender can pay for gas, blobs and value).

WETH9's `withdraw` sends value to the caller, who may re-enter. The model takes what it cannot
compute, the callee's gas and the substate and original account map it is handed, from the feed:
`call_feed` (`Fe/EVM/Reach.lean`) shows that a `CALL` in a trace is the model's `call` for some
entry of the feed, and whatever the callee does, to WETH9's storage as well, is in EVMLean's `Θ`
on both sides. The model records each call and creation it makes, as the inputs it passes to `Θ`
or `Lambda` (the ghost field `World.calls`), so a statement about the model can say which calls
it makes. Unlike the Stele certificate, neither WETH9 certificate assumes anything of
storage: a `name()` or `symbol()` whose ABI encoding takes 2^64 bytes or more panics with
`Panic(0x41)` in both the bytecode and the model.

For WETH9 (`FeProofs/WETH9/Invariant.lean`, stated on the exported model and its certificates,
proved through the hand-written model and its solvency in `Solvency.lean`): the ether the
contract holds covers the tokens at every set of distinct balance slots (`Solvent`).
`feWETH9KeepsSolvent` and `feWETH9TxKeepsSolvent`: every message call, creation and transaction
keeps that, re-entry through `withdraw` included, where every successful frame at WETH9 has
calldata shorter than 2^64 bytes and writes no allowance slot that is a balance slot
(`Admission`), and the balances of all accounts add up to less than 2^256. Admission speaks of
the calls the exported model makes under every feed, since EquiVM's traces do not record the
bytecode's path; the model's one call is `withdraw`'s, to the caller. The two models end alike
with the same recorded calls (`EndsAs` and `Alike` relate the records). `feWETH9DeploySolvent`: a successful deployment by an account that exists establishes it, if no
balance slot is the slot of `name`, `symbol` or `decimals`. `Lambda` adds the new account before
it runs the init code only when the creator has an account, which every creator the EVM runs has,
so the deployment statements assume it.

The files of an exported contract:

- `Exported.lean`: the exporter's output between marker lines, and nothing else: the
  definitions, then a check by `rfl` of each constant the compiler folded, that its definition
  evaluates to the value printed in its place.
- `<name>.trust`: the exporter's trust ledger, one line per place, in the contract (`own`),
  `core` or `std`: what Fe's checks take on trust there (unsafe blocks, functions and impls, raw
  memory and storage accesses), what the model's prelude defines (externs, external calls and
  creations), and each constant held as the value the compiler computed, its definition not
  exported.
- `ExportedCorrect.lean` (PackedStore, ERC20, WETH9): what the exported arms and std code do.
- `RuntimeCorrect.lean`: the bytecode refines the exported contract.
- `Model.lean`, `ModelCorrect.lean`: the hand-written model and its certificate, which the
  exported one is derived from.

`FeProofs/Lib/Exported.lean` has the core and std definitions the exports share, each once, and
`FeProofs/Lib/ExportedCorrect.lean` theorems about them. A method is named after the type its
impl is for (`CallData_word_at`, `u256_to_word`). Where `FeProofs.Lib` is open, `simp` unfolds
these definitions, except the ones `ExportedCorrect.lean` states a theorem for.
`FeProofs/Fixtures/` has the exporter's output on fixtures without a bytecode proof, with checks
of what it means.

To update the exported text after a change to the exporter or to std, regenerate the exporter's
golden files and copy them in:

```sh
(cd <fe checkout> && LEAN_EXPORT_BLESS=1 cargo test -p fe-lean-export --test golden)
scripts/sync_exported.py <fe checkout>
lake build
```

and set `fe.pin` to that Fe commit, pushed to the repository it names.

### Differential tests

`scripts/audit_exports.sh <fe checkout>` exports every contract of Fe's test fixtures and of this
repository, elaborates each export, and compares model and bytecode in EVMLean
(`Fe/EVM/Diff.lean`, `Fe/EVM/Generate.lean`) at `P1`: on each call the file's Fe tests make, and
on sequences of generated calls, in an Osaka block, the fork Fe compiles for (EVMLean runs Osaka's
`CLZ` only there). It prints the constructs the exporter stopped at and the
calls that disagree, and writes its output under `.lake/export-corpus/`.

EVMLean computes ECRECOVER, RIPEMD-160, SHA-256, BLAKE2 F and the BN254 addition and
multiplication with Lean definitions; SNARKV and the KZG point evaluation still run Python scripts
of its own, which need packages this repository does not install, and no test of the corpus
reaches them. An EVMLean that ran ECRECOVER in Python too ran
`python3 Ethereum/EllipticCurvesPy/recover.py` in the working directory: the audit elaborates from
this repository's root, where `Ethereum/EllipticCurvesPy/recover.py` stands in for it and runs the
program `ecrecover` (`FeProofs/Precompiles/Secp256k1/Main.lean`, which the audit builds), which recovers the key
with the exported model of fevm's secp256k1 code.

`FeProofs/Precompiles` is an ingot of fevm's precompiles as contracts: `Ecrecover`, a message
`recover` around `secp256k1::recover`, and `Bn254Add`, `Bn254Mul`, `Blake2F`, `Ripemd160`,
`EcrecoverPrecompile`, `Identity` and `Modexp`, whose fallback arms hand fevm's ECADD, ECMUL, BLAKE2
F compression, RIPEMD-160, ECRECOVER in the precompile's format, IDENTITY copy and MODEXP the call
data in memory and return what the precompile does, or revert without data where it fails. The other
files of `src/` are copied verbatim from `ingots/precompiles/src` of
[fevm](https://github.com/fe-lang/fevm) at `a631a777b` (`modexp.fe` at `0f5a423d5`, branch
`fix/modexp-byte-order`, not yet on fevm's main), as are the definitions of `lib.fe` it names, and
`keccak/` (for `ByteSource` and `Keccak256`) from [keccak](https://github.com/fe-lang/keccak) at
`345d5088d`. The ingot is exported as one: `Exported/Shared.lean` has the definitions more than one
contract reaches, once, and `Exported/<Contract>.lean` each contract's own.
`FeProofs/Precompiles/Secp256k1` proves the exported `Ecrecover` against `Secp256k1.Spec.recover`
(`feEcrecoverContractCorrect`), on the Montgomery field arithmetic of `FeProofs/Precompiles/Field`
and the safegcd inversion of `FeProofs/Precompiles/Inverse`. `scripts/<Contract>Diff.lean` runs an
exported contract against EVMLean's precompile (`Ξ_BN_ADD`, `Ξ_BN_MUL`, `Ξ_BLAKE2_F`, `Ξ_RIP160`,
`Ξ_ECREC`, `Ξ_ID`, `Ξ_EXPMOD`) on go-ethereum's vectors, EVMLean's or the RIPEMD-160 paper's, and on
generated inputs (`lake env lean scripts/<name>.lean`); `scripts/ModexpVectors.lean` runs `Modexp`
on go-ethereum's MODEXP vectors against their outputs. `Modexp` bounds each length at 1,024 bytes
(EIP-7823), which EVMLean does not, so `ModexpDiff` checks only that the model fails above it.
`scripts/ModexpKnuth.lean` builds inputs that reach the rare branches of `Modulus::reduce` (the
digit `β - 1`, the corrections inside `div_3by2` and `rem_2by1`, the add-back, shift 0, a
normalised top limb of `2^63`, `count < n`), runs the exported `Modulus_reduce` on them against
`X mod M`, and the contract against `Ξ_EXPMOD`.
`FeProofs/Precompiles/Identity` proves the exported `Identity` against `Ξ_ID`
(`feIdentityContractCorrect`, `precompile_eq`): it stops with the call data, empty call data
included.

### Sonatina IR

`Fe/Sonatina/` has a semantics of Sonatina IR, the IR the Fe compiler's EVM backend compiles: the
IR of an object is a contract model (`Sidecar.model`), compared with the bytecode compiled from
it as exported models are. `fe build --emit sidecar` (Fe branch `sidecar`) writes the IR together
with the bytes, symbols and lowering record of each section from one compilation: the section
IR after the backend's pipeline, the machine IR the bytes are emitted from, and the hints that
connect the machine IR to the bytes. Each of the three IRs runs as a model. `scripts/SonatinaDiff.lean` runs
the certified contracts, `scripts/audit_sonatina.sh <fe checkout>` every contract of Fe's test
fixtures. `Fe/Sonatina/README.md` describes the subset and the design for splitting a certificate
at the IR.

`FeProofs/Case44Bank/Sonatina*.lean` is the first certificate through the checker of a contract
whose runtime makes an internal call: `feCase44BankRefinesExportedP1` and
`feCase44BankDeployRefinesExportedP1`, of the pinned bytecode against the exported model at
`P1`. The runtime calls `credit` twice. Each side has one lemma about its `credit` from any world
and arguments, `Exported.credit_exec` and the machine IR's `ir_credit`, and each call site
rewrites with it (`ir_step` leaves a callee's run for such a lemma, `Fe/Sonatina/Run.lean`). The
certificate needed the relations restricted to frames whose account exists (`OwnerExists`): the
compiler forwards the stored total to the sum it returns, where the exported model loads it
back, and on an account map without the code owner's account a store is dropped, so the two
returned different words there.

## Layout

Each contract directory (`FeProofs/<Contract>/`) holds the Fe source, the pinned bytecode, the
Stele specification (`SpecSyntax.lean`), files generated by EquiVM's scripts (`Bytecode.lean`,
`Selectors.lean`, the per-block summaries `*Blocks_NNN.lean`, and the `Spec`/`Common`/`Dispatch`
skeleton), one proof file per function, and the capstone `Correct.lean`. Unused generated block
summaries are pruned (`scripts/prune_blocks.py`).

Shared selector hashes are listed in `scripts/selector_facts.json`. To regenerate affected
`Selectors.lean` files, use an EquiVM scaffold with `--selector-facts` support and pass
`--selector-facts scripts/selector_facts.json`; then remove any unused declarations with
`scripts/drop_decl.py`. The pinned EquiVM library is sufficient to check the generated proofs.

Some generated branch summaries share their instruction prefixes. With an EquiVM generator
supporting `--share-branch-prefixes`, pass that flag and repeat `--share-branch-pc` for each
retained pair: the existing private definitions named `*_block_<pc>_shared` record those PCs.
After pruning and running `scripts/static_twins.py`, run `scripts/share_static_prefixes.py` on
the contract directory to share eligible prefixes with static-mode twins, then run
`scripts/prune_blocks.py` again to update the block indexes.

`Fe/` is the model library, independent of any contract: the monad of exported code
(`Core.lean`), the EVM world and its primitives (`EVM/World.lean`, `Int.lean`, `Storage.lean`,
`Calls.lean`), the refinement relation (`EVM/Refine.lean`, `Reach.lean`), invariants through
reentrant calls (`EVM/FrameCalls.lean` and `Invariant.lean`, which import EVMLean only, and
`RefineInvariant.lean`),
facts about exported entry code (`EVM/Entry.lean`), the differential tests (`EVM/Diff.lean`,
`Generate.lean`), and the commands that embed exported text (`Embed.lean`).

`FeProofs/Common/` is shared by the contracts:

- `Tactics.lean`: `rd_step`/`rd_run` apply the generated block summaries from an `RD` hypothesis
  (discharging stack bounds, jump destinations and branch conditions from `using [...]` hints),
  `rd_checked` handles Fe's success and return-size checks after an external call, and
  `u256_lits` normalizes word literals inside memory terms.
- `Stele.lean`: evaluation of locals, literals, binary operators (with `≥`, `-` and `+` on words),
  casts and `uint256` range checks, local assignment, and the `store_get` tactic for reading a
  local through a chain of inserts.
- `Storage.lean`: mapping slots (`keccak256(key ‖ slot)`, the hashes as Fe computes them) and
  reads and writes of `m[k]` and `m[k][k']` for any contract's Solidity layout.
- `Fallback.lean`: refinement glue for contracts with a fallback (EquiVM's assumes none).
- `Abi.lean`, `Memory.lean`, `Calls.lean`: ABI decoding facts (selector word, canonical
  `address`, fixed-width scalar arguments), memory facts (adjacent word writes), and call-result checks.
- `SelectorERC20.lean`, `SelectorGet.lean`: kernel-checked hashes reused by selector certificates.
- `Basic.lean`, `Glue.lean`, `Constructor.lean`, `CtorUInt256.lean`, `PackedByte.lean`: dispatcher
  revert paths and Fe's checked arithmetic and `assert!` branches, small refinement glue,
  constructor shapes, and byte lanes of packed storage.

`scripts/` has `Audit.lean` (axioms of every capstone), `Unused.lean` (declarations no capstone
uses), `Dups.lean` (theorems duplicating another, in this project or its dependencies),
`Tactics.lean` (regressions for the side-goal search of the block-stepping tactics), the
cleanup helpers used to shrink the proofs, and the scripts of the exported models:
`sync_exported.py`, `audit_exports.sh` with its helpers (`lean_check_one.sh`, `build_ffi.sh`,
`tally_blockers.py`, `tally_diff.py`), and the checks CI runs (`check_*.sh`, `fetch_fe.sh`,
`install_elan.sh`) with the output they expect (`expected/`).

## Checking the proofs

CI (`.github/workflows/ci.yml`) runs these scripts on pushes to `main` and `fe-model` and on pull
requests. Each runs the same on a laptop, from any directory.

```sh
scripts/check_build.sh   # Mathlib's prebuilt files (`lake exe cache get`), then `lake build`
scripts/check_audit.sh   # the axioms of every capstone, against scripts/expected/audit.txt
```

The build fails on any error. `check_audit.sh` runs `scripts/Audit.lean`, which prints the axioms
each capstone theorem depends on: `Classical.choice`, `Quot.sound`, `propext` and a count of
`native_decide` evaluations of concrete bytecode facts. It fails if a capstone depends on any
other axiom (`sorryAx` among them), and on any difference from the expected file: a new or
missing capstone, or a changed count.

The exported models are checked with the Fe commit pinned in `fe.pin`:

```sh
fe=$(scripts/fetch_fe.sh)        # checks it out in .lake/fe
scripts/check_build.sh Fe
scripts/check_sync.sh "$fe"      # the golden test passes; Exported.lean and .trust files hold its output
scripts/check_bytecode.sh "$fe"  # each contract whose *.build.json names that commit compiles to its pinned bytes
scripts/check_corpus.sh "$fe"    # the export audit, against scripts/expected/exports.txt
```

`check_corpus.sh` runs `scripts/audit_exports.sh` and compares the totals, the constructs the
exporter stopped at, the files that do not elaborate and every differential-test line of each
file with the expected file.

A change that is meant to change an expected file updates it in the same commit: rerun the check
with `BLESS=1`, which copies the new output over the expected file, and review `git diff`. To move
to another Fe commit, change `fe.pin`, update the exported text as in "Exported models", and bless
the export audit.

## Reproducing the bytecode

Each contract directory holds the Fe source, the compiler settings
(`*.build.json`) and the bytecode the proofs are about. With the Fe compiler at
the listed commit, for example:

```sh
fe build FeDeposit.fe --standalone -O 1 --out-dir out --emit bytecode,runtime-bytecode
```

`out/DepositContract.bin` and `out/DepositContract.runtime.bin` must match
`creation.hex` and `runtime.hex`, ignoring a trailing newline. WETH9 is built as an ingot:

```sh
fe build FeProofs/WETH9 --contract WETH9 -O 1 --out-dir out --emit bytecode,runtime-bytecode
```

FeERC20's, FeDeposit's and WETH9's bytecode is what the Fe commit `fe.pin` names compiles, which
their `*.build.json` record (`scripts/check_bytecode.sh` checks it). A record's `contract` is the
name of the contract's files here; where Fe's contract has another name, `compiler.feContract`
gives it (`DepositContract`, `WETH9`):

```sh
fe build FeProofs/ERC20/FeERC20.fe --standalone -O 1 --out-dir out --emit bytecode,runtime-bytecode
```

`out/FeERC20.bin` and `out/FeERC20.runtime.bin` must match `FeProofs/ERC20/creation.hex` and
`FeProofs/ERC20/runtime.hex`. 

`FeProofs/Case44Bank` is the contract `Case44Bank` of Fe's `acceptance.fe` alone in a file, whose
runtime calls an internal function twice, with its bytecode and exported model and no proof yet.
Its bytecode is built with the Fe commit `Case44Bank.build.json` names, and is the same as the
compiler of the IR checker's sidecar makes:

```sh
fe build FeProofs/Case44Bank/Case44Bank.fe --standalone -O 1 --out-dir out --emit bytecode,runtime-bytecode
```
