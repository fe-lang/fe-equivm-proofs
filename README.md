# Fe EquiVM proofs

Machine-checked refinement proofs, in Lean 4 with
[EquiVM](https://github.com/argotorg/EquiVM), that EVM bytecode produced by the
[Fe](https://github.com/argotorg/fe) compiler behaves exactly like a high-level
specification written in EquiVM's specification language, Stele.

## Contracts

| Module | Contract | Compiler | Theorem |
| --- | --- | --- | --- |
| `FeProofs.Deposit` | [Fe deposit contract](https://github.com/argotorg/fe/blob/822e80878/crates/fe/tests/fixtures/fe_test/deposit_contract.fe) | Fe 26.4.0 (`822e80878`), Sonatina, `-O 1`, Osaka | `feDepositContractCorrect` |

`feDepositContractCorrect` covers the constructor and every runtime entry point
(`deposit`, `get_deposit_root`, `get_deposit_count`, `supportsInterface`): for
every input, the deployed bytecode returns, reverts, writes storage and emits
events exactly as the Stele specification in `FeProofs/Deposit/SpecSyntax.lean`
does. What the theorem assumes and does not claim:

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

## Checking the proofs

```sh
lake exe cache get   # Mathlib's prebuilt files
lake build
```

The build fails on any error. To list the axioms the capstone depends on:

```sh
printf 'import FeProofs\n#print axioms FeProofs.Deposit.feDepositContractCorrect\n' | lake env lean --stdin
```

Expect `propext`, `Classical.choice`, `Quot.sound` and the `native_decide`
evaluations of concrete bytecode facts, and no `sorryAx`.

## Reproducing the bytecode

Each contract directory holds the Fe source, the compiler settings
(`*.build.json`) and the bytecode the proofs are about. With the Fe compiler at
the listed commit:

```sh
fe build FeDeposit.fe --standalone -O 1 --out-dir out --emit bytecode,runtime-bytecode
```

`out/DepositContract.bin` and `out/DepositContract.runtime.bin` must match
`creation.hex` and `runtime.hex`, ignoring a trailing newline.
