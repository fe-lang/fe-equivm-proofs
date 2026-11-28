import Fe.Sonatina.H.Syntax
import Fe.Sonatina.H.Parse
import Fe.Sonatina.H.Value
import Fe.Sonatina.H.Memory
import Fe.Sonatina.H.World
import Fe.Sonatina.H.Inst
import Fe.Sonatina.H.Sem
import Fe.Sonatina.H.Run
import Fe.Sonatina.H.Wf
import Fe.Sonatina.H.Compose
import Fe.Sonatina.H.Tests

/-!
# The handover semantics H (design `s3/design.md` §3, §7.2; Slice 1)

The semantics of the IR machine lowering reads (`source_ir`), in which a pointer carries the
block it came from and each block's address word is a choice.

| Module | What | Design |
| --- | --- | --- |
| `H/Syntax` | `HInst`/`HTerm` (the machine IR's syntax plus `gep`, `evm_mload_bytes`, `trunc_nuw`, `evm_return_code`, `evm_revert_word`), `HSection`, `Object` | §10 Slice 1 |
| `H/Parse` | `parseModule` of `source_ir`, `objectOfSidecar` | |
| `H/Value` | `Val` (integers, pointers with origins), `MByte` (bytes, pointer fragments), `MemBlock` | §3.2–§3.4 |
| `H/Memory` | `State`, `AddrOk`, `align32`, `heapBudget`, `State.alloc`, `State.range` (E1, U1), typed `load`, `sizeOf` | §3.3, §3.4 |
| `H/World` | `messageCore`, `createCore`; `message_eq_core`, `createWith_eq_core` | §3.6 prerequisite |
| `H/Inst` | `Outcome`, `stepInst`, `stepTerm`, `EvmOp.arity` | §3.2, §3.4, §3.6, §3.7 |
| `H/Sem` | `ExecBody`/`ExecBlocks`/`ExecFunc`, `Object.Runtime`, `Object.Deploy`, `Matches`, `ImplementsH`, `ImplementsDeployH`; the readings I1–I11 | §3.1, §3.3, §7.2 |
| `H/Compose` | `RefinesForH`, `RefinesOnH`, `RefinesDeployH`, `Matches.agrees`, `RefinesOnFut.toH`, `RefinesDeployFut.toH` | §7.4 |
| `H/Run` | `Oracle`, `runFunc`, `runRuntime`, `runDeploy`; `runH_sound`, `runRuntime_sound`, `runDeploy_sound` | §3.1 |
| `H/Wf` | `wfReasons`, `wfH`: what H needs for no run to be stuck, and §3.7's rejections | §3.7 static rejections |
| `H/Tests` | `#guard` tests of the rules, one at a time, under two oracles, and of `wfH` | |

`scripts/HDiff.lean` runs H against the machine IR's interpreter on generated calls.
-/
