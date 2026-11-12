import Reasoning.Reach
import FeProofs.Deposit.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace feDepositBlocks

/-- Final stack for bytecode block summary `feDeposit_block_286_fallthrough`. -/
def feDeposit_block_286_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 286. -/
theorem feDeposit_block_286_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 32) x2) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 286) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 295) (feDeposit_block_286_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 362) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 295)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_295`. -/
def feDeposit_block_295_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1463040085526317939991363640015092170718453806954579752284610100685172) :: (UInt256.ofNat 47218010385908144003813089253757259093500130473809738114111675728878616182784) :: R)

/-- Automatically generated RD summary for bytecode block at pc 295. -/
theorem feDeposit_block_295 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2203) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 295) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2203) (feDeposit_block_295_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 47218010385908144003813089253757259093500130473809738114111675728878616182784) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1463040085526317939991363640015092170718453806954579752284610100685172) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2203) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2203)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_362_taken`. -/
def feDeposit_block_362_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 362. -/
theorem feDeposit_block_362_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 96) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 422) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 362) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 422) (feDeposit_block_362_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 422) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 422)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_362_fallthrough`. -/
def feDeposit_block_362_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 362. -/
theorem feDeposit_block_362_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 96) x1) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 362) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 371) (feDeposit_block_362_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 422) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 371)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_371`. -/
def feDeposit_block_371_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1112560778853359622660692443883836971961170929461552310030263167183207) :: (UInt256.shiftLeft (UInt256.ofNat 1093157339067989645933971041933) (UInt256.ofNat 155)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 371. -/
theorem feDeposit_block_371 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2203) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 371) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2203) (feDeposit_block_371_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1093157339067989645933971041933) (width := 13) (op := .PUSH13) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 155) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1112560778853359622660692443883836971961170929461552310030263167183207) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2203) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2203)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Shared branch prefix at pc 422. -/
private def feDeposit_block_422_shared {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 422) R mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 488) (by native_decide) (by evm_ov)
  exact r7

/-- Final stack for bytecode block summary `feDeposit_block_422_taken`. -/
def feDeposit_block_422_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 422. -/
theorem feDeposit_block_422_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ee.weiValue (UInt256.ofNat 1000000000000000000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 488) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 422) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 488) (feDeposit_block_422_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  have r7 := feDeposit_block_422_shared hstack h
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 488)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_422_fallthrough`. -/
def feDeposit_block_422_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Automatically generated RD summary for bytecode block at pc 422. -/
theorem feDeposit_block_422_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ee.weiValue (UInt256.ofNat 1000000000000000000))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 422) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 440) (feDeposit_block_422_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  have r7 := feDeposit_block_422_shared hstack h
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 440)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_440`. -/
def feDeposit_block_440_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1031680938851907703276691398622778079940259490106690526480247486308716) :: (UInt256.shiftLeft (UInt256.ofNat 554382338263822742876023) (UInt256.ofNat 176)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 440. -/
theorem feDeposit_block_440 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2203) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 440) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2203) (feDeposit_block_440_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 554382338263822742876023) (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 176) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1031680938851907703276691398622778079940259490106690526480247486308716) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2203) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2203)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Shared branch prefix at pc 488. -/
private def feDeposit_block_488_shared {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 488) (x0 :: R) mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1000000000) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.mod (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 568) (by native_decide) (by evm_ov)
  exact r6

/-- Automatically generated RD summary for bytecode block at pc 488. -/
theorem feDeposit_block_488_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.mod x0 (UInt256.ofNat 1000000000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 568) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 488) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ (k + 7) (C + ((28))) := by
  have r6 := feDeposit_block_488_shared hstack h
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 568)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 488. -/
theorem feDeposit_block_488_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.mod x0 (UInt256.ofNat 1000000000))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 488) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 501) (x0 :: R) mem aw rdata σ (k + 7) (C + ((28))) := by
  have r6 := feDeposit_block_488_shared hstack h
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 501)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_501`. -/
def feDeposit_block_501_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1382160245524866020607362594754033278697542367599717968734594419548524) :: (UInt256.ofNat 53099278670999451058051302811168505420277119914841686327538985755642649640960) :: R)

/-- Automatically generated RD summary for bytecode block at pc 501. -/
theorem feDeposit_block_501 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2203) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 501) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2203) (feDeposit_block_501_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 53099278670999451058051302811168505420277119914841686327538985755642649640960) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1382160245524866020607362594754033278697542367599717968734594419548524) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2203) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2203)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Shared branch prefix at pc 568. -/
private def feDeposit_block_568_shared {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1000000000) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.div (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r8 := r7.shr (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 637) (by native_decide) (by evm_ov)
  exact r12

/-- Final stack for bytecode block summary `feDeposit_block_568_taken`. -/
def feDeposit_block_568_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 (UInt256.ofNat 1000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 568. -/
theorem feDeposit_block_568_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.div x0 (UInt256.ofNat 1000000000)) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 637) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 637) (feDeposit_block_568_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((45))) := by
  have r12 := feDeposit_block_568_shared hstack h
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 637)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_568_fallthrough`. -/
def feDeposit_block_568_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 (UInt256.ofNat 1000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 568. -/
theorem feDeposit_block_568_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (UInt256.div x0 (UInt256.ofNat 1000000000)) (UInt256.shiftRight (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat 192)))) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 568) (x0 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 588) (feDeposit_block_568_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((45))) := by
  have r12 := feDeposit_block_568_shared hstack h
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 588)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_588`. -/
def feDeposit_block_588_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1058640885519058343071358413709797710613896634529231098961351096557932) :: (UInt256.shiftLeft (UInt256.ofNat 17740234824442327763594477) (UInt256.ofNat 171)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 588. -/
theorem feDeposit_block_588 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2203) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 588) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2203) (feDeposit_block_588_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 17740234824442327763594477) (width := 11) (op := .PUSH11) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 171) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1058640885519058343071358413709797710613896634529231098961351096557932) (width := 29) (op := .PUSH29) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2203) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2203)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_637`. -/
def feDeposit_block_637_stack {g : Sat256} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((58) + (memExpansionCost aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (UInt256.ofNat 256) :: (UInt256.ofNat 64) :: (UInt256.ofNat 256) :: (UInt256.ofNat 32) :: ((g.subNat (C + ((58) + (memExpansionCost aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_637`. -/
def feDeposit_block_637_memory {mem : ByteArray} {x3 : UInt256} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.shiftRight (memLoad ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 128)) (UInt256.ofNat 128)).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 32)) mem).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 288).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 637. -/
theorem feDeposit_block_637 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 637) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 677) (feDeposit_block_637_stack (g := g) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (feDeposit_block_637_memory (mem := mem) (x3 := x3)) (M (M (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((78) + (memExpansionCost aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shr (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := RD.genGas (RD.normalizeCounters (k' := k + 20) (C' := C + ((58) + (memExpansionCost aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw ((x3 + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) r20 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r27 := r26.dup6 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 677)) r27 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 677: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 678 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `feDeposit_block_678_taken`. -/
def feDeposit_block_678_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 678. -/
theorem feDeposit_block_678_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 678) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) (feDeposit_block_678_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_678_fallthrough`. -/
def feDeposit_block_678_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 678. -/
theorem feDeposit_block_678_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 678) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 685) (feDeposit_block_678_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((21))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 685)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Shared branch prefix at pc 685. -/
private def feDeposit_block_685_shared {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 685) R mem aw rdata σ k C) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 2199) (by native_decide) (by evm_ov)
  exact r6

/-- Automatically generated RD summary for bytecode block at pc 685. -/
theorem feDeposit_block_685_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J FeProofs.Deposit.feDepositBytecode 0).contains (UInt256.ofNat 2199) = true)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 685) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 2199) R mem aw rdata σ (k + 7) (C + ((25))) := by
  have r6 := feDeposit_block_685_shared hstack h
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2199)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 685. -/
theorem feDeposit_block_685_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 685) R mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 695) R mem aw rdata σ (k + 7) (C + ((25))) := by
  have r6 := feDeposit_block_685_shared hstack h
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 695)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Final stack for bytecode block summary `feDeposit_block_695`. -/
def feDeposit_block_695_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((133) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.ofNat 2) :: (x4 + (UInt256.ofNat 32)) :: (UInt256.ofNat 64) :: (UInt256.ofNat 320) :: (UInt256.ofNat 32) :: (x4 + (UInt256.ofNat 32)) :: ((g.subNat (C + ((133) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (UInt256.shiftLeft (UInt256.lor (UInt256.shiftRight (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x0 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x0 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32)) (UInt256.shiftLeft (UInt256.lor (UInt256.land (UInt256.ofNat 281470681808895) (UInt256.shiftRight (UInt256.lor (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x0 (UInt256.ofNat 8)))) (UInt256.ofNat 16))) (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.land x0 (UInt256.ofNat 71777214294589695)) (UInt256.ofNat 8)) (UInt256.land (UInt256.ofNat 71777214294589695) (UInt256.shiftRight x0 (UInt256.ofNat 8)))) (UInt256.ofNat 281470681808895)) (UInt256.ofNat 16))) (UInt256.ofNat 32))) (UInt256.ofNat 192)) :: (memLoad (UInt256.ofNat 256) mem) :: (memLoad (x6 + (UInt256.ofNat 32)) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `feDeposit_block_695`. -/
def feDeposit_block_695_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 695. -/
theorem feDeposit_block_695 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (h : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 695) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD FeProofs.Deposit.feDepositBytecode ee g s0 (UInt256.ofNat 796) (feDeposit_block_695_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (feDeposit_block_695_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 55) (C + ((162) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup9 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 71777214294589695) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.swap3 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r14 := r13.shr (by native_decide) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 71777214294589695) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.swap3 (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.pushConst (UInt256.ofNat 281470681808895) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r27 := r26.shr (by native_decide) (by evm_ov)
  have r28 := r27.pushConst (UInt256.ofNat 281470681808895) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r29 := r28.and (by native_decide) (by evm_ov)
  have r30 := r29.or (by native_decide) (by evm_ov)
  have r31 := r30.dup1 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r33 := r32.shl (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r36 := r35.shr (by native_decide) (by evm_ov)
  have r37 := r36.or (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r39 := r38.shl (by native_decide) (by evm_ov)
  have r40 := r39.push0 (by native_decide) (by evm_ov)
  have r41 := r40.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r42 := RD.genMstore r41 (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r45 := RD.genMstore r44 (by native_decide) (by evm_ov)
  have r46 := RD.genGas (RD.normalizeCounters (k' := k + 45) (C' := C + ((133) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x6 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) r45 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r48 := r47.dup9 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r53 := r52.dup4 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r55 := r54.dup7 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 796)) r55 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Unsupported instruction boundary at pc 796: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 797 from a fresh symbolic RD state. -/

end feDepositBlocks
