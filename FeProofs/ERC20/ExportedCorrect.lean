import FeProofs.ERC20.Exported
import FeProofs.ERC20.ModelCorrect

/-!
# FeERC20: the bytecode refines the exported arms

`Exported.contract` is the model with every arm body and the `init` body replaced by the
exporter's output.  The entry code around them (dispatch, call-value and calldata checks, result
encoding) and the two event encodings are still written by hand.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.ERC20.Exported

def approveArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return Model.encodeBool (← recv0_arm1 (word cd 4) (word cd 36))

def totalSupplyArm : FeM ByteArray := do
  nonPayable
  return (← recv0_arm5).toByteArray

def transferFromArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 3 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  if NotAddress (word cd 36) then M.revert ByteArray.empty
  return Model.encodeBool (← recv0_arm2 (word cd 4) (word cd 36) (word cd 68))

def balanceOfArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 1 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return (← recv0_arm3 (word cd 4)).toByteArray

def transferArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  return Model.encodeBool (← recv0_arm0 (word cd 4) (word cd 36))

def allowanceArm (cd : ByteArray) : FeM ByteArray := do
  nonPayable
  if BadHead cd 2 then M.revert ByteArray.empty
  if NotAddress (word cd 4) then M.revert ByteArray.empty
  if NotAddress (word cd 36) then M.revert ByteArray.empty
  return (← recv0_arm4 (word cd 4) (word cd 36)).toByteArray

def runtime : FeM ByteArray := do
  let cd ← calldata
  if cd.size < 4 then M.revert ByteArray.empty
  else if Model.approveSelector == cd.extract 0 4 then approveArm cd
  else if Model.totalSupplySelector == cd.extract 0 4 then totalSupplyArm
  else if Model.transferFromSelector == cd.extract 0 4 then transferFromArm cd
  else if Model.balanceOfSelector == cd.extract 0 4 then balanceOfArm cd
  else if Model.transferSelector == cd.extract 0 4 then transferArm cd
  else if Model.allowanceSelector == cd.extract 0 4 then allowanceArm cd
  else M.revert ByteArray.empty

def initEntry (args : ByteArray) : FeM Unit := do
  nonPayable
  if args.size < 32 then M.revert ByteArray.empty
  init (word args 0)

def contract : ContractModel := ⟨initEntry, runtime⟩

theorem runtime_exec (I : ExecutionEnv) (w : World) :
    runtime.exec I w = Model.runtime.exec I w := by
  simp only [runtime, Model.runtime, approveArm, totalSupplyArm, transferFromArm, balanceOfArm,
    transferArm, allowanceArm, Model.approveArm, Model.totalSupplyArm, Model.transferFromArm,
    Model.balanceOfArm, Model.transferArm, Model.allowanceArm]
  simp [M.exec_ite, exec_nonPayable, transfer_exec, approve_exec, transferFrom_exec,
    balanceOf_exec, allowance_exec, totalSupply_exec]

theorem init_entry_exec (args : ByteArray) (out : ByteArray) (I : ExecutionEnv) (w : World) :
    (initEntry args >>= fun _ => pure out).exec I w
      = (Model.init args >>= fun _ => pure out).exec I w := by
  simp [initEntry, Model.init, M.exec_ite, exec_nonPayable, init_exec]

/-- The runtime bytecode refines the contract built from the exported arms. -/
theorem feERC20RefinesExported : Refines .P0 feERC20Bytecode contract := by
  intro σ σ₀ g A I hcode hsize
  have h := feERC20RefinesModel σ σ₀ g A I hcode hsize
  unfold RefinesFor at h ⊢
  rwa [show contract.runtime = runtime from rfl, runtime_exec]

/-- Deployment refines the contract built from the exported `init`. -/
theorem feERC20DeployRefinesExported :
    RefinesDeploy .P0 feERC20CreationBytecode feERC20Bytecode contract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  intro σ σ₀ g A I args hargs hcode hperm
  have h := feERC20DeployRefinesModel σ σ₀ g A I args hargs hcode hperm
  rwa [show contract.init = initEntry from rfl, init_entry_exec]

end FeProofs.ERC20.Exported
