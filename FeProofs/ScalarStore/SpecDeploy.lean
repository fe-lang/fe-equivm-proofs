import FeProofs.ScalarStore.SpecCorrect
import FeSpecProofs.ScalarStoreInit

/-!
# FeScalarStore: deployment refines the interpreter's `initEntry`
-/

open Ethereum Ethereum.EVM Reasoning.Theory Fe Fe.EVM

namespace FeProofs.ScalarStore.Spec

/-- The interpreter's deployment entry of FeScalarStore on the EVM host whose code region is the
    creation code (133 bytes), from reserved memory: the bytes of the immutable fields. -/
def initM : FeM ByteArray := do
  reserve
  match ← (Fe.Sem.initEntry Fe.Proofs.scalarStore (specHost 133 [])).result {} with
  | .ok b => pure b
  | .error _ => Fe.M.diverge

/-- On one argument word after the creation code, the interpreter's deployment entry ends as the
    hand-written model's constructor does. -/
theorem init_endsAs (v : UInt256) (out : ByteArray) (I : ExecutionEnv) (w : World)
    (hmem : w.memory.size + 32 < UInt256.size)
    (hcode : I.code = feScalarStoreCreationBytecode ++ ctorTail v) (hperm : I.perm = true) :
    EndsAs ((initM >>= fun tail => pure (out ++ tail)).exec I w)
      ((Model.init (ctorTail v) >>= fun _ => pure out).exec I w) := by
  have hts : (ctorTail v).size = 32 := word_toBytesBE_toByteArray_size v
  have hcs := Sonatina.creation_runtime.2
  have hsize : I.code.size = 165 := by rw [hcode, ByteArray.size_append, hcs, hts]
  have hcs' : (UInt256.ofNat I.code.size).toNat = 165 := by rw [hsize]; rfl
  have harg : I.code.readWithPadding 133 32 = ctorTail v := by
    rw [readWithPadding_eq_extract _ _ (by omega), hcode,
      extract_append_right_window _ _ _ _ (by omega), hcs]
    show (ctorTail v).extract 0 32 = _
    rw [← hts, byteArray_extract_self]
  have hroom : w.reserved.memory.size + 32 < UInt256.size := reserveMemory_room hmem (by decide)
  have h165 : (UInt256.ofNat 165).toNat = 165 := rfl
  have hval : Fe.Sem.bytesNat (ctorTail v) = v.toNat := by
    rw [bytesNat_eq, Exported.ctorTail_eq, fromByteArrayBigEndian_toByteArray]
  have hword : uInt256OfByteArray ((ctorTail v).readBytes 0 32) = v := by
    rw [readBytes_all32 _ hts, Exported.ctorTail_eq, uInt256OfByteArray_toByteArray]
  unfold initM
  rw [Fe.Proofs.ScalarStore.init_entry_spec]
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have hwv' : I.weiValue.toNat ≠ 0 := fun h => hwv (u256_inj h)
    simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.init, callvalue, hwv', Model.init,
      exec_nonPayable, hwv]
    exact .exit _
  simp [M.exec_bind, Fe.Proofs.ScalarStore.Shallow.init, callvalue, hwv, harg, alloc, hroom,
    toNat32, mstoreBytes, Model.init, exec_nonPayable, hts, hword, Model.initBody, codesize, hsize, h165]
  have hlt : w.reserved.memory.size < UInt256.size := by omega
  have hA : w.reserved.memory.size % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w.reserved.memory.size :=
    Nat.mod_eq_of_lt (by unfold UInt256.size at hlt; exact hlt)
  have hbase : (w.reserved.memory ++ ({ data := Array.replicate 32 0 } : ByteArray)).size =
      w.reserved.memory.size + 32 := by
    rw [ByteArray.size_append]; rfl
  simp only [UInt256.toNat_ofNat_of_lt hlt, hA]
  rw [write32_read_back _ _ _ (by rw [hts]) (by rw [hbase]; omega)]
  have hx : (ctorTail v).extract 0 32 = ctorTail v := by rw [← hts, byteArray_extract_self]
  have hz : ({ data := Array.replicate 0 0 } : ByteArray) = ByteArray.empty := rfl
  have hvm : v.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = v.toNat := Nat.mod_eq_of_lt v.val.isLt
  simp only [hx, hts, Nat.sub_self, hz, ByteArray.append_empty, hval, hvm, u256_ofNat_toNat,
    exec_sstore, hperm, Model.storedSlot]
  exact .ok_ok rfl rfl rfl

/-- FeScalarStore as the interpreter means it: its runtime entry and its deployment entry. -/
def fullContract : ContractModel := { contract with init := fun _ => initM }

/-- The runtime bytecode refines the interpreter's runtime entry (`feScalarStoreRefinesSpec`). -/
theorem feScalarStoreRefinesSpecFull :
    RefinesOn .P1 feScalarStoreBytecode fullContract CalldataFits :=
  feScalarStoreRefinesSpec

/-- **Deployment by the creation bytecode of FeScalarStore, with one ABI-encoded `uint256`
    argument, refines the interpreter's `initEntry`** at profile `P1`: the exported
    deployment's `P1` certificate, transferred because both end as the hand-written
    constructor does. -/
theorem feScalarStoreDeployRefinesSpec :
    RefinesDeploy .P1 feScalarStoreCreationBytecode feScalarStoreBytecode fullContract
      (fun args => ∃ v : UInt256, args = ctorTail v) := by
  rintro σ σ₀ g A I args ⟨v, rfl⟩ hcode hown hperm
  rcases Sonatina.feScalarStoreDeployRefinesExportedP1 σ σ₀ g A I _ ⟨v, rfl⟩ hcode hown hperm
    with h | ⟨feed, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨feed, Agrees.of_endsAs_common
      (init_endsAs v _ I _ (by simp [World.init, UInt256.size]) hcode hperm)
      (Exported.init_endsAs v _ I _ (by simp [World.init, UInt256.size])) h⟩

end FeProofs.ScalarStore.Spec
