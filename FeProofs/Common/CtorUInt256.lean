import Reasoning.Constructor
import Reasoning.Memory

/-!
# Deployments of a constructor taking one `uint256`

Solidity-style deployment appends the argument's 32-byte big-endian word to the initcode; no other
argument list encodes.

-- LIBRARY CANDIDATE: `Reasoning/Constructor.lean` (generalizes the per-example deployment-shape
-- lemmas such as `ctorStoreDeployment_shape`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace FeProofs.Common

theorem uint256CtorDeployment_shape {name : Ident} {initcode d : ByteArray} {args : List Value}
    (h : genSolidityConstructorDeployment [{ name := name, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
      initcode args = some d) :
    ∃ i : Int, args = [.int i] ∧ 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) ∧
      d = initcode ++ (EVM.Word.toBytesBE (EVM.word i.toNat)).toByteArray := by
  cases args with
  | nil =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
              abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
              encodeABIWord?] at h
      | nil =>
          cases arg with
          | int i =>
              by_cases hbounds : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
              · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?, hbounds] at h
                change (((if i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (initcode ++ args.toByteArray)) = some d at h
                split at h
                · simp at h
                  exact ⟨i, rfl, hbounds.1, hbounds.2, h.symm⟩
                · rename_i hnot
                  exact False.elim (hnot hbounds.2)
              · simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat)
                    else none).bind fun word => some word.toBytesBE).bind
                    fun args => some (initcode ++ args.toByteArray)) = some d at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | _ =>
              simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
                abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                encodeABIWord?] at h

end FeProofs.Common
