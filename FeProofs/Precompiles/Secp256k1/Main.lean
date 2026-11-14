import FeProofs.Precompiles.Exported.Ecrecover
import Fe.EVM.Diff

/-!
# ECDSARECOVER by fevm's code

An EVMLean that computes ECRECOVER (`Ξ_ECREC`) in Python gets the signer's public key from a
process, `python3 Ethereum/EllipticCurvesPy/recover.py e v r s`, which uses the Python package
`coincurve`; the EVMLean this repository pins computes it in Lean.  `ecrecover e v r s` prints
what that script prints, computed by the exported model of fevm's secp256k1 key recovery: the
model's `runtime` on a call of `recover(e, v, r, s)`, the arm of the contract `Ecrecover`
(`FeProofs/Precompiles/src/lib.fe`) around `secp256k1::recover`.  The script of that name at the
repository root runs it.

The arguments are big-endian hex, as `Ξ_ECREC` passes them: the message hash `e`, the recovery id
`v` (0 or 1) and the signature `r`, `s`.  The output, without a newline, is the key `x ‖ y` as 128
hex digits, or `error` when the contract recovers none: for a recovery id other than 0 and 1, an
`r` or `s` that is 0 or at least the group order, an `r` that is no point's `x`, or the key at
infinity.  (`recover.py` accepts the recovery ids 2 and 3 too, which `Ξ_ECREC` never passes.)
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.Ecrecover

open FeProofs.Precompiles

/-- The number of at most 32 bytes that a string of hex digits spells, big-endian. -/
def word? (digits : String) : Option Nat := do
  let bytes ← (ByteArray.ofBlob digits).toOption
  if bytes.size ≤ 32 then some (fromByteArrayBigEndian bytes) else none

/-- The calldata of `recover(e, v, r, s)`. -/
def calldata (e v r s : Nat) : ByteArray :=
  [e, v, r, s].foldl (fun data n => data ++ (UInt256.ofNat n).toByteArray)
    ((KEC "recover(uint256,uint256,uint256,uint256)".toUTF8).extract 0 4)

/-- The key the model returns, `none` if it returns none, or how it ends instead. -/
def recover (e v r s : Nat) : Except String (Option ByteArray) :=
  let I : ExecutionEnv := { (default : ExecutionEnv) with calldata := calldata e v r s }
  let returned (out : ByteArray) : Except String (Option ByteArray) :=
    if out.size != 96 then .error s!"returns {Ethereum.toHex out}"
    else if fromByteArrayBigEndian (out.extract 0 32) == 1 then .ok (some (out.extract 32 96))
    else .ok none
  match (entry Precompiles.Exported.Ecrecover.runtime).exec I (World.init ∅ default) with
  | some (.ok (out, _)) | some (.error (.stop out _)) => returned out
  | some (.error exit) => .error (Diff.describeExit exit)
  | none => .error "does not terminate"

end FeProofs.Ecrecover

open FeProofs.Ecrecover in
def main (args : List String) : IO UInt32 := do
  match args.mapM word? with
  | some [e, v, r, s] =>
    match recover e v r s with
    | .ok key =>
      IO.print (key.elim "error" Ethereum.toHex)
      return 0
    | .error how =>
      IO.eprintln s!"ecrecover: the model {how}"
      return 1
  | _ =>
    IO.eprintln "usage: ecrecover <hash> <recovery id> <r> <s>, each at most 32 bytes in hex"
    return 2
