import FeProofs.Fixtures.Ints

/-!
# Lanes against the compiler's shifts and masks

`Fe/EVM/Storage.lean` defines a lane's read and write arithmetically.  This file checks them
against the word operations the compiler emits, `(w >> 8·off) & mask` and
`(w & ~(mask << 8·off)) | (bits << 8·off)`, on a grid of boundary words and lanes.  The checks
are evaluations, not proofs for every word.
-/

open Ethereum Ethereum.EVM Fe Fe.EVM

namespace FeProofs.Fixtures.State

open FeProofs.Fixtures.Ints (samples)

/-- Lanes at both ends of a slot and in its middle, of one to twenty bytes, and a whole slot. -/
def lanes : List Lane :=
  [⟨0, 1, true⟩, ⟨1, 1, true⟩, ⟨2, 2, true⟩, ⟨4, 20, true⟩, ⟨31, 1, true⟩, ⟨16, 16, true⟩,
    ⟨0, 32, false⟩]

def mask (l : Lane) : UInt256 := UInt256.ofNat (2 ^ (8 * l.width) - 1)
def shift (l : Lane) : UInt256 := UInt256.ofNat (8 * l.off)

/-- A lane's bytes are the word shifted down and masked. -/
theorem get_shift_mask : lanes.all (fun l => samples.all fun w =>
    UInt256.ofNat (l.get w) == (w >>> shift l) &&& mask l) = true := by
  native_decide

/-- A write to a lane clears its bytes and ors the new ones in. -/
theorem set_clear_or : lanes.all (fun l => samples.all fun w => samples.all fun v =>
    let bits := v &&& mask l
    l.set w bits.toNat == (w &&& ~~~(mask l <<< shift l)) ||| (bits <<< shift l)) = true := by
  native_decide

/-- A signed integer in a lane is its bytes sign-extended from the lane's top byte. -/
theorem load_signed : lanes.all (fun l => l.width == 32 || samples.all fun w =>
    IntTy.cast (.u 256) (l.ty (.i 256)) (UInt256.ofNat (l.get w)) ==
      UInt256.signextend (UInt256.ofNat (l.width - 1)) ((w >>> shift l) &&& mask l)) = true := by
  native_decide

/-- The word a whole struct's packed fields make is the or of their shifted bytes. -/
theorem packed_or : samples.all (fun a => samples.all fun b =>
    let a := a &&& UInt256.ofNat 0xff
    let b := b &&& UInt256.ofNat 0xffff
    packed [(0, a.toNat), (2, b.toNat)] == a ||| (b <<< UInt256.ofNat 16)) = true := by
  native_decide

end FeProofs.Fixtures.State
