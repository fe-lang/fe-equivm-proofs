import Ethereum.SpongeHash.Keccak256
import Mathlib.Tactic.IntervalCases

/-!
# Keccak: EVMLean's Keccak-f[1600] lane by lane

EVMLean's `Keccak256.round` (theta, rho, pi, chi, iota as loops over `Vector UInt64 25`) is
`roundK`, the round written lane by lane as fevm's `keccak_round` computes it (`round_eq`), and
`Keccak256.permute` is `roundK` folded over the 24 round constants (`permute_eq`).

The lane accessors, the rotation and the constant tables of EVMLean's file are `private`;
`keccak_private%` names them, so that their definitions can be unfolded (`lane_eq` and the
rest, each by `rfl`), and `unfold_keccak_private` unfolds them in a goal.  Then one `simp`
unrolls the loops, and each of the 25 lanes of both sides normalizes to the same term.  The
two elaborators exist only because EVMLean states no public lemmas about these definitions;
with such lemmas in EVMLean they can be deleted.
-/

namespace FeProofs.Keccak

open Lean Elab Term in
/-- A private definition of `Ethereum/SpongeHash/Keccak256.lean`, by its name. -/
elab "keccak_private%" n:ident : term => do
  mkConstWithLevelParams (Name.mkNum (`_private ++ `Ethereum.SpongeHash.Keccak256) 0 ++ n.getId)

open Lean Elab Tactic in
/-- Unfold private definitions of `Ethereum/SpongeHash/Keccak256.lean`, by their names. -/
elab "unfold_keccak_private" "[" ns:ident,* "]" : tactic => do
  for n in ns.getElems do
    let name := Name.mkNum (`_private ++ `Ethereum.SpongeHash.Keccak256) 0 ++ n.getId
    evalTactic (← `(tactic| unfold $(mkIdent name)))

open Ethereum

/-- EVMLean's rotation of a lane to the left. -/
def rotl (w : UInt64) (k : ℕ) : UInt64 :=
  if k = 0 then w else w.shiftLeft k.toUInt64 ||| w.shiftRight (64 - k).toUInt64

theorem lane_eq (s : Vector UInt64 25) (x y : ℕ) :
    (keccak_private% Ethereum.Keccak256.lane) s x y = s[(Fin.ofNat 25 (x + 5 * y) : Fin 25)] := rfl

theorem laneIndex_eq (x y : ℕ) :
    (keccak_private% Ethereum.Keccak256.laneIndex) x y = Fin.ofNat 25 (x + 5 * y) := rfl

theorem rotationOffsets_eq : (keccak_private% Ethereum.Keccak256.rotationOffsets) =
    #v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56,
      14] := rfl

theorem rotateLeft_eq : (keccak_private% Ethereum.Keccak256.rotateLeft) = rotl := rfl

/-- The 24 round constants. -/
def RC : List UInt64 :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

theorem roundConstants_eq : (keccak_private% Ethereum.Keccak256.roundConstants) = ⟨RC.toArray, rfl⟩ :=
  rfl

/-- One round of Keccak-f[1600] as fevm's `keccak_round` computes it: theta's column parities
`c` and deltas `d`, then rho and pi into `b`, then chi a row at a time, iota on lane 0. -/
def roundK (a : Vector UInt64 25) (rc : UInt64) : Vector UInt64 25 :=
  let c0 := a[0] ^^^ a[5] ^^^ a[10] ^^^ a[15] ^^^ a[20]
  let c1 := a[1] ^^^ a[6] ^^^ a[11] ^^^ a[16] ^^^ a[21]
  let c2 := a[2] ^^^ a[7] ^^^ a[12] ^^^ a[17] ^^^ a[22]
  let c3 := a[3] ^^^ a[8] ^^^ a[13] ^^^ a[18] ^^^ a[23]
  let c4 := a[4] ^^^ a[9] ^^^ a[14] ^^^ a[19] ^^^ a[24]
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := a[0] ^^^ d0
  let b1 := rotl (a[6] ^^^ d1) 44
  let b2 := rotl (a[12] ^^^ d2) 43
  let b3 := rotl (a[18] ^^^ d3) 21
  let b4 := rotl (a[24] ^^^ d4) 14
  let b5 := rotl (a[3] ^^^ d3) 28
  let b6 := rotl (a[9] ^^^ d4) 20
  let b7 := rotl (a[10] ^^^ d0) 3
  let b8 := rotl (a[16] ^^^ d1) 45
  let b9 := rotl (a[22] ^^^ d2) 61
  let b10 := rotl (a[1] ^^^ d1) 1
  let b11 := rotl (a[7] ^^^ d2) 6
  let b12 := rotl (a[13] ^^^ d3) 25
  let b13 := rotl (a[19] ^^^ d4) 8
  let b14 := rotl (a[20] ^^^ d0) 18
  let b15 := rotl (a[4] ^^^ d4) 27
  let b16 := rotl (a[5] ^^^ d0) 36
  let b17 := rotl (a[11] ^^^ d1) 10
  let b18 := rotl (a[17] ^^^ d2) 15
  let b19 := rotl (a[23] ^^^ d3) 56
  let b20 := rotl (a[2] ^^^ d2) 62
  let b21 := rotl (a[8] ^^^ d3) 55
  let b22 := rotl (a[14] ^^^ d4) 39
  let b23 := rotl (a[15] ^^^ d0) 41
  let b24 := rotl (a[21] ^^^ d1) 2
  #v[b0 ^^^ (~~~b1 &&& b2) ^^^ rc, b1 ^^^ (~~~b2 &&& b3), b2 ^^^ (~~~b3 &&& b4), b3 ^^^ (~~~b4 &&& b0), b4 ^^^ (~~~b0 &&& b1), b5 ^^^ (~~~b6 &&& b7), b6 ^^^ (~~~b7 &&& b8), b7 ^^^ (~~~b8 &&& b9), b8 ^^^ (~~~b9 &&& b5), b9 ^^^ (~~~b5 &&& b6), b10 ^^^ (~~~b11 &&& b12), b11 ^^^ (~~~b12 &&& b13), b12 ^^^ (~~~b13 &&& b14), b13 ^^^ (~~~b14 &&& b10), b14 ^^^ (~~~b10 &&& b11), b15 ^^^ (~~~b16 &&& b17), b16 ^^^ (~~~b17 &&& b18), b17 ^^^ (~~~b18 &&& b19), b18 ^^^ (~~~b19 &&& b15), b19 ^^^ (~~~b15 &&& b16), b20 ^^^ (~~~b21 &&& b22), b21 ^^^ (~~~b22 &&& b23), b22 ^^^ (~~~b23 &&& b24), b23 ^^^ (~~~b24 &&& b20), b24 ^^^ (~~~b20 &&& b21)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- **A round**: EVMLean's `round` is `roundK`. -/
theorem round_eq (s : Vector UInt64 25) (rc : UInt64) : Keccak256.round s rc = roundK s rc := by
  simp only [Keccak256.round, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, lane_eq, laneIndex_eq, rotationOffsets_eq, rotateLeft_eq]
  simp only [Id.run_pure, List.range', List.forIn_cons, List.forIn_nil, pure_bind, map_pure,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Fin.ofNat, Fin.getElem_fin]
  simp only [Vector.getElem_set, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.reduceEqDiff, ↓reduceIte]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp only [Vector.getElem_set, roundK, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceSub,
    Nat.reduceEqDiff, ↓reduceIte, rotl]

/-- **The permutation**: EVMLean's `permute` is `roundK` folded over the round constants. -/
theorem permute_eq (s : Vector UInt64 25) : Keccak256.permute s = RC.foldl roundK s := by
  simp only [Keccak256.permute, roundConstants_eq, round_eq, pure_bind, bind_pure,
    Vector.forIn_pure_yield_eq_foldl, Id.run_pure, Vector.foldl_mk, List.foldl_toArray']

end FeProofs.Keccak
