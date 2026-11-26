import Fe.Sonatina.Interp

/-!
# Words and the pure operations of the machine IR

The machine IR is SSA over `i256` values.  This module gives each pure operation of the machine
IR a function on words (`Nat` below `2 ^ 256`), written to reduce in the kernel, and proves it
equal to what `Interp.lean` computes for that instruction on `i256` operands:

- `Op1.eval`, `Op2.eval`, `Op3.eval`: the operations on words;
- `Op2.eval_eq_bin`, `Op2.eval_eq_cmp`, `Op1.eval_eq_*`, `Op3.eval_eq_*`: each equals the
  interpreter's `BinOp.eval`, `CmpOp.eval` (as the word `0` or `1`), or the inline
  computation of `runInst`, on operands below `2 ^ 256`;
- `PureInst`, `pureInst?`: the machine IR's pure instructions, and recognizing one;
- `runInst_pure`: `runInst` of a pure instruction whose operands evaluate to `i256` words
  returns the one value of the word function (`clz` only on Osaka, `runInst_clz`).

Operations of the machine instruction set that are not here: `evm_uaddsat`, `evm_saddsat`,
`evm_usubsat`, `evm_ssubsat`, `evm_umulsat`, `evm_smulsat`, `get_function_ptr`, `black_box`
(the Lean parser and interpreter have none of them), and `evm_keccak256` (it reads memory).
-/

namespace Fe.Sonatina.Steps.Schemas

open Ethereum
open private powAux from Ethereum.UInt256

/-- `2 ^ 256`: the words are the naturals below it. -/
abbrev W : Nat := 2 ^ 256

/-- The word with every bit set. -/
abbrev M : Nat := 2 ^ 256 - 1

/-- `omega` after unfolding `W` and `M`. -/
macro "womega" : tactic => `(tactic| (try simp only [W, M] at *) <;> omega)

/-- A boolean as the word `1` or `0`, as `bool` and `Val.as` make a comparison's result. -/
def ofBool (b : Bool) : Nat := if b then 1 else 0

/-- The pure unary operations of the machine IR. -/
inductive Op1 where
  | not | isZero | clz
  deriving DecidableEq, Repr, Inhabited

/-- The pure binary operations of the machine IR.  `udiv`, `sdiv`, `umod`, `smod` are the EVM
    forms (`evm_udiv` …), which give zero for a zero divisor; the shifts take the amount
    first; `byte` and `signextend` take the index first. -/
inductive Op2 where
  | add | sub | mul | udiv | sdiv | umod | smod | exp
  | shl | shr | sar | and | or | xor | byte | signextend
  | lt | gt | slt | sgt | eq
  deriving DecidableEq, Repr, Inhabited

/-- The pure ternary operations of the machine IR: `evm_add_mod`, `evm_mul_mod`. -/
inductive Op3 where
  | addmod | mulmod
  deriving DecidableEq, Repr, Inhabited

/-! ## The operations on words -/

/-- `shr`: zero for an amount of 256 or more. -/
def shrW (s y : Nat) : Nat := if 256 ≤ s then 0 else y >>> s

/-- `shl`: zero for an amount of 256 or more. -/
def shlW (s y : Nat) : Nat := if 256 ≤ s then 0 else (y <<< s) % W

/-- `sar`: a negative word shifts in ones, as the complement of the complement shifted. -/
def sarW (s y : Nat) : Nat := if y < 2 ^ 255 then shrW s y else M - shrW s (M - y)

/-- `evm_sdiv`: truncating division of the two's complement integers, zero for a zero divisor. -/
def sdivW (x y : Nat) : Nat := if y = 0 then 0 else wrap 256 ((signed 256 x).tdiv (signed 256 y))

/-- `evm_smod`: the remainder of truncating division, with the dividend's sign. -/
def smodW (x y : Nat) : Nat := if y = 0 then 0 else wrap 256 ((signed 256 x).tmod (signed 256 y))

/-- `evm_byte i y`: byte `i` of `y`, counting from the most significant; zero for `i > 31`. -/
def byteW (i y : Nat) : Nat := if 31 < i then 0 else (y >>> ((31 - i) * 8)) &&& 255

/-- `evm_signextend b y`: `y` sign-extended from bit `8 b + 7`; `y` itself for `b > 31`. -/
def signextendW (b y : Nat) : Nat :=
  if b ≤ 31 then
    if y &&& 2 ^ (8 * b + 7) ≠ 0 then y ||| (W - 2 ^ (8 * b + 7))
    else y &&& (2 ^ (8 * b + 7) - 1)
  else y

/-- Square-and-multiply modulo `2 ^ 256`, one step per bit of the exponent. -/
def expLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, b, e, acc => expLoop n (b * b % W) (e / 2) (if e % 2 = 1 then acc * b % W else acc)

/-- `evm_exp`: `b ^ e` modulo `2 ^ 256`. -/
def expW (b e : Nat) : Nat := expLoop 256 (b % W) e 1

/-- `clz`: the zero bits above the highest set bit; 256 for zero. -/
def clzW (x : Nat) : Nat := if x = 0 then 256 else 255 - x.log2

/-- `evm_add_mod`, `evm_mul_mod` without wrapping, zero for a zero modulus. -/
def addmodW (a b m : Nat) : Nat := if m = 0 then 0 else (a + b) % m

def mulmodW (a b m : Nat) : Nat := if m = 0 then 0 else (a * b) % m

def Op1.eval : Op1 → Nat → Nat
  | .not, x => M - x
  | .isZero, x => ofBool (x == 0)
  | .clz, x => clzW x

def Op2.eval : Op2 → Nat → Nat → Nat
  | .add, x, y => (x + y) % W
  | .sub, x, y => (x + (W - y)) % W
  | .mul, x, y => (x * y) % W
  | .udiv, x, y => if y = 0 then 0 else x / y
  | .sdiv, x, y => sdivW x y
  | .umod, x, y => if y = 0 then 0 else x % y
  | .smod, x, y => smodW x y
  | .exp, x, y => expW x y
  | .shl, x, y => shlW x y
  | .shr, x, y => shrW x y
  | .sar, x, y => sarW x y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .byte, x, y => byteW x y
  | .signextend, x, y => signextendW x y
  | .lt, x, y => ofBool (decide (x < y))
  | .gt, x, y => ofBool (decide (y < x))
  | .slt, x, y => ofBool (decide (signed 256 x < signed 256 y))
  | .sgt, x, y => ofBool (decide (signed 256 y < signed 256 x))
  | .eq, x, y => ofBool (x == y)

def Op3.eval : Op3 → Nat → Nat → Nat → Nat
  | .addmod, a, b, m => addmodW a b m
  | .mulmod, a, b, m => mulmodW a b m

/-! ## Bounds -/

theorem ofBool_lt (b : Bool) : ofBool b < W := by unfold ofBool; split <;> decide

theorem wrap_lt (n : Int) : wrap 256 n < W := by
  unfold wrap
  have h1 : 0 ≤ n % (2 ^ 256 : Int) := Int.emod_nonneg _ (by decide)
  have h2 : n % (2 ^ 256 : Int) < 2 ^ 256 := Int.emod_lt_of_pos _ (by decide)
  show _ < 2 ^ 256
  omega

theorem shrW_le (s y : Nat) : shrW s y ≤ y := by
  unfold shrW; split
  · exact Nat.zero_le _
  · rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _

theorem expLoop_lt {n b e acc : Nat} (h : acc < W) : expLoop n b e acc < W := by
  induction n generalizing b e acc with
  | zero => exact h
  | succ n ih =>
    unfold expLoop; apply ih; split
    · exact Nat.mod_lt _ (by decide)
    · exact h

theorem Op1.eval_lt (o : Op1) {x : Nat} (hx : x < W) : o.eval x < W := by
  cases o with
  | not => simp only [Op1.eval]; womega
  | isZero => exact ofBool_lt _
  | clz => simp only [Op1.eval, clzW]; split <;> womega

theorem Op2.eval_lt (o : Op2) {x y : Nat} (hx : x < W) (hy : y < W) : o.eval x y < W := by
  cases o <;> simp only [Op2.eval]
  all_goals try first
    | exact Nat.mod_lt _ (by decide)
    | exact ofBool_lt _
  case udiv =>
    split
    · decide
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
  case umod =>
    split
    · decide
    · exact lt_of_le_of_lt (Nat.mod_le _ _) hx
  case sdiv =>
    unfold sdivW; split
    · decide
    · exact wrap_lt _
  case smod =>
    unfold smodW; split
    · decide
    · exact wrap_lt _
  case exp => exact expLoop_lt (by decide)
  case shl =>
    unfold shlW; split
    · decide
    · exact Nat.mod_lt _ (by decide)
  case shr => exact lt_of_le_of_lt (shrW_le _ _) hy
  case sar =>
    unfold sarW; split
    · exact lt_of_le_of_lt (shrW_le _ _) hy
    · womega
  case and => exact Nat.and_lt_two_pow _ hy
  case or => exact Nat.or_lt_two_pow hx hy
  case xor => exact Nat.xor_lt_two_pow hx hy
  case byte =>
    unfold byteW; split
    · decide
    · exact Nat.and_lt_two_pow _ (n := 256) (by decide)
  case signextend =>
    unfold signextendW; split
    · split
      · have := Nat.two_pow_pos (8 * x + 7)
        exact Nat.or_lt_two_pow hy (by womega)
      · exact Nat.and_lt_two_pow _ (lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.pow_lt_pow_right (by decide) (by omega)))
    · exact hy

theorem Op3.eval_lt (o : Op3) {a b m : Nat} (hm : m < W) : o.eval a b m < W := by
  cases o <;> simp only [Op3.eval, addmodW, mulmodW] <;> split
  all_goals first | decide | exact lt_trans (Nat.mod_lt _ (by womega)) hm

/-! ## The interpreter's operations on `i256` operands -/

theorem wrap_natCast (n : Nat) : wrap 256 (n : Int) = n % W := by
  unfold wrap
  rw [show (2 : Int) ^ 256 = ((W : Nat) : Int) by norm_num, ← Int.natCast_emod, Int.toNat_natCast]

theorem wrap_sub {x y : Nat} (hy : y < W) : wrap 256 ((x : Int) - y) = (x + (W - y)) % W := by
  rw [← wrap_natCast]; unfold wrap; congr 1; simp only [W] at *; omega

theorem mul_pow_mod (X Y m : Nat) : X * (Y % W) ^ m % W = X * Y ^ m % W := by
  rw [← Nat.mul_mod_mod, ← Nat.pow_mod, Nat.mul_mod_mod]

/-- `expLoop` computes `acc * b ^ e` modulo `2 ^ 256` for an exponent below `2 ^ n`. -/
theorem expLoop_eq {n b e acc : Nat} (he : e < 2 ^ n) (hacc : acc < W) :
    expLoop n b e acc = acc * b ^ e % W := by
  induction n generalizing b e acc with
  | zero =>
    have : e = 0 := by omega
    subst this; simp [expLoop, Nat.mod_eq_of_lt hacc]
  | succ n ih =>
    unfold expLoop
    have he' : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    rw [ih he' (by split <;> first | exact Nat.mod_lt _ (by decide) | exact hacc), hsplit,
      mul_pow_mod]
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · simp only [h, Nat.zero_ne_one, ite_false, Nat.pow_zero, Nat.mul_one]
    · simp only [h, ite_true, Nat.pow_one]
      rw [Nat.mod_mul_mod]; congr 1; ring

theorem expW_eq {b e : Nat} (he : e < W) : expW b e = b ^ e % W := by
  unfold expW; rw [expLoop_eq he (by decide), Nat.one_mul, ← Nat.pow_mod]

theorem size_eq : UInt256.size = W := by decide

theorem toNat_ofNat (n : Nat) : (UInt256.ofNat n).toNat = n % W := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, size_eq]

theorem toNat_lt (u : UInt256) : u.toNat < W := lt_of_lt_of_eq u.val.isLt size_eq

theorem toNat_mul (a b : UInt256) : (a * b).toNat = a.toNat * b.toNat % W := by
  show (UInt256.mul a b).toNat = _
  simp [UInt256.mul, UInt256.toNat, Fin.val_mul, size_eq]

theorem toNat_mk_one : (⟨1⟩ : UInt256).toNat = 1 := rfl

theorem powAux_toNat (a c : UInt256) (n : Nat) :
    (powAux a c n).toNat = a.toNat * c.toNat ^ n % W := by
  induction n using Nat.strong_induction_on generalizing a c with
  | _ n ih =>
    rcases n with _ | k
    · rw [powAux, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (toNat_lt a)]
    · rw [powAux]
      have hlt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (by omega) (by decide)
      have hsplit : c.toNat ^ (k + 1) =
          (c.toNat * c.toNat) ^ ((k + 1) / 2) * c.toNat ^ ((k + 1) % 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
      split
      · next h =>
        have h1 : (k + 1) % 2 = 1 := by simpa using h
        rw [ih _ hlt, toNat_mul, toNat_mul, hsplit, h1, Nat.pow_one, mul_pow_mod,
          Nat.mod_mul_mod]
        congr 1; ring
      · next h =>
        have h0 : (k + 1) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k + 1) with h' | h'
          · exact h'
          · exact absurd (by simp [h']) h
        rw [ih _ hlt, toNat_mul, hsplit, h0, Nat.pow_zero, Nat.mul_one, mul_pow_mod]

theorem exp_toNat (b e : UInt256) : (UInt256.exp b e).toNat = b.toNat ^ e.toNat % W := by
  unfold UInt256.exp UInt256.pow
  rw [powAux_toNat, toNat_mk_one, Nat.one_mul]; rfl

theorem eval_exp {x y : Nat} (hx : x < W) (hy : y < W) :
    BinOp.eval .evmExp 256 x y = Op2.eval .exp x y := by
  simp only [BinOp.eval, Op2.eval]
  rw [exp_toNat, toNat_ofNat, toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, expW_eq hy]

theorem toNat_land (a b : UInt256) : (a &&& b).toNat = a.toNat &&& b.toNat := by
  show (UInt256.land a b).toNat = _
  simp only [UInt256.land, UInt256.toNat, Fin.land, size_eq]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (toNat_lt b))

theorem toNat_lor (a b : UInt256) : (a ||| b).toNat = a.toNat ||| b.toNat := by
  show (UInt256.lor a b).toNat = _
  simp only [UInt256.lor, UInt256.toNat, Fin.lor, size_eq]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (toNat_lt a) (toNat_lt b))

theorem fin256_le_iff (b : UInt256) : (256 : Fin UInt256.size) ≤ b.val ↔ 256 ≤ b.toNat :=
  Fin.le_def.trans (by rfl)

theorem toNat_shiftRight (a b : UInt256) :
    (a >>> b).toNat = shrW b.toNat a.toNat := by
  show (UInt256.shiftRight a b).toNat = _
  unfold UInt256.shiftRight shrW
  by_cases h : 256 ≤ b.toNat
  · rw [if_pos ((fin256_le_iff b).mpr h), if_pos h]; rfl
  · rw [if_neg (mt (fin256_le_iff b).mp h), if_neg h]
    rw [show ((⟨a.val >>> b.val⟩ : UInt256)).toNat = (a.toNat >>> b.toNat) % UInt256.size from rfl]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt
      (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) a.val.isLt)

theorem toNat_shiftLeft (a b : UInt256) :
    (a <<< b).toNat = shlW b.toNat a.toNat := by
  show (UInt256.shiftLeft a b).toNat = _
  unfold UInt256.shiftLeft shlW
  by_cases h : 256 ≤ b.toNat
  · rw [if_pos ((fin256_le_iff b).mpr h), if_pos h]; rfl
  · rw [if_neg (mt (fin256_le_iff b).mp h), if_neg h]
    rw [show ((⟨a.val <<< b.val⟩ : UInt256)).toNat = (a.toNat <<< b.toNat) % UInt256.size from rfl,
      size_eq]

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (a.toNat + (W - b.toNat)) % W := by
  show (UInt256.sub a b).toNat = _
  simp only [UInt256.sub, UInt256.toNat, Fin.sub_def, size_eq]
  rw [Nat.add_comm]

theorem eq_zero_iff (u : UInt256) : u = ⟨0⟩ ↔ u.toNat = 0 := by
  rcases u with ⟨v⟩
  simp only [UInt256.mk.injEq, UInt256.toNat, Fin.ext_iff]
  exact Iff.rfl

theorem toNat_ofNat_of_lt {n : Nat} (h : n < W) : (UInt256.ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

theorem byteAt_toNat {x y : Nat} (hx : x < W) (hy : y < W) :
    (UInt256.byteAt (UInt256.ofNat x) (UInt256.ofNat y)).toNat = byteW x y := by
  unfold UInt256.byteAt byteW
  have hx' := toNat_ofNat_of_lt hx
  have hy' := toNat_ofNat_of_lt hy
  have hc : (⟨31⟩ : UInt256) < UInt256.ofNat x ↔ 31 < x := by
    show (31 : Fin UInt256.size).val < (UInt256.ofNat x).val.val ↔ _
    rw [show (UInt256.ofNat x).val.val = x from hx']; exact Iff.rfl
  by_cases h : 31 < x
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (mt hc.mp h), if_neg h, toNat_land, toNat_shiftRight, hy', hx']
    have hs : (31 - x) * 8 < 256 := by omega
    rw [toNat_ofNat_of_lt (lt_trans hs (by decide)), shrW, if_neg (by omega)]
    rfl

theorem signextend_toNat {x y : Nat} (hx : x < W) (hy : y < W) :
    (UInt256.signextend (UInt256.ofNat x) (UInt256.ofNat y)).toNat = signextendW x y := by
  have hx' := toNat_ofNat_of_lt hx
  have hy' := toNat_ofNat_of_lt hy
  unfold UInt256.signextend signextendW
  rw [hx']
  by_cases hle : x ≤ 31
  · rw [if_pos hle, if_pos hle]
    have ht : (UInt256.ofNat x * ⟨8⟩ + ⟨7⟩).toNat = 8 * x + 7 := by
      show (UInt256.add (UInt256.mul (UInt256.ofNat x) ⟨8⟩) ⟨7⟩).toNat = _
      simp only [UInt256.add, UInt256.mul, UInt256.toNat, Fin.val_add, Fin.val_mul, size_eq]
      rw [show (UInt256.ofNat x).val.val = x from hx']
      show (x * 8 % W + 7) % W = 8 * x + 7
      rw [Nat.mod_eq_of_lt (by womega : x * 8 < W), Nat.mod_eq_of_lt (by womega)]; ring
    have hsmall : 2 ^ (8 * x + 7) < W := Nat.pow_lt_pow_right (by decide) (by omega)
    have hpos := Nat.two_pow_pos (8 * x + 7)
    have hsign : (⟨1⟩ <<< (UInt256.ofNat x * ⟨8⟩ + ⟨7⟩) : UInt256).toNat = 2 ^ (8 * x + 7) := by
      rw [toNat_shiftLeft, ht, shlW, if_neg (by omega), toNat_mk_one, Nat.shiftLeft_eq,
        Nat.one_mul]
      exact Nat.mod_eq_of_lt hsmall
    have hcond : (UInt256.ofNat y &&& ⟨1⟩ <<< (UInt256.ofNat x * ⟨8⟩ + ⟨7⟩) ≠ ⟨0⟩) ↔
        y &&& 2 ^ (8 * x + 7) ≠ 0 := by
      rw [ne_eq, eq_zero_iff, toNat_land, hy', hsign]
    have h0 : (UInt256.size.toUInt256).toNat = 0 := by
      show (UInt256.ofNat UInt256.size).toNat = 0
      rw [toNat_ofNat, size_eq, Nat.mod_self]
    have hW : 0 < W := by decide
    by_cases hb : y &&& 2 ^ (8 * x + 7) ≠ 0
    · rw [if_pos (hcond.mpr hb), if_pos hb, toNat_lor, hy', toNat_sub, hsign, h0, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg (mt hcond.mp hb), if_neg hb, toNat_land, hy', toNat_sub, hsign, toNat_mk_one]
      have : (2 ^ (8 * x + 7) + (W - 1)) % W = 2 ^ (8 * x + 7) - 1 := by
        rw [show 2 ^ (8 * x + 7) + (W - 1) = (2 ^ (8 * x + 7) - 1) + 1 * W by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [this]
    
  · rw [if_neg hle, if_neg hle, hy']

theorem eq0_false {m : Nat} (hm : m < W) (h : m ≠ 0) : (UInt256.ofNat m).eq0 = false := by
  unfold UInt256.eq0
  rw [beq_eq_false_iff_ne, ne_eq, eq_zero_iff, toNat_ofNat_of_lt hm]
  exact h

theorem addMod_toNat {a b m : Nat} (ha : a < W) (hb : b < W) (hm : m < W) :
    (UInt256.addMod (UInt256.ofNat a) (UInt256.ofNat b) (UInt256.ofNat m)).toNat =
      addmodW a b m := by
  have ha' : (UInt256.ofNat a).val.val = a := toNat_ofNat_of_lt ha
  have hb' : (UInt256.ofNat b).val.val = b := toNat_ofNat_of_lt hb
  unfold UInt256.addMod addmodW
  by_cases h : m = 0
  · subst h; rfl
  · rw [eq0_false hm h, if_neg h]
    simp only [Bool.false_eq_true, ite_false]
    rw [toNat_ofNat, ha', hb', toNat_ofNat_of_lt hm]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) hm)

theorem mulMod_toNat {a b m : Nat} (ha : a < W) (hb : b < W) (hm : m < W) :
    (UInt256.mulMod (UInt256.ofNat a) (UInt256.ofNat b) (UInt256.ofNat m)).toNat =
      mulmodW a b m := by
  have ha' : (UInt256.ofNat a).val.val = a := toNat_ofNat_of_lt ha
  have hb' : (UInt256.ofNat b).val.val = b := toNat_ofNat_of_lt hb
  unfold UInt256.mulMod mulmodW
  by_cases h : m = 0
  · subst h; rfl
  · rw [eq0_false hm h, if_neg h]
    simp only [Bool.false_eq_true, ite_false]
    rw [toNat_ofNat, ha', hb', toNat_ofNat_of_lt hm]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) hm)

theorem two_pow_255 : (2 : Nat) ^ (256 - 1) = 2 ^ 255 := rfl

theorem signed_of_lt {y : Nat} (h : y < 2 ^ 255) : signed 256 y = y := by
  simp only [signed, two_pow_255, if_pos h]

theorem signed_of_ge {y : Nat} (h : ¬ y < 2 ^ 255) : signed 256 y = (y : Int) - 2 ^ 256 := by
  simp only [signed, two_pow_255, if_neg h]

theorem sar_eq {s y : Nat} (hy : y < W) : BinOp.eval .sar 256 s y = sarW s y := by
  simp only [BinOp.eval, sarW, shrW]
  by_cases hneg : y < 2 ^ 255
  · rw [signed_of_lt hneg, if_pos hneg]
    by_cases hs : s ≥ 256
    · rw [if_pos hs, if_pos hs, if_neg (by omega)]
    · rw [if_neg hs, if_neg (by omega), Nat.shiftRight_eq_div_pow]
      rw [show ((y : Int) / 2 ^ s) = ((y / 2 ^ s : Nat) : Int) by push_cast; rfl, wrap_natCast]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hy)
  · rw [signed_of_ge hneg, if_neg hneg]
    by_cases hs : s ≥ 256
    · rw [if_pos hs, if_pos hs, if_pos (by womega)]; rfl
    · rw [if_neg hs, if_neg (by omega), Nat.shiftRight_eq_div_pow]
      have hz : (y : Int) - 2 ^ 256 = Int.negSucc (M - y) := by rw [Int.negSucc_eq]; womega
      rw [hz, Int.negSucc_ediv _ (by positivity)]
      have hq : (M - y) / 2 ^ s ≤ M - y := Nat.div_le_self _ _
      have hc : ((M - y : Nat) : Int).ediv (2 ^ s) = (((M - y) / 2 ^ s : Nat) : Int) := by
        push_cast; rfl
      rw [hc]
      unfold wrap
      generalize (M - y) / 2 ^ s = q at hq ⊢
      womega

/-- The interpreter's binary operation of an `Op2` that is not a comparison. -/
def Op2.binOp? : Op2 → Option BinOp
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .udiv => some .evmUdiv | .sdiv => some .evmSdiv | .umod => some .evmUmod
  | .smod => some .evmSmod | .exp => some .evmExp
  | .shl => some .shl | .shr => some .shr | .sar => some .sar
  | .and => some .and | .or => some .or | .xor => some .xor
  | .byte => some .evmByte | .signextend => some .evmSignExtend
  | .lt | .gt | .slt | .sgt | .eq => none

/-- The interpreter's comparison of an `Op2` that is one. -/
def Op2.cmpOp? : Op2 → Option CmpOp
  | .lt => some .lt | .gt => some .gt | .slt => some .slt | .sgt => some .sgt | .eq => some .eq
  | _ => none

/-- Each binary operation that is not a comparison is the interpreter's on `i256` words. -/
theorem Op2.eval_eq_bin {o : Op2} {op : BinOp} (h : o.binOp? = some op) {x y : Nat}
    (hx : x < W) (hy : y < W) : BinOp.eval op 256 x y = o.eval x y := by
  cases o <;> simp only [Op2.binOp?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  case add => simp only [BinOp.eval, Op2.eval]; exact_mod_cast wrap_natCast (x + y)
  case sub => exact wrap_sub hy
  case mul => simp only [BinOp.eval, Op2.eval]; exact_mod_cast wrap_natCast (x * y)
  case udiv => rfl
  case umod => rfl
  case sdiv => rfl
  case smod => rfl
  case exp => exact eval_exp hx hy
  case shl => simp only [BinOp.eval, Op2.eval, shlW, wrap_natCast]
  case shr => rfl
  case sar => exact sar_eq hy
  case and => rfl
  case or => rfl
  case xor => rfl
  case byte =>
    simp only [BinOp.eval, Op2.eval]
    exact byteAt_toNat hx hy
  case signextend =>
    simp only [BinOp.eval, Op2.eval]
    exact signextend_toNat hx hy

/-- The interpreter's value of an `Op2` on `i256` words, as `runInst` computes it. -/
def Op2.evalInterp (o : Op2) (x y : Nat) : Nat :=
  match o.binOp?, o.cmpOp? with
  | some op, _ => BinOp.eval op 256 x y
  | none, some op => ofBool (CmpOp.eval op 256 x y)
  | none, none => 0

/-- Each comparison is the interpreter's, as the word `0` or `1`. -/
theorem Op2.eval_eq_cmp {o : Op2} {op : CmpOp} (h : o.cmpOp? = some op) (x y : Nat) :
    ofBool (CmpOp.eval op 256 x y) = o.eval x y := by
  cases o <;> simp only [Op2.cmpOp?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem Op2.evalInterp_eq (o : Op2) {x y : Nat} (hx : x < W) (hy : y < W) :
    o.evalInterp x y = o.eval x y := by
  cases o <;> simp only [Op2.evalInterp, Op2.binOp?, Op2.cmpOp?]
  all_goals first
    | exact Op2.eval_eq_bin rfl hx hy
    | exact Op2.eval_eq_cmp rfl x y

theorem Op1.eval_not {x : Nat} : 2 ^ 256 - 1 - x = Op1.eval .not x := rfl

theorem Op1.eval_isZero (x : Nat) : ofBool (x == 0) = Op1.eval .isZero x := rfl

theorem Op1.eval_clz (x : Nat) : (if x = 0 then 256 else 256 - 1 - x.log2) = Op1.eval .clz x := rfl

/-- The EVM's `CLZ` (`UInt256.clz`) agrees with `clz` on words. -/
theorem Op1.eval_clz_evm {x : Nat} (hx : x < W) : (UInt256.clz (UInt256.ofNat x)).toNat = Op1.eval .clz x := by
  have hx' := toNat_ofNat_of_lt hx
  rw [show UInt256.clz (UInt256.ofNat x) = UInt256.ofNat (clzW x) by
    simp only [UInt256.clz, hx', clzW]]
  exact toNat_ofNat_of_lt (Op1.eval_lt .clz hx)

/-! ## Pure instructions -/

/-- A pure instruction of the machine IR, on its operands. -/
inductive PureInst where
  | op1 (o : Op1) (a : Operand)
  | op2 (o : Op2) (a b : Operand)
  | op3 (o : Op3) (a b c : Operand)
  deriving Repr

/-- The instruction of the interpreter's syntax. -/
def PureInst.toInst : PureInst → Inst
  | .op1 .not a => .not a
  | .op1 .isZero a => .isZero a
  | .op1 .clz a => .clz a
  | .op2 o a b => match o.binOp?, o.cmpOp? with
    | some op, _ => .bin op a b
    | none, some op => .cmp op a b
    | none, none => .bin .add a b
  | .op3 .addmod a b c => .evm .addMod [a, b, c]
  | .op3 .mulmod a b c => .evm .mulMod [a, b, c]

/-- The pure instruction an instruction of the machine IR is, if it is one.  The non-EVM
    division forms (`udiv` …) and the instructions outside the machine instruction set (`neg`,
    `ctz`, the casts, `ovf`, `select`, the other comparisons) are not. -/
def pureInst? : Inst → Option PureInst
  | .bin .add a b => some (.op2 .add a b)
  | .bin .sub a b => some (.op2 .sub a b)
  | .bin .mul a b => some (.op2 .mul a b)
  | .bin .evmUdiv a b => some (.op2 .udiv a b)
  | .bin .evmSdiv a b => some (.op2 .sdiv a b)
  | .bin .evmUmod a b => some (.op2 .umod a b)
  | .bin .evmSmod a b => some (.op2 .smod a b)
  | .bin .evmExp a b => some (.op2 .exp a b)
  | .bin .shl a b => some (.op2 .shl a b)
  | .bin .shr a b => some (.op2 .shr a b)
  | .bin .sar a b => some (.op2 .sar a b)
  | .bin .and a b => some (.op2 .and a b)
  | .bin .or a b => some (.op2 .or a b)
  | .bin .xor a b => some (.op2 .xor a b)
  | .bin .evmByte a b => some (.op2 .byte a b)
  | .bin .evmSignExtend a b => some (.op2 .signextend a b)
  | .cmp .lt a b => some (.op2 .lt a b)
  | .cmp .gt a b => some (.op2 .gt a b)
  | .cmp .slt a b => some (.op2 .slt a b)
  | .cmp .sgt a b => some (.op2 .sgt a b)
  | .cmp .eq a b => some (.op2 .eq a b)
  | .not a => some (.op1 .not a)
  | .isZero a => some (.op1 .isZero a)
  | .clz a => some (.op1 .clz a)
  | .evm .addMod [a, b, c] => some (.op3 .addmod a b c)
  | .evm .mulMod [a, b, c] => some (.op3 .mulmod a b c)
  | _ => none

theorem pureInst?_toInst {i : Inst} {p : PureInst} (h : pureInst? i = some p) : p.toInst = i := by
  unfold pureInst? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- The width of the value an operation's instruction gives: a comparison and `is_zero` give an
    `i1`, which `bind` makes the `i256` the machine IR declares (`Val.as`). -/
def PureInst.bits : PureInst → Nat
  | .op1 .isZero _ => 1
  | .op2 o _ _ => if o.cmpOp?.isSome then 1 else 256
  | _ => 256

/-- The word the operation gives on the words of its operands. -/
def PureInst.evalOn : PureInst → List Nat → Nat
  | .op1 o _, [x] => o.eval x
  | .op2 o _ _, [x, y] => o.eval x y
  | .op3 o _ _ _, [x, y, z] => o.eval x y z
  | _, _ => 0

def PureInst.args : PureInst → List Operand
  | .op1 _ a => [a]
  | .op2 _ a b => [a, b]
  | .op3 _ a b c => [a, b, c]

theorem Val.as_word {bits r : Nat} (hr : r < W) : (Val.int bits r).as (.int 256) = .int 256 r := by
  simp only [Val.as, Ty.bits, Nat.mod_eq_of_lt hr]

section Bridge

variable {c : Ctx} {env : Env}

/-- The operands of a pure instruction evaluate to `i256` words. -/
def ArgsAre (env : Env) (os : List Operand) (xs : List Nat) : Prop :=
  List.Forall₂ (fun o x => evalOperand env o = pure (.int 256 x) ∧ x < W) os xs

theorem evalInt_of {o : Operand} {x : Nat} (h : evalOperand env o = pure (.int 256 x)) :
    evalInt env o = pure (256, x) := by
  simp [evalInt, h]

theorem evalWord_of {o : Operand} {x : Nat} (h : evalOperand env o = pure (.int 256 x)) :
    evalWord env o = pure (UInt256.ofNat x) := by
  simp [evalWord, evalInt_of h]

theorem evalPair_of {a b : Operand} {x y : Nat} (ha : evalOperand env a = pure (.int 256 x))
    (hb : evalOperand env b = pure (.int 256 y)) : evalPair env a b = pure (256, x, y) := by
  simp [evalPair, evalInt_of ha, evalInt_of hb]

/-- A pure instruction other than `clz` whose operands evaluate to `i256` words gives the value
    of its word function, at the width of `PureInst.bits`; `bind` makes it the `i256` word
    (`Val.as_word`). -/
theorem runInst_pure {p : PureInst} (hclz : ∀ a, p ≠ .op1 .clz a) {xs : List Nat}
    (hargs : ArgsAre env p.args xs) :
    runInst c env p.toInst = pure [.int p.bits (p.evalOn xs)] := by
  rcases p with ⟨o, a⟩ | ⟨o, a, b⟩ | ⟨o, a, b, d⟩
  · simp only [PureInst.args, ArgsAre] at hargs
    rcases hargs with _ | ⟨⟨ha, hx⟩, hrest⟩
    cases hrest
    cases o
    · simp [PureInst.toInst, runInst, evalInt_of ha, PureInst.bits, PureInst.evalOn, Op1.eval, M]
    · simp [PureInst.toInst, runInst, evalInt_of ha, PureInst.bits, PureInst.evalOn, Op1.eval,
        ofBool, bool]
    · exact absurd rfl (hclz a)
  · simp only [PureInst.args, ArgsAre] at hargs
    rcases hargs with _ | ⟨⟨ha, hx⟩, _ | ⟨⟨hb, hy⟩, hrest⟩⟩
    cases hrest
    simp only [PureInst.evalOn]
    rw [← Op2.evalInterp_eq o hx hy]
    cases o <;> simp [PureInst.toInst, Op2.binOp?, Op2.cmpOp?, Op2.evalInterp, runInst,
      evalPair_of ha hb, PureInst.bits, bool, ofBool]
  · simp only [PureInst.args, ArgsAre] at hargs
    rcases hargs with _ | ⟨⟨ha, hx⟩, _ | ⟨⟨hb, hy⟩, _ | ⟨⟨hd, hz⟩, hrest⟩⟩⟩
    cases hrest
    cases o
    · simp [PureInst.toInst, runInst, evalWord_of ha, evalWord_of hb, evalWord_of hd, EvmOp.run,
        word, PureInst.bits, PureInst.evalOn, Op3.eval, addMod_toNat hx hy hz]
    · simp [PureInst.toInst, runInst, evalWord_of ha, evalWord_of hb, evalWord_of hd, EvmOp.run,
        word, PureInst.bits, PureInst.evalOn, Op3.eval, mulMod_toNat hx hy hz]

/-- `clz` on an `i256` word: its value on Osaka, a trap (the EVM's invalid instruction) before. -/
theorem runInst_clz {a : Operand} {x : Nat} (ha : evalOperand env a = pure (.int 256 x))
    (I : Fe.EVM.Env) (w : Fe.EVM.World) :
    (runInst c env (.clz a)).exec I w =
      if I.header.fork = .Osaka then some (.ok ([.int 256 (Op1.eval .clz x)], w))
      else some (.error .trap) := by
  simp only [runInst, evalInt_of ha, pure_bind]
  by_cases h : I.header.fork = .Osaka
  · simp [h, Fe.M.exec_bind, Op1.eval, clzW]
  · simp [h, Fe.M.exec_bind, Fe.EVM.trap, Fe.M.exec_fail]

end Bridge

end Fe.Sonatina.Steps.Schemas
