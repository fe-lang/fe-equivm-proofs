import Fe.EVM.Int

/-!
# Typed contract state

How a Fe value lies in storage or transient storage, as the compiler lays it out.

A scalar is read and written on one of two paths.  On the *word path* it has its slot to itself:
a write replaces the whole word, and a read takes the value from the low end of it.  On the
*lane path* it is some bytes of a slot, a `Lane`: the path of a struct or tuple field that packs
with its neighbours, or whose type is narrower than a word.  Which path an access takes is the
exporter's to say; it follows the compiler's choice, which depends on how the access names the
place and not only on the layout.

Aggregates have no definitions here: the exporter prints a load and a store function for each
struct, enum and array type it meets, from these.
-/

namespace Fe.EVM

open Ethereum

/-- The place `slots` slots after `p`.  Slot arithmetic wraps. -/
def Place.offset (p : Place) (slots : Nat) : Place :=
  { p with slot := p.slot + UInt256.ofNat slots }

/-- The place of element `index` of the array at `p`, whose elements take `stride` slots. -/
def Place.index (p : Place) (stride : Nat) (index : UInt256) : Place :=
  { p with slot := p.slot + index * UInt256.ofNat stride }

/-- The place at the same slot number of `space`: where a value pinned to `space` lies when its
    container lies in the other state space. -/
def Place.pin (p : Place) (space : Space) : Place := { p with space := space }

/-! ## The word path -/

/-- An integer with its slot to itself: the low bits of the word, at its type. -/
def loadInt (t : IntTy) (p : Place) : FeM UInt256 := do
  return IntTy.cast (.u 256) t (← load p)

/-- Store an integer over its whole slot: its bits at its own width, the rest zero. -/
def storeInt (t : IntTy) (p : Place) (v : UInt256) : FeM Unit :=
  store p (UInt256.ofNat (v.toNat % 2 ^ t.bits))

/-- A `bool` with its slot to itself is true unless the whole word is zero. -/
def loadBool (p : Place) : FeM Bool := do
  return decide ((← load p) ≠ UInt256.ofNat 0)

def storeBool (p : Place) (b : Bool) : FeM Unit := store p (Bool.toUInt256 b)

/-! ## The lane path -/

/-- The bytes of a slot that hold a packed value: `width` bytes from byte `off`, counted from the
    low end.  `shared` if other values lie in the slot, so that a write keeps the rest of it. -/
structure Lane where
  off : Nat
  width : Nat
  shared : Bool

namespace Lane

/-- The lane's bytes of the word `w`, as a number. -/
def get (l : Lane) (w : UInt256) : Nat := w.toNat / 2 ^ (8 * l.off) % 2 ^ (8 * l.width)

/-- The word `w` with the lane's bytes replaced by `bits`, a number below `2 ^ (8 * width)`. -/
def set (l : Lane) (w : UInt256) (bits : Nat) : UInt256 :=
  UInt256.ofNat (w.toNat - l.get w * 2 ^ (8 * l.off) + bits * 2 ^ (8 * l.off))

/-- The integer type of the lane's width with the signedness of `t`. -/
def ty (l : Lane) (t : IntTy) : IntTy :=
  match t with
  | .u _ => .u (8 * l.width)
  | .i _ => .i (8 * l.width)

/-- The bytes that hold `v` of type `t` in the lane.  A type wider than the lane must hold a value
    the lane can: otherwise the write reverts with no data. -/
def pack (l : Lane) (t : IntTy) (v : UInt256) : FeM Nat :=
  let bits := v.toNat % 2 ^ (8 * l.width)
  if 8 * l.width < t.bits ∧ IntTy.cast (.u 256) (l.ty t) (UInt256.ofNat bits) ≠ v then
    Fe.M.revert ByteArray.empty
  else
    pure bits

end Lane

/-- The word whose bytes are the given lanes' bytes, each a byte offset and the lane's bytes, and
    zero elsewhere: what a store of a whole struct writes to a slot its fields pack into. -/
def packed (lanes : List (Nat × Nat)) : UInt256 :=
  UInt256.ofNat (lanes.foldl (fun word (off, bits) => word + bits * 2 ^ (8 * off)) 0)

/-- An integer in a lane: the lane's bytes at the lane's width, sign-extended if `t` is signed. -/
def loadIntAt (t : IntTy) (p : Place) (l : Lane) : FeM UInt256 := do
  return IntTy.cast (.u 256) (l.ty t) (UInt256.ofNat (l.get (← load p)))

/-- Store an integer in a lane.  A shared slot keeps its other bytes; a lane alone in its slot
    zeroes them. -/
def storeIntAt (t : IntTy) (p : Place) (l : Lane) (v : UInt256) : FeM Unit := do
  let bits ← l.pack t v
  if l.shared then
    store p (l.set (← load p) bits)
  else
    store p (UInt256.ofNat (bits * 2 ^ (8 * l.off)))

/-- A `bool` in a lane is true unless its bytes are zero. -/
def loadBoolAt (p : Place) (l : Lane) : FeM Bool := do
  return decide (l.get (← load p) ≠ 0)

def storeBoolAt (p : Place) (l : Lane) (b : Bool) : FeM Unit :=
  storeIntAt (.u 8) p l (Bool.toUInt256 b)

/-! ## Enums and arrays -/

/-- The tag of the enum at `p`: the low `bits` bits of its first slot.  A tag that is no variant
    of the `count` is `Panic(0x21)`. -/
def loadTag (bits count : Nat) (p : Place) : FeM Nat := do
  let tag := (← load p).toNat % 2 ^ bits
  if tag < count then pure tag else Fe.M.panic 0x21

/-- The array of `n` elements at `p`, each of `stride` slots and read by `elem`, in index order. -/
def loadArray {α : Type} (stride : Nat) (elem : Place → FeM α) (p : Place) :
    (n : Nat) → FeM (Vector α n)
  | 0 => pure #v[]
  | n + 1 => do
    let init ← loadArray stride elem p n
    let last ← elem (p.offset (n * stride))
    pure (init.push last)

/-- Store an array at `p` element by element, in index order. -/
def storeArray {α : Type} [Inhabited α] {n : Nat} (stride : Nat) (elem : Place → α → FeM Unit)
    (p : Place) (v : Vector α n) : FeM Unit :=
  (List.range n).forM fun i => elem (p.offset (i * stride)) v[i]!

/-! ## Memory

Memory is addressed by the byte.  A scalar takes the bytes of its width, big-endian, and the
parts of an aggregate follow one another. -/

/-- The integer of type `t` at `ptr`: its bytes, big-endian. -/
def mloadInt (t : IntTy) (ptr : UInt256) : FeM UInt256 := do
  let bytes := (← get).memory.readWithPadding ptr.toNat (t.bits / 8)
  return IntTy.cast (.u 256) t (UInt256.ofNat (fromByteArrayBigEndian bytes))

/-- Write the integer `v` of type `t` at `ptr`: the low bytes of its word, big-endian. -/
def mstoreInt (t : IntTy) (ptr v : UInt256) : FeM Unit :=
  modify fun w =>
    { w with memory :=
        (v.toByteArray.extract (32 - t.bits / 8) 32).write 0 w.memory ptr.toNat (t.bits / 8) }

/-- A `bool` in memory is one byte, true unless it is zero. -/
def mloadBool (ptr : UInt256) : FeM Bool := do
  return decide (fromByteArrayBigEndian ((← get).memory.readWithPadding ptr.toNat 1) ≠ 0)

def mstoreBool (ptr : UInt256) (b : Bool) : FeM Unit := mstoreInt (.u 8) ptr (Bool.toUInt256 b)

/-- The array of `n` elements at `ptr`, each of `stride` bytes and read by `elem`, in index
    order. -/
def mloadArray {α : Type} (stride : Nat) (elem : UInt256 → FeM α) (ptr : UInt256) :
    (n : Nat) → FeM (Vector α n)
  | 0 => pure #v[]
  | n + 1 => do
    let init ← mloadArray stride elem ptr n
    let last ← elem (ptr + UInt256.ofNat (n * stride))
    pure (init.push last)

/-- Write an array at `ptr` element by element, in index order. -/
def mstoreArray {α : Type} [Inhabited α] {n : Nat} (stride : Nat) (elem : UInt256 → α → FeM Unit)
    (ptr : UInt256) (v : Vector α n) : FeM Unit :=
  (List.range n).forM fun i => elem (ptr + UInt256.ofNat (i * stride)) v[i]!

/-! ## Code

An immutable field lies in the running code as it would in memory. -/

/-- The integer of type `t` at `offset` of the running code: its bytes, big-endian. -/
def cloadInt (t : IntTy) (offset : UInt256) : FeM UInt256 := do
  let bytes := (← read).code.readWithPadding offset.toNat (t.bits / 8)
  return IntTy.cast (.u 256) t (UInt256.ofNat (fromByteArrayBigEndian bytes))

/-- A `bool` in the running code is one byte, true unless it is zero. -/
def cloadBool (offset : UInt256) : FeM Bool := do
  return decide (fromByteArrayBigEndian ((← read).code.readWithPadding offset.toNat 1) ≠ 0)

/-- The array of `n` elements at `offset` of the running code, each of `stride` bytes and read
    by `elem`, in index order. -/
def cloadArray {α : Type} (stride : Nat) (elem : UInt256 → FeM α) (offset : UInt256) :
    (n : Nat) → FeM (Vector α n)
  | 0 => pure #v[]
  | n + 1 => do
    let init ← cloadArray stride elem offset n
    let last ← elem (offset + UInt256.ofNat (n * stride))
    pure (init.push last)

/-- `clear` of a place of `slots` slots: every word zero. -/
def clearSlots (p : Place) (slots : Nat) : FeM Unit :=
  (List.range slots).forM fun i => store (p.offset i) (UInt256.ofNat 0)

/-- `__keccak_words(words)`: the hash of the words, each as 32 big-endian bytes, in order. -/
def keccakWords {n : Nat} (words : Vector UInt256 n) : UInt256 :=
  .ofNat (fromByteArrayBigEndian
    (KEC (words.toList.foldl (fun bytes word => bytes ++ word.toByteArray) ByteArray.empty)))

end Fe.EVM
