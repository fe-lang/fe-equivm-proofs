import Fe.Sonatina.Hints
import Reasoning.Memory

/-!
# Decoding bytes fast in the kernel

The checker is decided by the kernel, which runs EVMLean's `parseInstr`, a match on the byte,
by comparing the byte with each pattern in turn, and reads the byte at an offset by walking the
code to it.  `parseByte` reads the opcode from a table indexed by the byte's value instead
(`parseByte_eq`); `instrs` decodes the code in one pass, and `codeTree` keeps the instructions
in a search tree by offset, which the kernel builds once and reads in a few comparisons.
`codeTree_find`: what it finds is what `Hints.decodeAt` decodes.
-/

namespace Fe.Sonatina.Check

open Ethereum Ethereum.EVM

/-- The opcode of each byte, as `parseInstr` gives it. -/
def opTable : List (Option Operation) := [
    some (.StopArith .STOP), some (.StopArith .ADD), some (.StopArith .MUL), some (.StopArith .SUB),
    some (.StopArith .DIV), some (.StopArith .SDIV), some (.StopArith .MOD),
    some (.StopArith .SMOD), some (.StopArith .ADDMOD), some (.StopArith .MULMOD),
    some (.StopArith .EXP), some (.StopArith .SIGNEXTEND), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID), some (.CompBit .LT),
    some (.CompBit .GT), some (.CompBit .SLT), some (.CompBit .SGT), some (.CompBit .EQ),
    some (.CompBit .ISZERO), some (.CompBit .AND), some (.CompBit .OR), some (.CompBit .XOR),
    some (.CompBit .NOT), some (.CompBit .BYTE), some (.CompBit .SHL), some (.CompBit .SHR),
    some (.CompBit .SAR), some (.System .INVALID), some (.System .INVALID),
    some (.Keccak .KECCAK256), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.Env .ADDRESS), some (.Env .BALANCE), some (.Env .ORIGIN),
    some (.Env .CALLER), some (.Env .CALLVALUE), some (.Env .CALLDATALOAD),
    some (.Env .CALLDATASIZE), some (.Env .CALLDATACOPY), some (.Env .CODESIZE),
    some (.Env .CODECOPY), some (.Env .GASPRICE), some (.Env .EXTCODESIZE),
    some (.Env .EXTCODECOPY), some (.Env .RETURNDATASIZE), some (.Env .RETURNDATACOPY),
    some (.Env .EXTCODEHASH), some (.Block .BLOCKHASH), some (.Block .COINBASE),
    some (.Block .TIMESTAMP), some (.Block .NUMBER), some (.Block .PREVRANDAO),
    some (.Block .GASLIMIT), some (.Block .CHAINID), some (.Block .SELFBALANCE),
    some (.Block .BASEFEE), some (.Block .BLOBHASH), some (.Block .BLOBBASEFEE),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.StackMemFlow .POP),
    some (.StackMemFlow .MLOAD), some (.StackMemFlow .MSTORE), some (.StackMemFlow .MSTORE8),
    some (.StackMemFlow .SLOAD), some (.StackMemFlow .SSTORE), some (.StackMemFlow .JUMP),
    some (.StackMemFlow .JUMPI), some (.StackMemFlow .PC), some (.StackMemFlow .MSIZE),
    some (.StackMemFlow .GAS), some (.StackMemFlow .JUMPDEST), some (.StackMemFlow .TLOAD),
    some (.StackMemFlow .TSTORE), some (.StackMemFlow .MCOPY), some (.Push .PUSH0),
    some (.Push .PUSH1), some (.Push .PUSH2), some (.Push .PUSH3), some (.Push .PUSH4),
    some (.Push .PUSH5), some (.Push .PUSH6), some (.Push .PUSH7), some (.Push .PUSH8),
    some (.Push .PUSH9), some (.Push .PUSH10), some (.Push .PUSH11), some (.Push .PUSH12),
    some (.Push .PUSH13), some (.Push .PUSH14), some (.Push .PUSH15), some (.Push .PUSH16),
    some (.Push .PUSH17), some (.Push .PUSH18), some (.Push .PUSH19), some (.Push .PUSH20),
    some (.Push .PUSH21), some (.Push .PUSH22), some (.Push .PUSH23), some (.Push .PUSH24),
    some (.Push .PUSH25), some (.Push .PUSH26), some (.Push .PUSH27), some (.Push .PUSH28),
    some (.Push .PUSH29), some (.Push .PUSH30), some (.Push .PUSH31), some (.Push .PUSH32),
    some (.Dup .DUP1), some (.Dup .DUP2), some (.Dup .DUP3), some (.Dup .DUP4), some (.Dup .DUP5),
    some (.Dup .DUP6), some (.Dup .DUP7), some (.Dup .DUP8), some (.Dup .DUP9), some (.Dup .DUP10),
    some (.Dup .DUP11), some (.Dup .DUP12), some (.Dup .DUP13), some (.Dup .DUP14),
    some (.Dup .DUP15), some (.Dup .DUP16), some (.Exchange .SWAP1), some (.Exchange .SWAP2),
    some (.Exchange .SWAP3), some (.Exchange .SWAP4), some (.Exchange .SWAP5),
    some (.Exchange .SWAP6), some (.Exchange .SWAP7), some (.Exchange .SWAP8),
    some (.Exchange .SWAP9), some (.Exchange .SWAP10), some (.Exchange .SWAP11),
    some (.Exchange .SWAP12), some (.Exchange .SWAP13), some (.Exchange .SWAP14),
    some (.Exchange .SWAP15), some (.Exchange .SWAP16), some (.Log .LOG0), some (.Log .LOG1),
    some (.Log .LOG2), some (.Log .LOG3), some (.Log .LOG4), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .CREATE), some (.System .CALL),
    some (.System .CALLCODE), some (.System .RETURN), some (.System .DELEGATECALL),
    some (.System .CREATE2), some (.System .INVALID), some (.System .INVALID),
    some (.System .INVALID), some (.System .INVALID), some (.System .STATICCALL),
    some (.System .INVALID), some (.System .INVALID), some (.System .REVERT),
    some (.System .INVALID), some (.System .SELFDESTRUCT)
  ]

/-- `parseInstr`, read from `opTable`. -/
def parseByte (b : UInt8) : Option Operation := opTable.getD b.toNat none

set_option maxRecDepth 10000 in
theorem parseByte_eq : parseByte = parseInstr := by
  funext b
  have h : ∀ n < 256, parseByte (UInt8.ofNat n) = parseInstr (UInt8.ofNat n) := by decide +kernel
  have := h b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- The instructions of the bytes `bs`, which start at offset `i` of the code: each with its
    offset, its opcode, its immediate as `Hints.decodeAt` gives it, and where the next starts.
    At most `fuel` of them, in one pass over the bytes. -/
def instrs : Nat → List UInt8 → Nat → List (Nat × Operation × Option Nat × Nat)
  | 0, _, _ => []
  | _, [], _ => []
  | fuel + 1, b :: bs, i => match parseByte b with
    | none => []
    | some op =>
      let w := argOnNBytesOfInstr op
      let arg := if w == 0 then (if op == .PUSH0 then some 0 else none)
        else some (fromBytes' (bs.take w).reverse % UInt256.size)
      (i, op, arg, i + 1 + w) :: instrs fuel (bs.drop w) (i + 1 + w)

/-- `instrs` with the instructions so far in an accumulator, which the compiled code runs in its
    place (`instrs_eq_instrsTR`): a large section has more instructions than the stack frames
    `instrs` would take.  The kernel runs `instrs`. -/
def instrsTR (fuel : Nat) (bs : List UInt8) (i : Nat) :
    List (Nat × Operation × Option Nat × Nat) :=
  go fuel bs i #[]
where
  go : Nat → List UInt8 → Nat → Array (Nat × Operation × Option Nat × Nat) →
      List (Nat × Operation × Option Nat × Nat)
  | 0, _, _, acc | _, [], _, acc => acc.toList
  | fuel + 1, b :: bs, i, acc => match parseByte b with
    | none => acc.toList
    | some op =>
      let w := argOnNBytesOfInstr op
      let arg := if w == 0 then (if op == .PUSH0 then some 0 else none)
        else some (fromBytes' (bs.take w).reverse % UInt256.size)
      go fuel (bs.drop w) (i + 1 + w) (acc.push (i, op, arg, i + 1 + w))

theorem instrsTR_go : ∀ (fuel : Nat) (bs : List UInt8) (i : Nat) acc,
    instrsTR.go fuel bs i acc = acc.toList ++ instrs fuel bs i
  | 0, _, _, _ => by simp [instrsTR.go, instrs]
  | _ + 1, [], _, _ => by simp [instrsTR.go, instrs]
  | fuel + 1, b :: bs, i, acc => by
    unfold instrsTR.go instrs
    cases parseByte b with
    | none => simp
    | some op => simp [instrsTR_go fuel]

@[csimp] theorem instrs_eq_instrsTR : @instrs = @instrsTR := by
  funext fuel bs i
  simp [instrsTR, instrsTR_go]

/-- A search tree keyed by offsets. -/
inductive PcTree (α : Type) where
  | leaf
  | node (l : PcTree α) (pc : Nat) (v : α) (r : PcTree α)

/-- The tree of the first `n` entries of `xs`, balanced if they are sorted by offset, at most
    `depth` deep. -/
def PcTree.build {α : Type} : Nat → List (Nat × α) → Nat → PcTree α
  | 0, _, _ => .leaf
  | depth + 1, xs, n => if n = 0 then .leaf else
    match xs.drop (n / 2) with
    | [] => .leaf
    | (p, v) :: rest =>
      .node (build depth (xs.take (n / 2)) (n / 2)) p v (build depth rest (n - n / 2 - 1))

def PcTree.find {α : Type} : PcTree α → Nat → Option α
  | .leaf, _ => none
  | .node l p v r, q => if q < p then l.find q else if q = p then some v else r.find q

/-- The code's instructions, in one pass. -/
def codeInstrs (code : ByteArray) : List (Nat × Operation × Option Nat × Nat) :=
  instrs code.size code.data.toList 0

/-- The code's instructions by offset: the kernel reads one in a few comparisons, where
    `decode` reads the byte at the offset by walking the code to it. -/
def codeTree (code : ByteArray) : PcTree (Operation × Option Nat × Nat) :=
  .build 16 (codeInstrs code) (codeInstrs code).length

/-- The offsets of the code's `JUMPDEST`s. -/
def jumpdests (code : ByteArray) : List Nat :=
  (codeInstrs code).filterMap fun (pc, op, _) => if op == .JUMPDEST then some pc else none

/-! ## The tree finds what `decodeAt` decodes -/

theorem PcTree.mem_of_find {α : Type} {q : Nat} {v : α} :
    ∀ {t : PcTree α} {xs : List (Nat × α)} {n d : Nat}, t = .build d xs n → t.find q = some v →
      (q, v) ∈ xs
  | .leaf, _, _, _, _, h => by simp [find] at h
  | .node l p w r, xs, n, d, ht, h => by
    cases d with
    | zero => simp [build] at ht
    | succ d =>
      simp only [build] at ht
      split at ht
      · cases ht
      split at ht
      · cases ht
      next p' w' rest hdrop =>
      simp only [node.injEq] at ht
      obtain ⟨hl, rfl, rfl, hr⟩ := ht
      have hmem : (p, w) ∈ xs ∧ ∀ x ∈ rest, x ∈ xs := by
        refine ⟨?_, fun x hx => ?_⟩
        · exact List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_self ..)
        · exact List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_of_mem _ hx)
      simp only [find] at h
      split_ifs at h with h1 h2
      · exact List.mem_of_mem_take (mem_of_find hl h)
      · cases h; subst h2; exact hmem.1
      · exact hmem.2 _ (mem_of_find hr h)

theorem get?_drop (c : ByteArray) (i : Nat) : c.get? i = (c.data.toList.drop i).head? := by
  rw [List.head?_drop, Array.getElem?_toList]
  unfold ByteArray.get?
  split
  · next h => rw [Array.getElem?_eq_getElem h]; rfl
  · next h => rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem extract'_toList (a : ByteArray) (b e : Nat) :
    (a.extract' b e).data.toList = (a.data.toList.drop b).take (e - b) := by
  unfold ByteArray.extract'
  split
  · rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  · show List.take (e - b) (List.drop b a.toList) = _
    rw [Reasoning.Theory.byteArray_toList_eq]

/-- Each instruction of the one pass is the one `decodeAt` decodes at its offset. -/
theorem mem_instrs {c : ByteArray} (hc : c.size < UInt256.size) :
    ∀ (f i : Nat) (bs : List UInt8), bs = c.data.toList.drop i → ∀ pc d,
      (pc, d) ∈ instrs f bs i → Hints.decodeAt c pc = some d
  | 0, _, _, _, _, _, h => by simp [instrs] at h
  | _ + 1, _, [], _, _, _, h => by simp [instrs] at h
  | f + 1, i, b :: bs, hbs, pc, d, h => by
    have hlen : c.data.toList.length = c.size := Array.length_toList
    have hi : i < c.size := by
      by_contra hn
      rw [List.drop_eq_nil_of_le (by omega)] at hbs
      cases hbs
    have hrest : bs = c.data.toList.drop (i + 1) := by
      rw [← List.drop_drop, ← hbs, List.drop_one, List.tail_cons]
    unfold instrs at h
    cases hop : parseByte b with
    | none => simp only [hop] at h; cases h
    | some op =>
    simp only [hop] at h
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨hp, rfl⟩ := h
      rw [hp]
      have hget : c.get? i = some b := by rw [get?_drop, ← hbs]; rfl
      rw [parseByte_eq] at hop
      have hpc : (UInt256.ofNat i).toNat = i := Nat.mod_eq_of_lt (lt_trans hi hc)
      simp only [Hints.decodeAt, decode, hpc, hget, Option.bind_eq_bind, Option.bind_some, hop,
        Option.map_some]
      have hx : (c.extract' i.succ (i.succ + argOnNBytesOfInstr op)).data.toList =
          bs.take (argOnNBytesOfInstr op) := by
        rw [extract'_toList, ← hrest, Nat.succ_eq_add_one, Nat.add_sub_cancel_left]
      by_cases hw : argOnNBytesOfInstr op = 0
      · simp [hw]
      · simp only [hw, beq_iff_eq, if_false, Option.map_some, Option.orElse_some,
          Option.getD_some, Option.some.injEq, Prod.mk.injEq, and_true, true_and]
        show (fromBytes' (c.extract' _ _).data.toList.reverse) % UInt256.size = _
        rw [hx]
    · exact mem_instrs hc f _ _ (by rw [hrest, List.drop_drop]) pc d h

/-- An instruction the tree finds is the one `decodeAt` decodes. -/
theorem codeTree_find {c : ByteArray} {pc : Nat} {d : Operation × Option Nat × Nat}
    (hc : c.size < UInt256.size) (h : (codeTree c).find pc = some d) :
    Hints.decodeAt c pc = some d :=
  mem_instrs hc _ 0 _ (by simp) pc d (PcTree.mem_of_find rfl h)

end Fe.Sonatina.Check
