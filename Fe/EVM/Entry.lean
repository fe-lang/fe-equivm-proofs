import Fe.EVM.Refine
import Fe.EVM.Calls
import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Solc

/-!
# Reasoning about an exported runtime entry

Facts that proofs about `fe-lean-export`'s runtime entry share, whatever the contract: word
arithmetic the std decoder and encoder perform, the selector word, and how an entry that stops
relates to a hand-written one that returns.
-/

namespace Fe.EVM

open Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Words -/

theorem toNat0 : (UInt256.ofNat 0).toNat = 0 := rfl
theorem toNat4 : (UInt256.ofNat 4).toNat = 4 := rfl
theorem toNat32 : (UInt256.ofNat 32).toNat = 32 := rfl
theorem toNat64 : (UInt256.ofNat 64).toNat = 64 := rfl
theorem toNat96 : (UInt256.ofNat 96).toNat = 96 := rfl
theorem add0_32 : UInt256.ofNat 0 + UInt256.ofNat 32 = UInt256.ofNat 32 := rfl
theorem add32_32 : UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 := rfl
theorem add64_32 : UInt256.ofNat 64 + UInt256.ofNat 32 = UInt256.ofNat 96 := rfl
theorem ne32 : UInt256.ofNat 32 ≠ UInt256.ofNat 0 := by decide
theorem ne64 : UInt256.ofNat 64 ≠ UInt256.ofNat 0 := by decide
theorem ne96 : UInt256.ofNat 96 ≠ UInt256.ofNat 0 := by decide
theorem at4 : (UInt256.ofNat 0 + UInt256.ofNat 4).toNat = 4 := rfl
theorem at36 : (UInt256.ofNat 0 + (UInt256.ofNat 4 + UInt256.ofNat 32)).toNat = 36 := rfl
theorem toNat4_32 : (UInt256.ofNat 4 + UInt256.ofNat 32).toNat = 36 := rfl
theorem at68 :
    (UInt256.ofNat 0 + (UInt256.ofNat 4 + UInt256.ofNat 32 + UInt256.ofNat 32)).toNat = 68 := rfl
theorem toNatMax : (~~~UInt256.ofNat 0).toNat = UInt256.size - 1 := by decide
theorem toNatU64 : (UInt256.ofNat 18446744073709551615).toNat = 18446744073709551615 := rfl
theorem sub32_0 : (UInt256.ofNat 32 - UInt256.ofNat 0).toNat = 32 := rfl

theorem add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply u256_inj
  rw [uadd_toNat, toNat0, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

/-- A length below `2 ^ 64` survives std's cast to `u64`: minus the view's base 0, masked, then
    cut to 64 bits. -/
theorem truncate_size (n : Nat) (h : n < 2 ^ 64) :
    truncate 64 ((UInt256.ofNat n).sub (UInt256.ofNat 0) &&& UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat n := by
  have hn : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat n).sub (UInt256.ofNat 0) = UInt256.ofNat n := by
    apply u256_inj
    exact (usub_toNat (a := UInt256.ofNat n) (b := UInt256.ofNat 0) (Nat.zero_le _)).trans
      (Nat.sub_zero _)
  have hmask : (UInt256.ofNat 18446744073709551615).toNat = 2 ^ 64 - 1 := rfl
  have hand : (UInt256.ofNat n &&& UInt256.ofNat 18446744073709551615).toNat = n := by
    change (UInt256.land _ _).toNat = n
    rw [uland_toNat, hn, hmask]
    change Nat.land n (2 ^ 64 - 1) = n
    rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt h]
  rw [hsub]
  apply u256_inj
  unfold truncate
  rw [hand, Nat.mod_eq_of_lt h]

/-- Signed comparison of two words below `2 ^ 255` is comparison of their values. -/
theorem sltBool_small {a b : UInt256} (ha : a.toNat < 2 ^ 255) (hb : b.toNat < 2 ^ 255) :
    a.sltBool b = decide (a.toNat < b.toNat) := by
  unfold UInt256.sltBool
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

/-- Std's head check on calldata of `size` bytes, at least a selector and below `2 ^ 64`:
    `(size - 4) <s need`, signed, is `size - 4 < need`. -/
theorem headCheck {size need : Nat} (hlo : 4 ≤ size) (hfits : size < 2 ^ 64)
    (hneed : need < 2 ^ 64) :
    (UInt256.ofNat size - UInt256.ofNat 4).sltBool (UInt256.ofNat need) =
      decide (size - 4 < need) := by
  have hn : (UInt256.ofNat size).toNat = size := ulit_toNat' _ (by unfold UInt256.size; omega)
  have hm : (UInt256.ofNat need).toNat = need := ulit_toNat' _ (by unfold UInt256.size; omega)
  have hsub : (UInt256.ofNat size - UInt256.ofNat 4).toNat = size - 4 := by
    have h := usub_toNat (a := UInt256.ofNat size) (b := UInt256.ofNat 4) (by rw [hn, toNat4]; omega)
    rw [hn, toNat4] at h
    exact h
  rw [sltBool_small (by rw [hsub]; omega) (by rw [hm]; omega), hsub, hm]

/-! ## Memory after a return -/

/-- Memory after `return_value` encodes the word `v` into a fresh 32-byte buffer. -/
def returned (memory : ByteArray) (v : UInt256) : ByteArray :=
  v.toByteArray.write 0
    ((⟨Array.replicate 32 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 32 0⟩) memory.size 32)
    memory.size 32

/-- The word written into the fresh buffer reads back. -/
theorem returned_read (memory : ByteArray) (v : UInt256) :
    (v.toByteArray.write 0
        ((⟨Array.replicate 32 0⟩ : ByteArray).write 0 (memory ++ ⟨Array.replicate 32 0⟩)
          memory.size 32)
        memory.size 32).readWithPadding memory.size 32 = v.toByteArray := by
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  apply toByteArray_write32_read_back
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hzeros])
    (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]
  omega

theorem returned_size (memory : ByteArray) (v : UInt256) :
    (returned memory v).size = memory.size + 32 := by
  have hzeros : (⟨Array.replicate 32 0⟩ : ByteArray).size = 32 := rfl
  unfold returned
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
      (by rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [hzeros])
        (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]),
    byteArray_write_size_of_inBounds _ _ _ _ (by rw [hzeros])
      (by rw [ByteArray.size_append, hzeros]), ByteArray.size_append, hzeros]

/-! ## Memory past a known prefix

Exported code allocates fresh memory and writes into it, so its memory is a prefix `M` it does not
touch followed by a tail `T` whose bytes a proof tracks. -/

/-- A write of `n` bytes of `src` from `s` into the tail, at `k` bytes into it. -/
theorem write_tail (src M T : ByteArray) {d : ℕ} (s k n : ℕ) (hd : d = M.size + k) (hn : n ≠ 0)
    (hsrc : s + n ≤ src.size) (hk : k + n ≤ T.size) :
    src.write s (M ++ T) d n =
      M ++ (T.extract 0 k ++ src.extract s (s + n) ++ T.extract (k + n) T.size) := by
  subst hd
  rw [write_eq_gen_from src (M ++ T) s (M.size + k) n hn hsrc
      (by rw [ByteArray.size_append]; omega),
    extract_append_span _ _ _ _ (Nat.zero_le _) (by omega), byteArray_extract_self,
    extract_append_right_window _ _ _ _ (by omega), ByteArray.size_append,
    show M.size + k + n - M.size = k + n by omega, show M.size + T.size - M.size = T.size by omega,
    show M.size + k - M.size = k by omega, ByteArray.append_assoc, ByteArray.append_assoc,
    ByteArray.append_assoc]

/-- A read of `n` bytes of the tail, at `k` bytes into it. -/
theorem readWithPadding_tail (M T : ByteArray) {a : ℕ} (k n : ℕ) (ha : a = M.size + k)
    (hn : 0 < n) (hk : k + n ≤ T.size) :
    (M ++ T).readWithPadding a n = T.extract k (k + n) := by
  subst ha
  rw [readWithPadding_eq_extract_unbounded _ _ _ hn (by rw [ByteArray.size_append]; omega),
    extract_append_right_window _ _ _ _ (by omega), show M.size + k - M.size = k by omega,
    show M.size + k + n - M.size = k + n by omega]

/-- The size of `n` fresh zero bytes. -/
theorem zeros_size (n : ℕ) : (⟨Array.replicate n 0⟩ : ByteArray).size = n := by
  simp [ByteArray.size]

/-! ## A hashed pair of words -/

/-- Memory after two words are stored in a fresh 64-byte buffer: what std's `mapping_slot`
    leaves, the key and the root of the map it hashes. -/
def keyed (memory : ByteArray) (key root : UInt256) : ByteArray :=
  root.toByteArray.write 0
    (key.toByteArray.write 0 (memory ++ ⟨Array.replicate 64 0⟩) memory.size 32)
    (memory.size + 32) 32

private theorem keyed_first_size (memory : ByteArray) (key : UInt256) :
    (key.toByteArray.write 0 (memory ++ ⟨Array.replicate 64 0⟩) memory.size 32).size =
      memory.size + 64 := by
  have hzeros : (⟨Array.replicate 64 0⟩ : ByteArray).size = 64 := rfl
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by rw [ByteArray.size_append, hzeros]; omega), ByteArray.size_append, hzeros]

theorem keyed_size (memory : ByteArray) (key root : UInt256) :
    (keyed memory key root).size = memory.size + 64 := by
  unfold keyed
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size])
    (by rw [keyed_first_size]), keyed_first_size]

/-- The buffer reads back as the two words. -/
theorem keyed_read (memory : ByteArray) (key root : UInt256) :
    (keyed memory key root).readWithPadding memory.size 64 =
      key.toByteArray ++ root.toByteArray := by
  rw [show (64 : Nat) = 32 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide)
      (by rw [keyed_size])]
  unfold keyed
  rw [write32_read_below _ _ (memory.size + 32) memory.size (by rw [toByteArray_size])
      (by rw [keyed_first_size]; omega) (by omega),
    toByteArray_write32_read_back _ _ _ (by rw [ByteArray.size_append]; omega),
    toByteArray_write32_read_back _ _ _ (by rw [keyed_first_size]; omega)]

/-- The hash of the buffer is the slot of the map's entry: Solidity's mapping layout. -/
theorem keyed_slot (memory : ByteArray) (key root : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((keyed memory key root).readWithPadding memory.size 64))) = mapSlot key root := by
  rw [keyed_read]
  exact Reasoning.Theory.mappingSlot_single key root

/-- Memory after each pair of `pairs` is hashed in turn, each in its own fresh buffer: what the
    lookups of an arm leave. -/
def keyedAll (memory : ByteArray) : List (UInt256 × UInt256) → ByteArray
  | [] => memory
  | (key, root) :: rest => keyedAll (keyed memory key root) rest

@[simp] theorem keyedAll_nil (memory : ByteArray) : keyedAll memory [] = memory := rfl

@[simp] theorem keyedAll_cons (memory : ByteArray) (key root : UInt256)
    (rest : List (UInt256 × UInt256)) :
    keyedAll memory ((key, root) :: rest) = keyedAll (keyed memory key root) rest := rfl

theorem keyedAll_size (memory : ByteArray) (pairs : List (UInt256 × UInt256)) :
    (keyedAll memory pairs).size = memory.size + 64 * pairs.length := by
  induction pairs generalizing memory with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨key, root⟩ := pair
    rw [keyedAll_cons, ih, keyed_size, List.length_cons]
    omega

/-- An empty return ends the call with no data and changes nothing. -/
theorem returnNone_exec (I : ExecutionEnv) (w : World) :
    (returnData (UInt256.ofNat 0) (UInt256.ofNat 0)).exec I w =
      some (.error (.stop ByteArray.empty w)) := by
  simp [returnData, toNat0, byteArray_readWithPadding_zero]

/-! ## The selector -/

/-- The selector word: the first four bytes of calldata as a number. -/
abbrev selWord (cd : ByteArray) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩

theorem selector_exec (I : ExecutionEnv) (w : World) :
    calldataSelector.exec I w = some (.ok (selWord I.calldata, w)) := rfl

theorem selWord_hit {cd sel : ByteArray} {word : UInt256}
    (h : UInt256.eq word (selWord cd) = if (sel == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩)
    (hsel : (sel == cd.extract 0 4) = true) : selWord cd = word := by
  rw [hsel, if_pos rfl] at h
  by_contra hne
  rw [u256_eq_of_ne (fun e => hne e.symm)] at h
  exact absurd h (by decide)

theorem selWord_miss {cd sel : ByteArray} {word : UInt256}
    (h : UInt256.eq word (selWord cd) = if (sel == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩)
    (hsel : (sel == cd.extract 0 4) = false) : selWord cd ≠ word := by
  intro e
  rw [hsel, e, u256_eq_refl] at h
  exact absurd h (by decide)

/-! ## Entries -/

theorem entry_exec {m : FeM Empty} {I : ExecutionEnv} {w : World} {f : Exit World}
    (h : m.exec I w = some (.error f)) : (entry m).exec I w = some (.error f) := by
  simp [entry, h]

/-- With calldata below `2 ^ 64` bytes, std's head check is the one a hand-written entry makes. -/
theorem badHead_iff (cd : ByteArray) (words : Nat) (hfits : cd.size < 2 ^ 64) :
    BadHead cd words ↔ cd.size < 4 + 32 * words := by
  unfold BadHead
  constructor
  · rintro (h | h)
    · exact h
    · omega
  · exact Or.inl

/-- An entry that runs `arm` and returns its result through `ret` ends as a run of `arm` that
    returns the encoding `enc` of its result, when `ret` stops with that encoding and changes
    memory only, and `arm` leaves memory alone. -/
theorem endsAs_arm {α : Type} {arm : FeM α} {ret : α → FeM Empty} {enc : α → ByteArray}
    {I : ExecutionEnv} {w : World}
    (hret : ∀ r w', w'.memory.size + 32 < UInt256.size →
      ∃ memory, (ret r).exec I w' = some (.error (.stop (enc r) { w' with memory := memory })))
    (hkeep : KeepsMemory arm) (hmem : w.memory.size + 32 < UInt256.size) :
    EndsAs ((entry (arm >>= ret)).exec I w) ((arm >>= fun r => pure (enc r)).exec I w) := by
  cases h : arm.exec I w with
  | none => simp [entry, h]; exact .diverge
  | some res =>
    cases res with
    | error f => simp [entry, h]; exact .exit f
    | ok p =>
      obtain ⟨r, w'⟩ := p
      obtain ⟨memory, hr⟩ := hret r w' (by rw [hkeep I w r w' h]; exact hmem)
      simp [entry, h, hr]
      exact .stop_ok rfl rfl

/-! ## Runs alike up to memory -/

/-- Two runs from the world `w` end alike up to memory: both diverge, both exit the same way,
    or both return the same result with the same accounts and logs, the first having grown
    memory by at most `grow` bytes.  An exported arm that allocates relates this way to a
    hand-written one that does not. -/
inductive Alike {α : Type} (grow : Nat) (w : World) :
    Option (Except (Exit World) (α × World)) → Option (Except (Exit World) (α × World)) → Prop
  | ok {a : α} {v v' : World} (ha : v.accounts = v'.accounts) (hl : v.logs = v'.logs)
      (hm : v.memory.size ≤ w.memory.size + grow) :
      Alike grow w (some (.ok (a, v))) (some (.ok (a, v')))
  | exit (f : Exit World) : Alike grow w (some (.error f)) (some (.error f))
  | diverge : Alike grow w none none

/-- An outcome with the memory of the world it returns replaced by `memory`. -/
def withMemory {α : Type} (memory : ByteArray) :
    Option (Except (Exit World) (α × World)) → Option (Except (Exit World) (α × World))
  | some (.ok (a, v)) => some (.ok (a, { v with memory := memory }))
  | outcome => outcome

@[simp] theorem withMemory_ok {α : Type} (memory : ByteArray) (a : α) (v : World) :
    withMemory memory (some (.ok (a, v))) = some (.ok (a, { v with memory := memory })) := rfl

@[simp] theorem withMemory_error {α : Type} (memory : ByteArray) (f : Exit World) :
    withMemory (α := α) memory (some (.error f)) = some (.error f) := rfl

@[simp] theorem withMemory_none {α : Type} (memory : ByteArray) :
    withMemory (α := α) memory none = none := rfl

/-- A run that is another's with its memory replaced ends alike up to memory. -/
theorem alike_withMemory {α : Type} {grow : Nat} {w : World} {memory : ByteArray}
    {x y : Option (Except (Exit World) (α × World))} (h : x = withMemory memory y)
    (hm : memory.size ≤ w.memory.size + grow) : Alike grow w x y := by
  subst h
  match y with
  | none => exact .diverge
  | some (.error f) => exact .exit f
  | some (.ok (a, v)) => exact .ok rfl rfl hm

/-- A run equal to another ends alike with no growth, if a result leaves memory alone. -/
theorem alike_of_eq {α : Type} {w : World} {x y : Option (Except (Exit World) (α × World))}
    (h : x = y) (hkeep : ∀ a v, y = some (.ok (a, v)) → v.memory = w.memory) :
    Alike 0 w x y := by
  subst h
  match x, hkeep with
  | none, _ => exact .diverge
  | some (.error f), _ => exact .exit f
  | some (.ok (a, v)), hkeep => exact .ok rfl rfl (by rw [hkeep a v rfl]; omega)

/-- A call with no input and no output copied, as std's empty buffers make it, neither reads
    nor changes memory: it is the call a hand-written model makes on empty memory, with memory
    put back. -/
theorem call_noData (gasArg addr value argsPtr retPtr : UInt256) (I : ExecutionEnv) (w : World) :
    (call gasArg addr value argsPtr (UInt256.ofNat 0) retPtr (UInt256.ofNat 0)).exec I w =
      withMemory w.memory ((call gasArg addr value ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩).exec I
        { w with memory := ByteArray.empty }) := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have h0' : (UInt256.ofNat 0).toNat = 0 := rfl
  have hmin : ∀ o : ByteArray, (min (UInt256.ofNat 0) (UInt256.ofNat o.size)).toNat = 0 := by
    intro o
    have hle : UInt256.ofNat 0 ≤ UInt256.ofNat o.size := Nat.zero_le _
    simp [min, hle, h0']
  by_cases hs : I.perm = false ∧ value ≠ ⟨0⟩
  · simp [call, hs]
  cases hf : w.feed with
  | nil => simp [call, message, next, hs, hf]
  | cons s rest =>
    simp only [call, message, next, M.exec_bind, M.exec_read, M.exec_get, M.exec_set, M.exec_pure,
      if_neg hs, hf, h0, h0', byteArray_readWithPadding_zero]
    generalize (if value ≤ ((w.accounts.get? I.codeOwner).option ⟨0⟩ (·.balance)) ∧
      I.depth < 1024 then _ else _) = T
    obtain ⟨σ', g', A', z, o⟩ := T
    have hmin' : ∀ o : ByteArray, (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := hmin
    simp [hmin, hmin', byteArray_write_len_zero]

/-- An entry that runs `arm` and returns its result through `ret` ends as a run of `arm'` that
    returns the encoding `enc` of its result, when the two arms end alike up to memory and `ret`
    stops with that encoding, changing memory only. -/
theorem endsAs_alike {α : Type} {arm arm' : FeM α} {ret : α → FeM Empty} {enc : α → ByteArray}
    {I : ExecutionEnv} {w : World} {grow : Nat}
    (hret : ∀ r w', w'.memory.size + 32 < UInt256.size →
      ∃ memory, (ret r).exec I w' = some (.error (.stop (enc r) { w' with memory := memory })))
    (halike : Alike grow w (arm.exec I w) (arm'.exec I w))
    (hmem : w.memory.size + grow + 32 < UInt256.size) :
    EndsAs ((entry (arm >>= ret)).exec I w) ((arm' >>= fun r => pure (enc r)).exec I w) := by
  generalize ha : arm.exec I w = x at halike
  generalize hb : arm'.exec I w = y at halike
  cases halike with
  | ok hacc hlogs hm =>
    rename_i a v v'
    obtain ⟨memory, hr⟩ := hret a v (by omega)
    simp [entry, ha, hb, hr]
    exact .stop_ok hacc hlogs
  | exit f => simp [entry, ha, hb]; exact .exit f
  | diverge => simp [entry, ha, hb]; exact .diverge

end Fe.EVM
