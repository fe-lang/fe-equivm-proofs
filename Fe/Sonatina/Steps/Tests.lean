import Fe.Sonatina.Steps.Machine
import Fe.Sonatina.Steps.Read

/-!
# Tests of the machine-step checkers

Hand-written records (`Tests/gen.py` writes them): small machine-IR functions before and after
a step, which `validateWith` accepts by kernel evaluation, and mutations of them, which it
rejects.  The final module is the record's own composition (`replay`), so these test the step
checkers; the comparison with a sidecar's machine IR is the same `decide` on modules.
-/

namespace Fe.Sonatina.Steps.Tests

/-- The module a record composes to, its steps unchecked. -/
def replay (r : MachineSteps) : Module :=
  r.passes.foldl (fun M p => p.steps.foldl (fun M st => stepOut M st.funcs) M) (r.module [])

machine_steps_file es_ok "Fe/Sonatina/Steps/Tests/edge_split.json"
machine_steps_file es_bad_phi "Fe/Sonatina/Steps/Tests/edge_split_bad_phi.json"
machine_steps_file es_bad_store "Fe/Sonatina/Steps/Tests/edge_split_bad_store.json"
machine_steps_file es_bad_inst "Fe/Sonatina/Steps/Tests/edge_split_bad_inst.json"
machine_steps_file es_bad_target "Fe/Sonatina/Steps/Tests/edge_split_bad_target.json"
machine_steps_file es_bad_swap "Fe/Sonatina/Steps/Tests/edge_split_bad_swap.json"

machine_steps_file es_br_same "Fe/Sonatina/Steps/Tests/es_br_same.json"
machine_steps_file es_table_same "Fe/Sonatina/Steps/Tests/es_table_same.json"
machine_steps_file es_br_differ "Fe/Sonatina/Steps/Tests/es_br_differ.json"
machine_steps_file es_table_nodefault "Fe/Sonatina/Steps/Tests/es_table_nodefault.json"
machine_steps_file wf_table_dup "Fe/Sonatina/Steps/Tests/wf_table_dup.json"
machine_steps_file wf_table_ok "Fe/Sonatina/Steps/Tests/wf_table_ok.json"
machine_steps_file es_unreachable "Fe/Sonatina/Steps/Tests/es_unreachable.json"
machine_steps_file es_bad_ssa "Fe/Sonatina/Steps/Tests/es_bad_ssa.json"
machine_steps_file es_two_slots "Fe/Sonatina/Steps/Tests/es_two_slots.json"

/-- The records validate with no symbols: none uses one. -/
abbrev ES := validateWith [.edgeSplit] []

example : ES es_ok (replay es_ok) = true := by decide +kernel
example : ES es_bad_phi (replay es_bad_phi) = false := by decide +kernel
example : ES es_bad_store (replay es_bad_store) = false := by decide +kernel
example : ES es_bad_inst (replay es_bad_inst) = false := by decide +kernel
example : ES es_bad_target (replay es_bad_target) = false := by decide +kernel
example : ES es_bad_swap (replay es_bad_swap) = false := by decide +kernel
/-- A kind outside the allowed list is rejected. -/
example : validateWith [] [] es_ok (replay es_ok) = false := by decide +kernel
/-- The final module must be the composed one. -/
example : ES es_ok (es_ok.module []) = false := by decide +kernel

/-! The lifted restriction: `br v0 block1 block1` and an all-identical `br_table` with a
default become `jump block1`; `br` to different blocks does not. -/
example : ES es_br_same (replay es_br_same) = true := by decide +kernel
example : ES es_table_same (replay es_table_same) = true := by decide +kernel
example : ES es_br_differ (replay es_br_differ) = false := by decide +kernel

/-! Review C-6: a defaultless table turned into `jump` is rejected; so is a table with
duplicate keys, which `wf` rejects in the lowered module. -/
example : ES es_table_nodefault (replay es_table_nodefault) = false := by decide +kernel
example : ES wf_table_dup (replay wf_table_dup) = false := by decide +kernel
example : ES wf_table_ok (replay wf_table_ok) = true := by decide +kernel

/-! Review H-1: a tree whose entry has an immediate dominator is rejected; a function with an
unreachable block jumping into reachable code is accepted, and an input not in SSA form is
rejected. -/

/-- The lowered function of a record of one function. -/
def lowered₀ (r : MachineSteps) : Func := (r.lowered.head?.map (·.func)).getD default

example : (domTree (lowered₀ es_ok)).valid (lowered₀ es_ok) = true := by decide +kernel
example : ({ domTree (lowered₀ es_ok) with idom := (domTree (lowered₀ es_ok)).idom.insert 0 2 }
    : DomTree).valid (lowered₀ es_ok) = false := by decide +kernel
example : ES es_unreachable (replay es_unreachable) = true := by decide +kernel
example : ES es_bad_ssa (replay es_bad_ssa) = false := by decide +kernel

/-- Review 6 F-2: two slots of one block may go to one split block. -/
example : ES es_two_slots (replay es_two_slots) = true := by decide +kernel

/-! ## `cfg_cleanup` -/

machine_steps_file cc_merge "Fe/Sonatina/Steps/Tests/cc_merge.json"
machine_steps_file cc_bad_inst "Fe/Sonatina/Steps/Tests/cc_bad_inst.json"
machine_steps_file cc_tunnel "Fe/Sonatina/Steps/Tests/cc_tunnel.json"
machine_steps_file cc_bad_phi "Fe/Sonatina/Steps/Tests/cc_bad_phi.json"
machine_steps_file cc_bad_c4_phi "Fe/Sonatina/Steps/Tests/cc_bad_c4_phi.json"
machine_steps_file cc_bridge "Fe/Sonatina/Steps/Tests/cc_bridge.json"
machine_steps_file cc_unreachable "Fe/Sonatina/Steps/Tests/cc_unreachable.json"
machine_steps_file cc_trivial "Fe/Sonatina/Steps/Tests/cc_trivial.json"
machine_steps_file cc_chain "Fe/Sonatina/Steps/Tests/cc_chain.json"
machine_steps_file cc_collapse "Fe/Sonatina/Steps/Tests/cc_collapse.json"
machine_steps_file cc_collapse_merge "Fe/Sonatina/Steps/Tests/cc_collapse_merge.json"
machine_steps_file cc_noret "Fe/Sonatina/Steps/Tests/cc_noret.json"
machine_steps_file cc_bad_noret_claim "Fe/Sonatina/Steps/Tests/cc_bad_noret_claim.json"
machine_steps_file cc_bad_noret_none "Fe/Sonatina/Steps/Tests/cc_bad_noret_none.json"
machine_steps_file cc_bad_noret_id "Fe/Sonatina/Steps/Tests/cc_bad_noret_id.json"
machine_steps_file cc_noret_kept "Fe/Sonatina/Steps/Tests/cc_noret_kept.json"
machine_steps_file cc_bad_sstore "Fe/Sonatina/Steps/Tests/cc_bad_sstore.json"
machine_steps_file cc_bad_swap "Fe/Sonatina/Steps/Tests/cc_bad_swap.json"
machine_steps_file cc_bad_entry "Fe/Sonatina/Steps/Tests/cc_bad_entry.json"
machine_steps_file cc_bad_pred "Fe/Sonatina/Steps/Tests/cc_bad_pred.json"

abbrev CC := validateWith [.cfgCleanup] []

/-- Accepted: a merge with a trivial phi after pruning (design §4.3), a tunnel, a forward bridge
(a tunnel through a block's phi), an unreachable block deleted, a trivial loop phi, chained
trivial phis, a branch collapsed to `jump` (and then merged), a noreturn trim, and an existing
`call; unreachable` tail. -/
example : CC cc_merge (replay cc_merge) = true := by decide +kernel
example : CC cc_tunnel (replay cc_tunnel) = true := by decide +kernel
example : CC cc_bridge (replay cc_bridge) = true := by decide +kernel
example : CC cc_unreachable (replay cc_unreachable) = true := by decide +kernel
example : CC cc_trivial (replay cc_trivial) = true := by decide +kernel
example : CC cc_chain (replay cc_chain) = true := by decide +kernel
example : CC cc_collapse (replay cc_collapse) = true := by decide +kernel
example : CC cc_collapse_merge (replay cc_collapse_merge) = true := by decide +kernel
example : CC cc_noret (replay cc_noret) = true := by decide +kernel
example : CC cc_noret_kept (replay cc_noret_kept) = true := by decide +kernel

/-- Rejected: review C-4's counterexamples (a phi taken as trivial over a tunnelled
predecessor; a deleted `evm_sstore`; swapped branch targets; a changed entry), a merged block
with a second predecessor, a changed instruction, a wrong phi operand, a noreturn claim that does
not hold, a trim without a claim, and a trim's `unreachable` with an input id. -/
example : CC cc_bad_c4_phi (replay cc_bad_c4_phi) = false := by decide +kernel
example : CC cc_bad_sstore (replay cc_bad_sstore) = false := by decide +kernel
example : CC cc_bad_swap (replay cc_bad_swap) = false := by decide +kernel
example : CC cc_bad_entry (replay cc_bad_entry) = false := by decide +kernel
example : CC cc_bad_pred (replay cc_bad_pred) = false := by decide +kernel
example : CC cc_bad_inst (replay cc_bad_inst) = false := by decide +kernel
example : CC cc_bad_phi (replay cc_bad_phi) = false := by decide +kernel
example : CC cc_bad_noret_claim (replay cc_bad_noret_claim) = false := by decide +kernel
example : CC cc_bad_noret_none (replay cc_bad_noret_none) = false := by decide +kernel
example : CC cc_bad_noret_id (replay cc_bad_noret_id) = false := by decide +kernel

/-! ## `branch_canonicalize` and `branch_conditions` -/

machine_steps_file bc_peel1 "Fe/Sonatina/Steps/Tests/bc_peel1.json"
machine_steps_file bc_peel2 "Fe/Sonatina/Steps/Tests/bc_peel2.json"
machine_steps_file bc_peel3 "Fe/Sonatina/Steps/Tests/bc_peel3.json"
machine_steps_file bc_peel_partial "Fe/Sonatina/Steps/Tests/bc_peel_partial.json"
machine_steps_file bc_keep "Fe/Sonatina/Steps/Tests/bc_keep.json"
machine_steps_file bc_cross "Fe/Sonatina/Steps/Tests/bc_cross.json"
machine_steps_file bc_conditions "Fe/Sonatina/Steps/Tests/bc_conditions.json"
machine_steps_file bc_bad_parity1 "Fe/Sonatina/Steps/Tests/bc_bad_parity1.json"
machine_steps_file bc_bad_parity2 "Fe/Sonatina/Steps/Tests/bc_bad_parity2.json"
machine_steps_file bc_bad_parity3 "Fe/Sonatina/Steps/Tests/bc_bad_parity3.json"
machine_steps_file bc_bad_live "Fe/Sonatina/Steps/Tests/bc_bad_live.json"
machine_steps_file bc_bad_delete "Fe/Sonatina/Steps/Tests/bc_bad_delete.json"
machine_steps_file bc_bad_not "Fe/Sonatina/Steps/Tests/bc_bad_not.json"
machine_steps_file bc_bad_cond "Fe/Sonatina/Steps/Tests/bc_bad_cond.json"
machine_steps_file bc_bad_target "Fe/Sonatina/Steps/Tests/bc_bad_target.json"

abbrev BC := validateWith [.branchCanonicalize, .branchConditions] []

/-- Accepted: `is_zero` peeled `k = 1, 2, 3` times (targets swapped iff `k` is odd, the
`is_zero`s deleted); one of two peeled; an `is_zero` kept that the output still uses; an
`is_zero` in a dominating block; `branch_conditions`. -/
example : BC bc_peel1 (replay bc_peel1) = true := by decide +kernel
example : BC bc_peel2 (replay bc_peel2) = true := by decide +kernel
example : BC bc_peel3 (replay bc_peel3) = true := by decide +kernel
example : BC bc_peel_partial (replay bc_peel_partial) = true := by decide +kernel
example : BC bc_keep (replay bc_keep) = true := by decide +kernel
example : BC bc_cross (replay bc_cross) = true := by decide +kernel
example : BC bc_conditions (replay bc_conditions) = true := by decide +kernel

/-- Rejected: review M-3's counterexamples that apply to peeling (the wrong parity for `k = 1, 2,
3`, a deleted `is_zero` the output uses, a deleted `evm_sstore`, a peel through the bitwise
`not`), an unrelated condition, a changed target. -/
example : BC bc_bad_parity1 (replay bc_bad_parity1) = false := by decide +kernel
example : BC bc_bad_parity2 (replay bc_bad_parity2) = false := by decide +kernel
example : BC bc_bad_parity3 (replay bc_bad_parity3) = false := by decide +kernel
example : BC bc_bad_live (replay bc_bad_live) = false := by decide +kernel
example : BC bc_bad_delete (replay bc_bad_delete) = false := by decide +kernel
example : BC bc_bad_not (replay bc_bad_not) = false := by decide +kernel
example : BC bc_bad_cond (replay bc_bad_cond) = false := by decide +kernel
example : BC bc_bad_target (replay bc_bad_target) = false := by decide +kernel

/-! ## Facts (ruling R-11.3) -/

machine_steps_file cc_bad_facts "Fe/Sonatina/Steps/Tests/cc_bad_facts.json"
machine_steps_file cc_bad_unread "Fe/Sonatina/Steps/Tests/cc_bad_unread.json"
machine_steps_file rd_demand_empty "Fe/Sonatina/Steps/Tests/rd_demand_empty.json"
machine_steps_file rd_demand_none "Fe/Sonatina/Steps/Tests/rd_demand_none.json"

/-- A step of a kind that reads no facts is rejected if it carries known bits, or a key no
checker reads. -/
example : CC cc_bad_facts (replay cc_bad_facts) = false := by decide +kernel
example : CC cc_bad_unread (replay cc_bad_unread) = false := by decide +kernel

/-- The first function step's facts. -/
def facts₀ (r : MachineSteps) : Schemas.StepFacts :=
  (((r.passes.head?.bind (·.steps.head?)).bind (·.funcs.head?)).map (·.facts)).getD {}

/-- `"demanded_bits": []` is read as a demand round with no demanded value, `null` as none. -/
example : (facts₀ rd_demand_empty).demanded = some [] := by decide
example : (facts₀ rd_demand_none).demanded = none := by decide
example : (facts₀ cc_bad_facts).knownBits = [(3, 0, 1)] := by decide
example : (facts₀ cc_bad_unread).unread = ["ranges"] := by decide

/-! ## `coalesce_copies` -/

machine_steps_file kc_const "Fe/Sonatina/Steps/Tests/kc_const.json"
machine_steps_file kc_interleaved "Fe/Sonatina/Steps/Tests/kc_interleaved.json"
machine_steps_file kc_arith "Fe/Sonatina/Steps/Tests/kc_arith.json"
machine_steps_file kc_keep_add "Fe/Sonatina/Steps/Tests/kc_keep_add.json"
machine_steps_file kc_two_runs "Fe/Sonatina/Steps/Tests/kc_two_runs.json"
machine_steps_file kc_base "Fe/Sonatina/Steps/Tests/kc_base.json"
machine_steps_file kc_base2 "Fe/Sonatina/Steps/Tests/kc_base2.json"
machine_steps_file kc_past "Fe/Sonatina/Steps/Tests/kc_past.json"
machine_steps_file kc_bad_overlap "Fe/Sonatina/Steps/Tests/kc_bad_overlap.json"
machine_steps_file kc_bad_len "Fe/Sonatina/Steps/Tests/kc_bad_len.json"
machine_steps_file kc_bad_order "Fe/Sonatina/Steps/Tests/kc_bad_order.json"
machine_steps_file kc_bad_twouse "Fe/Sonatina/Steps/Tests/kc_bad_twouse.json"
machine_steps_file kc_bad_store "Fe/Sonatina/Steps/Tests/kc_bad_store.json"
machine_steps_file kc_bad_operand "Fe/Sonatina/Steps/Tests/kc_bad_operand.json"
machine_steps_file kc_bad_gap "Fe/Sonatina/Steps/Tests/kc_bad_gap.json"
machine_steps_file kc_bad_other "Fe/Sonatina/Steps/Tests/kc_bad_other.json"
machine_steps_file kc_bad_one "Fe/Sonatina/Steps/Tests/kc_bad_one.json"
machine_steps_file kc_bad_moved "Fe/Sonatina/Steps/Tests/kc_bad_moved.json"
machine_steps_file kc_bad_base_inter "Fe/Sonatina/Steps/Tests/kc_bad_base_inter.json"
machine_steps_file kc_bad_past_inter "Fe/Sonatina/Steps/Tests/kc_bad_past_inter.json"
machine_steps_file kc_bad_two_base "Fe/Sonatina/Steps/Tests/kc_bad_two_base.json"
machine_steps_file kc_unreach "Fe/Sonatina/Steps/Tests/kc_unreach.json"
machine_steps_file kc_unreach_any "Fe/Sonatina/Steps/Tests/kc_unreach_any.json"
machine_steps_file kc_bad_unreach_term "Fe/Sonatina/Steps/Tests/kc_bad_unreach_term.json"
machine_steps_file kc_bad_unreach_used "Fe/Sonatina/Steps/Tests/kc_bad_unreach_used.json"
machine_steps_file kc_bad_reach_any "Fe/Sonatina/Steps/Tests/kc_bad_reach_any.json"

abbrev KC := validateWith [.coalesceCopies] []

/-- Accepted: two words with all loads first; interleaved disjoint constant ranges; addresses
through `add`/`sub` chains, the arithmetic deleted, three words; an `add` of the window that the
output still uses, kept before the copy; two runs in one block and one in another; base-relative
ranges, all loads first, at one base and at a base each; a constant range past `2 ^ 256`, all
loads first (the copy does not terminate there). -/
example : KC kc_const (replay kc_const) = true := by decide +kernel
example : KC kc_interleaved (replay kc_interleaved) = true := by decide +kernel
example : KC kc_arith (replay kc_arith) = true := by decide +kernel
example : KC kc_keep_add (replay kc_keep_add) = true := by decide +kernel
example : KC kc_two_runs (replay kc_two_runs) = true := by decide +kernel
example : KC kc_base (replay kc_base) = true := by decide +kernel
example : KC kc_base2 (replay kc_base2) = true := by decide +kernel
example : KC kc_past (replay kc_past) = true := by decide +kernel

/-- Rejected: interleaved overlapping ranges; a length other than `32 n`; store `i` not storing
load `i`; a load used twice; a store outside a run deleted; a changed copy operand;
non-contiguous addresses; another instruction in the window; one word; a kept `add` moved after
the copy; interleaved base-relative ranges; interleaved with a range past `2 ^ 256`; loads at
two bases. -/
example : KC kc_bad_overlap (replay kc_bad_overlap) = false := by decide +kernel
example : KC kc_bad_len (replay kc_bad_len) = false := by decide +kernel
example : KC kc_bad_order (replay kc_bad_order) = false := by decide +kernel
example : KC kc_bad_twouse (replay kc_bad_twouse) = false := by decide +kernel
example : KC kc_bad_store (replay kc_bad_store) = false := by decide +kernel
example : KC kc_bad_operand (replay kc_bad_operand) = false := by decide +kernel
example : KC kc_bad_gap (replay kc_bad_gap) = false := by decide +kernel
example : KC kc_bad_other (replay kc_bad_other) = false := by decide +kernel
example : KC kc_bad_one (replay kc_bad_one) = false := by decide +kernel
example : KC kc_bad_moved (replay kc_bad_moved) = false := by decide +kernel
example : KC kc_bad_base_inter (replay kc_bad_base_inter) = false := by decide +kernel
example : KC kc_bad_past_inter (replay kc_bad_past_inter) = false := by decide +kernel
example : KC kc_bad_two_base (replay kc_bad_two_base) = false := by decide +kernel

/-- Review 20, M-1: a run in an unreachable block whose addresses go through that block's own
`add`s, which the compiler coalesces (`copy.rs` visits every block).  `addrNorm` follows only
definitions in reachable blocks, so `cbodyOk` rejects the block's statements (the check before
the change ran it on every block); `blockOk` no longer checks an unreachable block's statements,
so the step is accepted, as is any other body there.  Rejected: the unreachable block's terminator
changed; its body using a deleted value (`unusedOk'`); the arbitrary body in a reachable block. -/
example : (((kc_unreach.lowered.head?.map (·.func)).bind fun f =>
    ((replay kc_unreach).funcs.head?).bind fun f' => (f.block? 1).bind fun b =>
      (f'.block? 1).map fun b' => (KCtx.of f f').cbodyOk (b.body.length + 1) b'.body b.body) =
    some false) := by decide +kernel
example : KC kc_unreach (replay kc_unreach) = true := by decide +kernel
example : KC kc_unreach_any (replay kc_unreach_any) = true := by decide +kernel
example : KC kc_bad_unreach_term (replay kc_bad_unreach_term) = false := by decide +kernel
example : KC kc_bad_unreach_used (replay kc_bad_unreach_used) = false := by decide +kernel
example : KC kc_bad_reach_any (replay kc_bad_reach_any) = false := by decide +kernel

/-! ## `lower_switches` -/

machine_steps_file ls_real "Fe/Sonatina/Steps/Tests/ls_real.json"
machine_steps_file ls_real_phi "Fe/Sonatina/Steps/Tests/ls_real_phi.json"
machine_steps_file ls_tree "Fe/Sonatina/Steps/Tests/ls_tree.json"
machine_steps_file ls_tree_perm "Fe/Sonatina/Steps/Tests/ls_tree_perm.json"
machine_steps_file ls_bad_pivot "Fe/Sonatina/Steps/Tests/ls_bad_pivot.json"
machine_steps_file ls_bad_pivot_low "Fe/Sonatina/Steps/Tests/ls_bad_pivot_low.json"
machine_steps_file ls_bad_swap "Fe/Sonatina/Steps/Tests/ls_bad_swap.json"
machine_steps_file ls_bad_default "Fe/Sonatina/Steps/Tests/ls_bad_default.json"
machine_steps_file ls_bad_missing "Fe/Sonatina/Steps/Tests/ls_bad_missing.json"
machine_steps_file ls_bad_target "Fe/Sonatina/Steps/Tests/ls_bad_target.json"
machine_steps_file ls_bad_moved "Fe/Sonatina/Steps/Tests/ls_bad_moved.json"
machine_steps_file ls_bad_extra "Fe/Sonatina/Steps/Tests/ls_bad_extra.json"
machine_steps_file ls_bad_fresh "Fe/Sonatina/Steps/Tests/ls_bad_fresh.json"
machine_steps_file ls_bad_slt "Fe/Sonatina/Steps/Tests/ls_bad_slt.json"
machine_steps_file ls_bad_scrut "Fe/Sonatina/Steps/Tests/ls_bad_scrut.json"
machine_steps_file ls_bad_id "Fe/Sonatina/Steps/Tests/ls_bad_id.json"
machine_steps_file ls_bad_junk "Fe/Sonatina/Steps/Tests/ls_bad_junk.json"
machine_steps_file ls_bad_body "Fe/Sonatina/Steps/Tests/ls_bad_body.json"
machine_steps_file ls_bad_node "Fe/Sonatina/Steps/Tests/ls_bad_node.json"
machine_steps_file ls_bad_phi_old "Fe/Sonatina/Steps/Tests/ls_bad_phi_old.json"
machine_steps_file ls_bad_phi_missing "Fe/Sonatina/Steps/Tests/ls_bad_phi_missing.json"
machine_steps_file ls_bad_phi_value "Fe/Sonatina/Steps/Tests/ls_bad_phi_value.json"
machine_steps_file ls_bad_max "Fe/Sonatina/Steps/Tests/ls_bad_max.json"

/-- The records validate with the symbols of their sections. -/
abbrev LS (r : MachineSteps) : Bool :=
  validateWith [.lowerSwitches] ["%contract_runtime_root_BytesViewBounds", ".", "%from_abi_tail__ge513",
    "%contract_runtime_root_Order"] r (replay r)

/-- The check alone, on the record's first lowered function and its first step's output: the
    mutants below fail it, not only the output's `wf`. -/
def lsCheck (r : MachineSteps) : Bool :=
  match r.lowered.head?, r.passes.head?.bind (·.steps.head?) with
  | some f, some st => match st.funcs.head? with
    | some fs => fs.facts.unread.isEmpty && checkLowerSwitches f.func (some f.insts) fs.out
    | none => false
  | _, _ => false

/-- Accepted: two real records (one switch of five keys; six switches, with phis in their
targets, whose operands from the switch's block move to the end); a hand-written switch with
keys 0 and `2 ^ 256 - 1`, the default also a case's target, a target two leaves go to, phis
in the targets and a kept one-case table; the same with phi operands in another order. -/
example : LS ls_real = true := by decide +kernel
example : lsCheck ls_real = true := by decide +kernel
example : LS ls_real_phi = true := by decide +kernel
example : lsCheck ls_real_phi = true := by decide +kernel
example : LS ls_tree = true := by decide +kernel
example : lsCheck ls_tree = true := by decide +kernel
example : LS ls_tree_perm = true := by decide +kernel
example : lsCheck ls_tree_perm = true := by decide +kernel

/-- Rejected, by `validate` and by the check alone: a pivot one above and one below; swapped
branch targets; a leaf with a wrong default, a missing key, a wrong target, a key of the other
leaf; an extra instruction in a new block; a condition that is an input value; a signed
compare; a leaf on another scrutinee; a leaf with the switch's instruction id; a new block
outside the trees; a changed statement of the switch's block; a node that is an input block;
a phi operand left on the switch's block, one missing for a leaf, a wrong one for a leaf; the
key `2 ^ 256 - 1` in the lower leaf. -/
example : LS ls_bad_pivot = false := by decide +kernel
example : lsCheck ls_bad_pivot = false := by decide +kernel
example : LS ls_bad_pivot_low = false := by decide +kernel
example : lsCheck ls_bad_pivot_low = false := by decide +kernel
example : LS ls_bad_swap = false := by decide +kernel
example : lsCheck ls_bad_swap = false := by decide +kernel
example : LS ls_bad_default = false := by decide +kernel
example : lsCheck ls_bad_default = false := by decide +kernel
example : LS ls_bad_missing = false := by decide +kernel
example : lsCheck ls_bad_missing = false := by decide +kernel
example : LS ls_bad_target = false := by decide +kernel
example : lsCheck ls_bad_target = false := by decide +kernel
example : LS ls_bad_moved = false := by decide +kernel
example : lsCheck ls_bad_moved = false := by decide +kernel
example : LS ls_bad_extra = false := by decide +kernel
example : lsCheck ls_bad_extra = false := by decide +kernel
example : LS ls_bad_fresh = false := by decide +kernel
example : lsCheck ls_bad_fresh = false := by decide +kernel
example : LS ls_bad_slt = false := by decide +kernel
example : lsCheck ls_bad_slt = false := by decide +kernel
example : LS ls_bad_scrut = false := by decide +kernel
example : lsCheck ls_bad_scrut = false := by decide +kernel
example : LS ls_bad_id = false := by decide +kernel
example : lsCheck ls_bad_id = false := by decide +kernel
example : LS ls_bad_junk = false := by decide +kernel
example : lsCheck ls_bad_junk = false := by decide +kernel
example : LS ls_bad_body = false := by decide +kernel
example : lsCheck ls_bad_body = false := by decide +kernel
example : LS ls_bad_node = false := by decide +kernel
example : lsCheck ls_bad_node = false := by decide +kernel
example : LS ls_bad_phi_old = false := by decide +kernel
example : lsCheck ls_bad_phi_old = false := by decide +kernel
example : LS ls_bad_phi_missing = false := by decide +kernel
example : lsCheck ls_bad_phi_missing = false := by decide +kernel
example : LS ls_bad_phi_value = false := by decide +kernel
example : lsCheck ls_bad_phi_value = false := by decide +kernel
example : LS ls_bad_max = false := by decide +kernel
example : lsCheck ls_bad_max = false := by decide +kernel

end Fe.Sonatina.Steps.Tests
