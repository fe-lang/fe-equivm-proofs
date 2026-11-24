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

end Fe.Sonatina.Steps.Tests
