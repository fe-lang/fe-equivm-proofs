import FeProofs
/-! Lists `FeProofs.*` theorems whose statement exactly matches (up to binder names) another
theorem's, in this project or in its dependencies. Run: `lake env lean scripts/Dups.lean`. -/
open Lean Meta

#eval show CoreM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Name :=
    (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous
  let mut ours : Std.HashMap Expr (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if (`FeProofs).isPrefixOf (modOf n) && !n.isInternalDetail then
        ours := ours.insert ci.type ((ours.getD ci.type #[]).push n)
  let mut hits : Std.HashMap Expr (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if !n.isInternalDetail && ours.contains ci.type then
        hits := hits.insert ci.type ((hits.getD ci.type #[]).push n)
  for (_, ns) in hits.toArray do
    if ns.size > 1 then
      IO.println (", ".intercalate (ns.toList.map fun n => s!"{n} [{modOf n}]"))
