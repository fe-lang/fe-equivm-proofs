import FeProofs
/-! Lists the declarations of `FeProofs.*` modules that no capstone theorem (`…ContractCorrect`) uses.
Run: `lake env lean scripts/Unused.lean`. -/
open Lean Meta

def closureOf (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots.toList
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet do
          unless seen.contains m do stack := m :: stack
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (n, _) =>
    if (`FeProofs).isPrefixOf n && n.lastComponentAsString.endsWith "ContractCorrect" then some n else none
  let used := closureOf env roots.toArray
  let mut byMod : Std.HashMap Name (Array (Nat × Name)) := {}
  let mut total := 0
  for (n, ci) in env.constants.toList do
    if ci matches .recInfo _ then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FeProofs).isPrefixOf mod do continue
    if used.contains n || n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then continue
    if (← isMatcher n) || isPrivateName n && n.isInternal then continue
    let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
    byMod := byMod.insert mod ((byMod.getD mod #[]).push (line, n))
    total := total + 1
  IO.println s!"unused: {total}"
  for (mod, ds) in byMod.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"== {mod} ({ds.size})"
    for (l, n) in ds.qsort (fun a b => a.1 < b.1) do
      IO.println s!"  {l}\t{n}"
