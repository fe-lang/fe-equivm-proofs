import Lean

/-!
# `export_all`

Exported contract code names the core and std definitions it shares with other contracts as if
they were its own, and starts with the `export` of the ones it names.  Proofs about it name
more of them.  `export_all ns` gives every declaration of namespace `ns` an alias in the current
namespace, as `export ns (…)` gives the ones it lists, except where the current namespace has
that name already.  An alias, unlike a name `open` brings in, takes precedence over a root
declaration of the same name, such as `max`.
-/

open Lean Elab Command in
/-- Give every declaration of namespace `ns` an alias in the current namespace, unless the
    current namespace has a declaration or an alias of that name. -/
elab "export_all " ns:ident : command => do
  let [ns] ← resolveNamespace ns | throwErrorAt ns "ambiguous namespace"
  let current ← getCurrNamespace
  modifyEnv fun env => env.constants.fold (init := env) fun env name _ =>
    let alias := name.replacePrefix ns current
    if ns.isPrefixOf name && name != ns && !name.isInternalDetail && !env.contains alias
        && (getAliases env alias (skipProtected := false)).isEmpty then
      addAlias env alias name
    else env
