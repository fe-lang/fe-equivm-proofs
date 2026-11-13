import Lean

/-!
# Commands for embedding exported code

## `export_all`

Exported contract code names the core and std definitions it shares with other contracts as if
they were its own, and starts with the `export` of the ones it names.  Proofs about it name
more of them.  `export_all ns` gives every declaration of namespace `ns` an alias in the current
namespace, as `export ns (…)` gives the ones it lists, except where the current namespace has
that name already.  An alias, unlike a name `open` brings in, takes precedence over a root
declaration of the same name, such as `max`.

## `simp_exported`

Proofs about exported code run through the core and std definitions it calls.  After the
exported text of a namespace, `simp_exported except a b` makes each definition in the model
monad that the file adds to that namespace `[scoped simp]`, but `a` and `b`: `simp` unfolds
them where the namespace is open.  The exceptions are the definitions a proof states a lemma
for, and the recursive ones, which `simp` would unfold without end.
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

/-- Make every non-recursive definition in the model monad that this file adds to the current
    namespace `[scoped simp]`, except `names`. -/
syntax "simp_exported" (" except " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(simp_exported $[except $names*]?) => do
    let current ← getCurrNamespace
    let env ← getEnv
    let kept ← (names.getD #[]).mapM fun name => do
      let kept := current ++ name.getId
      unless env.contains kept do throwErrorAt name "unknown definition {kept}"
      pure kept
    let defs := env.constants.map₂.foldl (init := #[]) fun defs name info =>
      if current.isPrefixOf name && !name.isInternalDetail && info matches .defnInfo _
          && info.type.getForallBody.getAppFn.isConstOf `Fe.EVM.FeM && !kept.contains name then
        defs.push name
      else defs
    for name in defs do
      unless ← liftCoreM (Meta.isRecursiveDefinition name) do
        elabCommand (← `(attribute [scoped simp] $(mkIdent name)))
