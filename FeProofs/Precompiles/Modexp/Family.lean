import Lean

/-!
# Modexp: one proof text for the four `Small<L>` copies

The exporter emits `small_power<L>` and its helpers four times, for `L = 1 … 4`, as the same text
with `L` a constant and the names suffixed by `L`.  `limb_family [k, …] … end_limb_family`
elaborates the commands between once per `k`, after replacing in every identifier each `ℓ` by the
digits of `k`, and the identifier `ℓ` itself by the numeral `k`.  So `small_power_ℓ.loop.eq_1`
names `small_power_2.loop.eq_1` at `k = 2`, and `smul ℓ m inv a b` is `smul 2 m inv a b`.
-/

namespace FeProofs.Modexp

open Lean Elab Command

/-- `n` with each `ℓ` in its components replaced by `k`. -/
def renameL (k : String) : Name → Name
  | .str p s => .str (renameL k p) (s.replace "ℓ" k)
  | .num p n => .num (renameL k p) n
  | .anonymous => .anonymous

/-- The syntax `s` at `L = k`. -/
partial def instL (k : Nat) : Syntax → Syntax
  | .ident info _ n _ =>
    if n == `ℓ then (Syntax.mkNumLit (toString k) info).raw
    else let n' := renameL (toString k) n; .ident info n'.toString.toRawSubstring n' []
  | .node info kind args => .node info kind (args.map (instL k))
  | s => s

/-- Elaborates the commands once per listed `L`. -/
syntax (name := limbFamily) "limb_family " "[" num,+ "]" (ppLine command)+ ppLine "end_limb_family" : command

@[command_elab limbFamily] def elabLimbFamily : CommandElab
  | `(limb_family [$ks,*] $cmds* end_limb_family) =>
    for k in ks.getElems do
      for c in cmds do elabCommand (instL k.getNat c)
  | _ => throwUnsupportedSyntax

end FeProofs.Modexp
