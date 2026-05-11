import SpLean.Algebraic.Visualize
import ProofWidgets.Component.HtmlDisplay

/-! # Rendering algebraic `ZX n m` terms

    The `MetaM` side of algebraic visualization: turning a `ZX n m` `Expr`
    into `Html`. Kept apart from `Visualize.lean` (which is pure) so that
    the `#zx` command in `SpLean/Panel.lean` can draw algebraic terms. -/

open Lean Elab Meta ProofWidgets

namespace SpLean.Algebraic

/-- If `ty` is `ZX n m`, return `(n, m)` as expressions. -/
private def matchZXType? (ty : Expr) : Option (Expr × Expr) :=
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.constName? == some ``ZX && args.size == 2 then
    some (args[0]!, args[1]!)
  else none

/-- Build an `Expr` calling `ZX.toHtml` and evaluate it to `Html`.
    `ZX n m` is arity-indexed so we can't `Meta.evalExpr` the term itself
    — but `Html` is a plain type, so we evaluate the *application*. The
    arity comes from `inferType`, which is why this can't be a plain
    `evalExpr` at a fixed type. -/
private unsafe def evalZXHtmlImpl (z : Expr) : MetaM Html := do
  let ty ← inferType z
  let some (nE, mE) := matchZXType? ty
    | throwError "evalZXHtml: expected `ZX n m`, got {ty}"
  -- `ZX.toHtml` also takes a phase-label override list; a term rendered by
  -- `#zx` is closed, so its phases come straight from the diagram and the
  -- list is empty. `mkAppOptM` does not fill in optional arguments, and a
  -- partial application would not evaluate at type `Html`.
  let noLabels : Expr := Lean.toExpr ([] : List (Nat × String))
  let htmlE ← mkAppOptM ``ZX.toHtml #[some nE, some mE, some z, some noLabels]
  Meta.evalExpr Html (mkConst ``ProofWidgets.Html) htmlE

@[implemented_by evalZXHtmlImpl]
opaque evalZXHtml (z : Expr) : MetaM Html

/-- Render an `Expr` as an algebraic ZX diagram, or `none` if it is not a
    `ZX n m` term. The `#zx` command uses this to accept algebraic terms
    alongside graph-style `ZXDiagram`s. -/
def zxTermHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  if (matchZXType? (← whnf (← inferType e))).isNone then return none
  return some (← evalZXHtml e)

end SpLean.Algebraic
