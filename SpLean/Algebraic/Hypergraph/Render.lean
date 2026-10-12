import SpLean.Algebraic.Hypergraph.Visualize

/-! # Rendering a `Hyp` term

The `MetaM` side of hypergraph visualization, for `#zx` in `SpLean/Panel.lean`.
Unlike an algebraic `ZX n m`, which is walked at the `Expr` level, a `Hyp` is
*evaluated*: its fields are functions, so there is no constructor tree to walk.
The term therefore has to be closed. -/

open Lean Meta ProofWidgets

namespace SpLean.Algebraic.Hypergraph

private unsafe def evalWireHypergraphImpl (e : Expr) : MetaM Wire.Hypergraph :=
  Meta.evalExpr Wire.Hypergraph (mkConst ``Wire.Hypergraph) e

@[implemented_by evalWireHypergraphImpl]
private opaque evalWireHypergraph : Expr → MetaM Wire.Hypergraph

/-- Render a `Hyp n m`-valued term. `none` if `e` is not a `Hyp` at all;
    throws if it is one that cannot be evaluated. -/
def hypHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  unless (← whnf (← inferType e)).isAppOfArity ``Hyp 2 do return none
  return some (← evalWireHypergraph (← mkAppM ``Hyp.toWire #[e])).toHtml

end SpLean.Algebraic.Hypergraph
