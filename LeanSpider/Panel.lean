import LeanSpider.Tactics
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Presentation.Expr

open Lean Server Elab Meta ProofWidgets

namespace LeanSpider

/-- Render a goal `d₁ ≈z d₂` as the current diagram with the goal diagram alongside.
    Returns `none` if `e` is not a ZX equivalence, or if a side still contains
    metavariables or free variables (so cannot be evaluated to a concrete diagram). -/
def zxEquivHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (lhs, rhs) := e.app2? ``ZXDiagram.equiv | return none
  try
    let dLhs ← evalZXDiagram lhs
    -- An unassigned RHS (e.g. from `zx_explore`) means there is no goal to show yet.
    let goal? ← if rhs.hasExprMVar then pure none else some <$> evalZXDiagram rhs
    return some (dLhs.toHtml goal?)
  catch _ => return none

/-- Render a bare `ZXDiagram`-valued term, e.g. a subterm selected with shift-click. -/
def zxDiagramHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  if !(← inferType e).isConstOf ``ZXDiagram then return none
  try return some (← evalZXDiagram e).toHtml
  catch _ => return none

/-- Presents `≈z` goals and `ZXDiagram` subterms as diagrams. Surfaced by
    `ProofWidgets.GoalTypePanel` and, for shift-click selections,
    `ProofWidgets.SelectionPanel`.

    Throwing is how a presenter signals "not applicable": `getExprPresentations`
    catches it and omits this presenter for the expression. -/
@[expr_presenter]
def zxPresenter : ExprPresenter where
  userName := "ZX diagram"
  layoutKind := .block
  present e := do
    if let some html ← zxEquivHtml? e then return html
    if let some html ← zxDiagramHtml? e then return html
    throwError "Not a ZX diagram or `≈z` goal."

@[server_rpc_method]
def ZXPanel.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    -- No goal means no proof in progress, e.g. the cursor is on a `#zx` line.
    -- Render nothing at all, rather than a panel announcing it has nothing to
    -- show directly above the diagram that `#zx` is already drawing.
    let some g := props.goals[0]? | return .text ""
    let html? ← g.ctx.val.runMetaM {} do
      g.mvarId.withContext do
        zxEquivHtml? (← g.mvarId.getType)
    return html?.getD (.text "No ZX diagram.")

/-- Renders the current `≈z` goal as a diagram, following the cursor through a
    proof. Enable for a section with

    ```lean
    show_panel_widgets [local ZXPanel]
    ```

    or for a single proof with `with_panel_widgets [ZXPanel]`. -/
@[widget_module]
def ZXPanel : Component PanelWidgetProps :=
  mk_rpc_widget% ZXPanel.rpc

/-- Display a `ZXDiagram` in the InfoView at a top-level command:

    ```lean
    #zx zHadX
    ```

    The diagram must be closed, since it is evaluated to a concrete value to be
    drawn. -/
syntax (name := zxCmd) "#zx " term : command

open Elab Command in
@[command_elab zxCmd]
def elabZxCmd : CommandElab := fun
  | stx@`(#zx $t:term) => do
    let html ← liftTermElabM do
      let e ← Term.elabTerm t (mkConst ``ZXDiagram)
      Term.synthesizeSyntheticMVarsNoPostponing
      let some html ← zxDiagramHtml? (← instantiateMVars e)
        | throwError "#zx could not evaluate{indentExpr e}\nto a concrete diagram."
      return html
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

end LeanSpider
