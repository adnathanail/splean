import SpLean.Axiomatic.Tactics
import SpLean.Algebraic.Render
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Presentation.Expr

open Lean Server Elab Meta ProofWidgets

namespace SpLean

/-- "Cannot be drawn" is a `none`, but an interrupt or a blown recursion depth is
    not an answer about the diagram: the first aborts a superseded request when the
    user edits the file, the second means we ran out of stack rather than out of
    diagram. Both must propagate, or a cancelled request resolves with a misleading
    "No ZX diagram." -/
private def asRenderFailure (ex : Exception) : MetaM (Option Html) := do
  if ex.isInterrupt || ex.isMaxRecDepth then throw ex
  return none

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
  catch ex => asRenderFailure ex

/-- Render a bare `ZXDiagram`-valued term, e.g. a subterm selected with shift-click. -/
def zxDiagramHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  try
    if !(← inferType e).isConstOf ``ZXDiagram then return none
    return some (← evalZXDiagram e).toHtml
  catch ex => asRenderFailure ex

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

/-- How many goals to draw at once. A case split can leave many goals live, and a
    wall of diagrams is less use than a few; the rest are reported as a count. -/
def maxPanelGoals : Nat := 6

/-- A goal's `case` name, shown above its diagram so that the cases of a split can
    be told apart. -/
private def goalHeading (g : Widget.InteractiveGoal) : Html :=
  .element "div"
    #[("style", Json.mkObj [("fontFamily", "monospace"), ("fontWeight", "bold"),
                            ("marginTop", "8px")])]
    #[.text (g.userName?.getD "goal")]

@[server_rpc_method]
def ZXPanel.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    -- No goal means no proof in progress, e.g. the cursor is on a `#zx` line.
    -- Render nothing at all, rather than a panel announcing it has nothing to
    -- show directly above the diagram that `#zx` is already drawing.
    if props.goals.isEmpty then return .text ""
    let shown := props.goals.extract 0 maxPanelGoals
    let mut out : Array Html := #[]
    for g in shown do
      let html? ← g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          zxEquivHtml? (← g.mvarId.getType)
      if let some html := html? then
        -- Only label when there is more than one diagram; a heading above a lone
        -- diagram is noise.
        if shown.size > 1 then out := out.push (goalHeading g)
        out := out.push html
    if out.isEmpty then return .text "No ZX diagram."
    let omitted := props.goals.size - shown.size
    if omitted > 0 then
      out := out.push (.text s!"… and {omitted} further goal(s) not drawn.")
    return .element "div" #[] out

/-- Renders the current `≈z` goal as a diagram, following the cursor through a
    proof. Enable for a section with

    ```lean
    show_panel_widgets [local ZXPanel]
    ```

    or for a single proof with `with_panel_widgets [ZXPanel]`. -/
@[widget_module]
def ZXPanel : Component PanelWidgetProps :=
  mk_rpc_widget% ZXPanel.rpc

/-- Display a ZX diagram in the InfoView at a top-level command:

    ```lean
    #zx zHadX          -- graph-style `ZXDiagram`
    #zx algCnot        -- algebraic `ZX n m`
    #zx greenAlpha     -- `(α : AlgPhase) → ZX 0 0`, drawn with `α` on the spider
    ```

    Both representations are accepted, so `#zx` replaces ProofWidgets'
    `#html d.toHtml` for either one. A `ZXDiagram` must be closed, since it is
    evaluated to a concrete value to be drawn. An algebraic term need not be:
    it is walked at the `Expr` level, so a phase it cannot evaluate is drawn
    as its own source text, and any leading `∀`s are instantiated with their
    own binders — which is what makes a phase-parameterized diagram
    displayable at all.

    Unlike the `ZXDiagram`-only form this had before, the argument is
    elaborated without an expected type — `ZX n m` is arity-indexed, so
    there is no single type to ensure against. Notation that needs an
    expected type (`.spider .Z 1 1`, anonymous constructors) therefore
    needs an ascription: `#zx (.spider .Z 1 1 : ZX 1 1)`. -/
syntax (name := zxCmd) "#zx " term : command

open Elab Command in
@[command_elab zxCmd]
def elabZxCmd : CommandElab := fun
  | stx@`(#zx $t:term) => do
    let html ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if let some html ← zxDiagramHtml? e then return html
      if let some html ← Algebraic.zxTermHtml? e then return html
      -- Neither branch fired: either the term has the wrong type entirely, or
      -- it is a `ZXDiagram` that could not be evaluated (an open term). An
      -- algebraic term that is the right type but cannot be walked reports
      -- that itself, from `zxTermHtml?`. Report the type so the cases are
      -- told apart.
      throwError "#zx expects a `ZXDiagram` or an algebraic `ZX n m` term, \
        and a `ZXDiagram` has to be closed enough to evaluate. Got{indentExpr e}\
        \nof type{indentExpr (← inferType e)}"
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

end SpLean
