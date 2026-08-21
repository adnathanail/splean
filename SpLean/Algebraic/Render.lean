import SpLean.Algebraic.Visualize
import ProofWidgets.Component.HtmlDisplay

/-! # Rendering algebraic `ZX n m` terms

    The `MetaM` side of algebraic visualization: turning a `ZX n m` `Expr`
    into `Html`. Kept apart from `Visualize.lean` (which is pure) so that
    the `#zx` command in `SpLean/Panel.lean` can draw algebraic terms, and
    apart from `Tactics.lean` so that drawing one does not drag in the
    algebraic rewrite tactics and their proofs. -/

open Lean Elab Meta ProofWidgets

namespace SpLean.Algebraic

/-- If `ty` is `ZX n m`, return `(n, m)` as expressions. -/
private def matchZXType? (ty : Expr) : Option (Expr × Expr) :=
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.constName? == some ``ZX && args.size == 2 then
    some (args[0]!, args[1]!)
  else none

/-- The `AlgPhase` type as an `Expr` — used as the type filter when
    substituting symbolic phase free variables, and to type the placeholder
    `(0 : AlgPhase)` returned by `algPhaseZeroExpr`. -/
private def algPhaseTypeExpr : Expr := mkConst ``AlgPhase

/-- Build the placeholder phase `Expr`: `(0 : AlgPhase)`. Used to close
    a parameterized term before `Meta.evalExpr` so the eval can succeed —
    the visualized symbolic phases are recovered separately via the labels
    side-channel. -/
private def algPhaseZeroExpr : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some algPhaseTypeExpr, some (mkRawNatLit 0), none]

/-- Try to evaluate an `Expr` of type `AlgPhase` (a `ℚ`) to a concrete value.
    Returns `none` for symbolic phases (free variables, unreduced binders). -/
private unsafe def tryEvalAlgPhaseImpl (e : Expr) : MetaM (Option AlgPhase) := do
  try
    let v ← Meta.evalExpr AlgPhase algPhaseTypeExpr e
    return some v
  catch _ => return none

@[implemented_by tryEvalAlgPhaseImpl]
opaque tryEvalAlgPhase (e : Expr) : MetaM (Option AlgPhase)

/-- Format an `AlgPhase` for display. Uses `AlgPhase.format` (raw ℚ) rather
    than the graph-side `Phase.format`, so the displayed value matches the
    actual stored ℚ value (no mod-2π reduction). -/
private def algPhaseFormat (q : AlgPhase) : String :=
  AlgPhase.format q

/-- Render an `AlgPhase`-typed `Expr` as a display string. The walker
    prioritises *evaluation* over surface preservation: any sub-expression
    free of fvars is evaluated to a concrete `ℚ` and formatted via
    `algPhaseFormat`, so e.g. `phaseLit 1 4 + phaseLit 1 4` shows as `π/2`
    rather than `π/4 + π/4`. Surface `HAdd` / `HSub` / `Neg` combinators
    are only walked recursively when an fvar prevents evaluation. Free
    variables render as their user name; anything else falls back to
    `ppExpr`. -/
partial def phaseExprToLabel (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let fallback : MetaM String := do
    return (← Lean.PrettyPrinter.ppExpr e).pretty
  -- 1. Free variable — render as the user name.
  if e.isFVar then
    let decl ← e.fvarId!.getDecl
    return decl.userName.toString
  -- 2. Closed (no fvars) — evaluate as ℚ and format. Reduces
  --    `phaseLit 1 4 + phaseLit 1 4` to `π/2`.
  if !e.hasFVar then
    match (← tryEvalAlgPhase e) with
    | some q => return algPhaseFormat q
    | none   => return ← fallback
  -- 3. Has fvars — recurse through surface combinators so closed
  --    sub-expressions still evaluate cleanly while symbolic parts
  --    preserve their user names.
  let (fn, args) := (e.getAppFn, e.getAppArgs)
  match fn.constName?, args.size with
  | some ``HAdd.hAdd, 6 =>
      return s!"{← phaseExprToLabel args[4]!} + {← phaseExprToLabel args[5]!}"
  | some ``HSub.hSub, 6 =>
      return s!"{← phaseExprToLabel args[4]!} - {← phaseExprToLabel args[5]!}"
  | some ``Neg.neg, 3 =>
      return s!"-{← phaseExprToLabel args[2]!}"
  | _, _ => fallback

/-- Walk a `ZX n m` `Expr` in the same DFS / offset scheme as `buildFrag`
    in `Visualize.lean` (and `buildFusionProof` below). At each spider
    whose phase contains a free variable, format the phase Expr via
    `phaseExprToLabel` and record `(nodeId, prettyString)`. Returns
    `(labels, endOffset)`. -/
partial def collectPhaseLabels (z : Expr) (off : Nat := 0) :
    MetaM (List (Nat × String) × Nat) := do
  let z ← whnf z
  let f := z.getAppFn
  match f.constName? with
  | some ``ZX.empty    => return ([], off)
  | some ``ZX.wire     => return ([], off + 1)
  | some ``ZX.hadamard => return ([], off + 1)
  | some ``ZX.spider   =>
      let args := z.getAppArgs
      if args.size = 4 then
        let s ← phaseExprToLabel args[3]!
        return ([(off, s)], off + 1)
      return ([], off + 1)
  | some ``ZX.stack    =>
      let args := z.getAppArgs
      let (la, off1) ← collectPhaseLabels args[4]! off
      let (lb, off2) ← collectPhaseLabels args[5]! off1
      return (la ++ lb, off2)
  | some ``ZX.compose  =>
      let args := z.getAppArgs
      let (la, off1) ← collectPhaseLabels args[3]! off
      let (lb, off2) ← collectPhaseLabels args[4]! off1
      return (la ++ lb, off2)
  | _ => return ([], off)

/-- Substitute every free variable of type `AlgPhase` in `z` with the
    placeholder `(0 : AlgPhase)`. After this the Expr is closed wrt
    `AlgPhase` fvars and can be fed to `Meta.evalExpr` — symbolic phases
    are recovered visually via the labels list emitted by
    `collectPhaseLabels`. -/
def substitutePhaseFVars (z : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let mut fvars : Array Expr := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← isDefEq decl.type algPhaseTypeExpr then
        fvars := fvars.push decl.toExpr
  if fvars.isEmpty then return z
  let placeholder ← algPhaseZeroExpr
  let replacements := fvars.map fun _ => placeholder
  return z.replaceFVars fvars replacements

/-- Build an `Expr` calling `ZX.toHtml`/`ZX.toHtmlPair` (with symbolic-phase
    labels) and evaluate it to `Html`. `ZX n m` is arity-indexed so we can't
    `Meta.evalExpr` the term itself — but `Html` is a plain type, so we
    evaluate the *application*. -/
private unsafe def evalAlgHtmlImpl (lhs : Expr) (rhs? : Option Expr) : MetaM Html := do
  let ty ← inferType lhs
  let some (nE, mE) := matchZXType? ty
    | throwError "evalAlgHtml: expected `ZX n m`, got {ty}"
  let (lhsLabels, _) ← collectPhaseLabels lhs
  let lhs' ← substitutePhaseFVars lhs
  let lhsLabelsE : Expr := Lean.toExpr lhsLabels
  let htmlE ← match rhs? with
    | none =>
        mkAppOptM ``ZX.toHtml
          #[some nE, some mE, some lhs', some lhsLabelsE]
    | some rhs =>
        let (rhsLabels, _) ← collectPhaseLabels rhs
        let rhs' ← substitutePhaseFVars rhs
        let rhsLabelsE : Expr := Lean.toExpr rhsLabels
        mkAppOptM ``ZX.toHtmlPair
          #[some nE, some mE, some lhs', some rhs',
            some lhsLabelsE, some rhsLabelsE]
  Meta.evalExpr Html (mkConst ``ProofWidgets.Html) htmlE

@[implemented_by evalAlgHtmlImpl]
opaque evalAlgHtml (lhs : Expr) (rhs? : Option Expr) : MetaM Html
/-- Render an `Expr` as an algebraic ZX diagram, or `none` if it is not a
    `ZX n m` term. The `#zx` command uses this to accept algebraic terms
    alongside graph-style `ZXDiagram`s. -/
def zxTermHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  if (matchZXType? (← whnf (← inferType e))).isNone then return none
  return some (← evalAlgHtml e none)

end SpLean.Algebraic
