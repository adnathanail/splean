import LeanSpider.Axioms
import LeanSpider.Visualize

open Lean Elab Tactic Meta

namespace LeanSpider

-- == Evaluation (for visualization only) ==

private unsafe def evalZXDiagramImpl (e : Expr) : MetaM ZXDiagram :=
  Meta.evalExpr ZXDiagram (mkConst ``ZXDiagram) e

@[implemented_by evalZXDiagramImpl]
opaque evalZXDiagram : Expr → MetaM ZXDiagram

private unsafe def evalStringImpl (e : Expr) : MetaM String :=
  Meta.evalExpr String (mkConst ``String) e

@[implemented_by evalStringImpl]
opaque evalString : Expr → MetaM String

-- == Goal parsing ==

/-- Extract LHS and RHS from a goal of the form `d ≈z d'` -/
def parseEquivGoal (goalType : Expr) : TacticM (Expr × Expr) := do
  let goalType ← instantiateMVars goalType
  let some (lhs, rhs) := goalType.app2? ``ZXDiagram.equiv
    | throwError "Goal is not of the form `d ≈z d'`"
  return (lhs, rhs)

-- == Core rewrite tactic ==

/-- Apply a rewrite rule, replacing the goal's LHS with the rewritten diagram.
    Evaluates the rewrite via whnf (works because ZXDiagram uses List). -/
def applyRewrite (label : String) (rewriteFn soundAxiom : Name) (args : Array Expr) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseEquivGoal goalType

  -- Build the rewrite application and reduce via whnf
  let rewriteApp ← mkAppM rewriteFn (#[lhs] ++ args)
  let rewriteReduced ← whnf rewriteApp

  -- Check it returned `.ok d₁`
  let some (_, _, d₁) := rewriteReduced.app3? ``Except.ok
    | do
      -- Try to extract the error message from `.error msg`
      let some (_, _, msgExpr) := rewriteReduced.app3? ``Except.error | throwError "{label} failed"
      let msg ← try
                   let msgReduced ← whnf msgExpr
                   liftM (evalString msgReduced : MetaM String)
                 catch _ => pure s!"{label} failed"
      throwError "{msg}"

  -- New goal: d₁ ≈z rhs
  let newGoalType ← mkAppM ``ZXDiagram.equiv #[d₁, rhs]
  let newGoal ← mkFreshExprMVar newGoalType

  -- Build proof: equiv_trans (soundAxiom lhs args... d₁ rfl) newGoal
  let soundProof ← mkAppM soundAxiom (#[lhs] ++ args ++ #[d₁, ← mkEqRefl rewriteReduced])
  let transProof ← mkAppM ``ZXDiagram.equiv_trans #[soundProof, newGoal]
  goal.assign transProof

  setGoals [newGoal.mvarId!]

-- == General tactics ==

/-- Print the JSON for the current LHS and RHS diagrams to the InfoView. -/
elab "zx_debug" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseEquivGoal goalType
  let dLhs ← evalZXDiagram lhs
  let lhsJson := dLhs.toJson (includeNones := true)
  let mut msg := s!"LHS:\n{lhsJson.pretty}"
  if !rhs.isMVar then
    let dRhs ← evalZXDiagram rhs
    let rhsJson := dRhs.toJson (includeNones := true)
    msg := msg ++ s!"\n\nRHS:\n{rhsJson.pretty}"
  logInfo msg

/-- Close a `d₁ ≈z d₂` goal by normalization (both sides normalize to the same diagram). -/
elab "zx_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseEquivGoal goalType
  -- If the RHS is a metavar (e.g. from zx_explore), unify it with the LHS
  if rhs.isMVar then
    rhs.mvarId!.assign lhs
    let reflProof ← mkAppM ``ZXDiagram.equiv_refl #[lhs]
    goal.assign reflProof
  else
    -- Use decide: evaluates normalize on both sides and compares
    evalTactic (← `(tactic| decide))

/-- Start aimless exploration: introduces `∃ d', diagram ≈z d'` into `diagram ≈z ?d'`.
    Apply rewrites freely and close with `zx_rfl`. -/
elab "zx_explore" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Expect ∃ d', lhs ≈z d'
  let some (_, _) := goalType.app2? ``Exists
    | throwError "Expected goal of the form `∃ d', diagram ≈z d'`"
  -- Introduce the existential with a placeholder witness, reducing to `diagram ≈z ?_`
  evalTactic (← `(tactic| refine Exists.intro ?_ ?_))
  let goals ← getGoals
  -- Goals are [witness : ZXDiagram, proof : lhs ≈z ?_]. Focus on the proof goal.
  setGoals [goals[1]!]
  -- Check the existential's body really is a `≈z` goal.
  let _ ← parseEquivGoal (← (← getMainGoal).getType)

end LeanSpider
