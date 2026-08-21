import SpLean.Algebraic.SpiderFusion
import SpLean.Algebraic.Congruence
import SpLean.Algebraic.Rewrite
import SpLean.Algebraic.Render
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Tactic Meta ProofWidgets

namespace SpLean.Algebraic

/-- Parse a goal of the form `lhs ≃ZX rhs` into its sides.
    `ZX.equiv` has signature `{n m} → ZX n m → ZX n m → Prop` so the
    elaborated expression is `@ZX.equiv n m lhs rhs` — 4 args. -/
def parseAlgEquivGoal (goalType : Expr) : TacticM (Expr × Expr) := do
  let goalType ← instantiateMVars goalType
  let (fn, args) := (goalType.getAppFn, goalType.getAppArgs)
  if fn.constName? == some ``ZX.equiv && args.size == 4 then
    return (args[2]!, args[3]!)
  throwError "Goal is not of the form `lhs ≃ZX rhs` (got: {goalType})"


/-- Log a widget showing `lhs` on the `Current` panel and (when concrete)
    `rhs?` on the `Goal` panel. Render failures are downgraded to a warning
    so visualization never blocks an otherwise-successful proof. -/
def showAlgDiagram (stx : Syntax) (label : String)
    (lhs : Expr) (rhs? : Option Expr := none) : TacticM Unit := do
  let rhs? := rhs?.filter (fun r => !r.isMVar)
  try
    let html ← evalAlgHtml lhs rhs?
    let msg ← Lean.MessageData.ofHtml html label
    logInfoAt stx msg
  catch e =>
    logWarningAt stx m!"could not render ZX diagram: {e.toMessageData}"

/-- Walk a `ZX n m` expression in the same DFS order as `buildFrag` in
    `Visualize.lean`, building both the rewritten term and a proof
    `original ≃ZX rewritten`. At the target `compose` (whose children
    have node IDs `idA` and `idB`), applies `Z_spiderFusion` with the raw
    summed phase `α + β` — no fast-path simplification, since `AlgPhase = ℚ`
    handles phase arithmetic via `abel`/`ring`/`norm_num` at the user's
    discretion.

    Returns `(rewritten, proof, endOffset)`. -/
partial def buildFusionProof (z : Expr) (idA idB : Nat) (off : Nat) :
    MetaM (Expr × Expr × Nat) := do
  let z ← whnf z
  let f := z.getAppFn
  let name := f.constName?
  match name with
  | some ``ZX.empty =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off)
  | some ``ZX.wire =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.hadamard =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.spider =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.stack =>
      -- @ZX.stack n m p q a b — args 4 and 5 are the children
      let args := z.getAppArgs
      let a := args[4]!
      let b := args[5]!
      let (a', proofA, off1) ← buildFusionProof a idA idB off
      let (b', proofB, off2) ← buildFusionProof b idA idB off1
      let stacked ← mkAppM ``ZX.stack #[a', b']
      let proof ← mkAppM ``ZX.stack_congr #[proofA, proofB]
      return (stacked, proof, off2)
  | some ``ZX.compose =>
      -- @ZX.compose n m k a b — args 3 and 4 are the children
      let args := z.getAppArgs
      let a := args[3]!
      let b := args[4]!
      let offA := off
      -- Walk a first to determine offB
      let (a', proofA, offB) ← buildFusionProof a idA idB offA
      if offA == idA && offB == idB then
        -- Target compose. Reach for Z_spiderFusion. Extract n, k, α, β
        -- from the spiders a and b directly. Both are leaves (nodeCount 1),
        -- so the end offset is just offB + 1.
        let aWhnf ← whnf a
        let bWhnf ← whnf b
        let aArgs := aWhnf.getAppArgs   -- @ZX.spider .Z n 1 α
        let bArgs := bWhnf.getAppArgs   -- @ZX.spider .Z 1 k β
        unless aWhnf.getAppFn.constName? == some ``ZX.spider
            && bWhnf.getAppFn.constName? == some ``ZX.spider
            && aArgs.size == 4 && bArgs.size == 4 do
          throwError "Nodes {idA} and {idB} are adjacent under a `compose`, \
                     but the pair is not a fuseable Z-spider junction."
        let n := aArgs[1]!
        let α := aArgs[3]!
        let k := bArgs[2]!
        let β := bArgs[3]!
        let colorZ := mkConst ``SpiderColor.Z
        let proof ← mkAppM ``Z_spiderFusion #[n, k, α, β]
        let sumPhase ← mkAppM ``HAdd.hAdd #[α, β]
        let fused ← mkAppM ``ZX.spider #[colorZ, n, k, sumPhase]
        return (fused, proof, offB + 1)
      else
        let (b', proofB, offEnd) ← buildFusionProof b idA idB offB
        let composed ← mkAppM ``ZX.compose #[a', b']
        let proof ← mkAppM ``ZX.compose_congr #[proofA, proofB]
        return (composed, proof, offEnd)
  | _ => throwError "Unrecognized ZX expression head: {name}"

/-- The main tactic engine — mirrors `applyRewrite` in
    `SpLean/Tactics.lean` but for `≃ZX`. -/
def applyZxAlgFusion (idA idB : Nat) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseAlgEquivGoal goalType
  -- Build the rewrite proof
  let (lhs', proof, _) ← buildFusionProof lhs idA idB 0
  -- New residual goal: lhs' ≃ZX rhs
  let newGoalType ← mkAppM ``ZX.equiv #[lhs', rhs]
  let newGoal ← mkFreshExprMVar newGoalType
  -- Combined proof: equiv_trans (lhs ≃ZX lhs') (lhs' ≃ZX rhs)
  let trans ← mkAppM ``ZX.equiv_trans #[proof, newGoal]
  goal.assign trans
  setGoals [newGoal.mvarId!]

elab tk:"zx_alg_fusion " idA:num idB:num : tactic => do
  applyZxAlgFusion idA.getNat idB.getNat
  withMainContext do
    let goalType ← (← getMainGoal).getType
    let (lhs', rhs) ← parseAlgEquivGoal goalType
    showAlgDiagram tk "After spider fusion" lhs' (some rhs)

/-- Close a goal `ZX.spider c n m α ≃ZX ZX.spider c n m β` whose two phases
    are concrete `AlgPhase` (ℚ) values differing by `2k` for some integer `k`.

    Strategy: evaluate both phases as ℚ; compute `k := (β - α) / 2` and verify
    it's an integer. Combine `ZX.spider_phase_mod_two α k` (which gives
    `spider c n m α ≃ZX spider c n m (α + 2*k)`) with the residual equality
    `α + 2*k = β` (closed by `unfold phaseLit; push_cast; ring`).

    Fails when either phase is symbolic — for those, write the periodicity
    application by hand. -/
elab "zx_mod_two" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseAlgEquivGoal goalType
  let lhsW ← whnf lhs
  let rhsW ← whnf rhs
  let lhsArgs := lhsW.getAppArgs
  let rhsArgs := rhsW.getAppArgs
  unless lhsW.getAppFn.constName? == some ``ZX.spider
       && rhsW.getAppFn.constName? == some ``ZX.spider
       && lhsArgs.size == 4 && rhsArgs.size == 4 do
    throwError "zx_mod_two: expected `ZX.spider _ _ _ _ ≃ZX ZX.spider _ _ _ _`, got {goalType}"
  let cE := lhsArgs[0]!
  let nE := lhsArgs[1]!
  let mE := lhsArgs[2]!
  let αE := lhsArgs[3]!
  let βE := rhsArgs[3]!
  let some αVal ← tryEvalAlgPhase αE
    | throwError "zx_mod_two: could not evaluate LHS phase to a concrete ℚ ({αE})"
  let some βVal ← tryEvalAlgPhase βE
    | throwError "zx_mod_two: could not evaluate RHS phase to a concrete ℚ ({βE})"
  let diff := βVal - αVal
  let kQ := diff / 2
  unless kQ.den == 1 do
    throwError "zx_mod_two: phase difference {diff} is not an integer multiple of 2 \
                (β − α)/2 = {kQ})"
  let k : ℤ := kQ.num
  let kE : Expr := Lean.toExpr k
  let modProof ← mkAppOptM ``ZX.spider_phase_mod_two
    #[some cE, some nE, some mE, some αE, some kE]
  -- Direct application works whenever the kernel reduces `α + 2*k` to `β`.
  if ← isDefEq (← inferType modProof) goalType then
    goal.assign modProof
    return
  -- Fallback: build the residual `α + 2*k = β` equality and discharge by
  -- `unfold phaseLit; push_cast; ring`, then bridge via `spider_eq_of_phase_eq`.
  let modType ← inferType modProof
  let (_, modRhs) ← parseAlgEquivGoal modType
  let modRhsArgs := modRhs.getAppArgs
  let shiftedβ := modRhsArgs[3]!
  let eqType ← mkAppM ``Eq #[shiftedβ, βE]
  let eqMVar ← mkFreshExprMVar eqType
  let congProof ← mkAppOptM ``spider_eq_of_phase_eq
    #[some cE, some nE, some mE, some shiftedβ, some βE, some eqMVar]
  let finalProof ← mkAppM ``ZX.equiv_trans #[modProof, congProof]
  goal.assign finalProof
  setGoals [eqMVar.mvarId!]
  evalTactic (← `(tactic|
    (first
      | rfl
      | (unfold SpLean.Algebraic.phaseLit; push_cast; ring))))

end SpLean.Algebraic
