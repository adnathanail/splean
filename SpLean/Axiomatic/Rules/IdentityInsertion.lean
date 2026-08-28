import SpLean.Axiomatic.Axioms
import SpLean.Axiomatic.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.identityInsertion (d : ZXDiagram) (a b : NodeId) (color : SpiderColor)
    : Except String ZXDiagram := do
  unless (d.getNode? a).isSome do throw s!"Node {a} not found"
  unless (d.getNode? b).isSome do throw s!"Node {b} not found"
  unless d.connected a b do throw s!"Nodes {a} and {b} are not connected"
  -- Remove one edge between a and b
  let d := d.removeOneEdge a b
  -- Add new phase-free spider
  let (d, c) := d.addNode (Node.spider color ⟨0, 1⟩)
  -- Connect a—c—b
  let d := d.addEdge (Edge.mk a c)
  let d := d.addEdge (Edge.mk c b)
  return d.normalize

namespace SpLean

axiom ZXDiagram.identityInsertion_sound (d : ZXDiagram) (a b : NodeId)
    (color : SpiderColor) (d' : ZXDiagram) :
  d.identityInsertion a b color = .ok d' → d ≈z d'

/-- `zx_unid <nodeA> <nodeB> X` -/
syntax "zx_unid" num num ident : tactic

elab_rules : tactic
  | `(tactic| zx_unid $a $b $c) => do
    let colorExpr ← match c.getId.toString with
      | "X" => pure (mkConst ``SpiderColor.X)
      | "Z" => pure (mkConst ``SpiderColor.Z)
      | s => throwError "Expected X or Z, got {s}"
    applyRewrite "Identity insertion"
      ``ZXDiagram.identityInsertion ``ZXDiagram.identityInsertion_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat, colorExpr]

end SpLean
