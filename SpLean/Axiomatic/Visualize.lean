import SpLean.Axiomatic.Data
import SpLean.Widget

/-! # Drawing a graph-style `ZXDiagram`

The `ZXDiagram → SpLean.Wire.Diagram` lowering. It supplies no positions, so
zxcc lays the graph out itself with its own BFS.

This is the axiomatic representation's *own* renderer. The algebraic one has
its own, in `SpLean/Algebraic/Visualize.lean`; the two meet only at
`SpLean.Wire`. -/

open Lean SpLean ProofWidgets

/-- Human-readable phase string used by the widget. gcd + mod-2π normalize
    via `Phase.simplify`, then format as `π/2`, `-π/4`, `2π/3`, `π`, or `0`. -/
def Phase.format (p : Phase) : String :=
  let p := p.simplify
  if p.num == 0 then "0"
  else
    let ns := if p.num == 1 then "" else if p.num == -1 then "-"
              else toString p.num
    let ds := if p.den.val == 1 then "" else s!"/{p.den.val}"
    s!"{ns}π{ds}"

def SpiderColor.wireName : SpiderColor → String
  | .Z => "Z" | .X => "X"

/-- A Hadamard box carries a phase of π by convention. It is sent explicitly,
    like every other phase — see `Wire.Node.phase`. -/
def hadamardPhase : Phase := ⟨1, 1⟩

/-- Lower one node. -/
def Node.toWire (n : Node) (id : NodeId) : Wire.Node :=
  match n with
  | .spider c p => { id, kind := .spider, color := some c.wireName, phase := some p.format }
  | .hadamard   => { id, kind := .hadamard, phase := some hadamardPhase.format }
  | .wire       => { id, kind := .wire }
  | .input ioId  => { id, kind := .input,  ioId := some ioId }
  | .output ioId => { id, kind := .output, ioId := some ioId }

def Edge.toWire (e : Edge) : Wire.Edge := { src := e.src, tgt := e.tgt }

/-- Lower the diagram, dropping the `none` slots left by `removeNode` — a hole
    is not something to draw. List indices stay the node ids, so the surviving
    ids are unchanged and the edges still refer to them. -/
def ZXDiagram.toWire (d : ZXDiagram) : Wire.Diagram :=
  { nodes := d.nodes.zipIdx.filterMap fun (opt, idx) => opt.map (·.toWire idx)
    edges := d.edges.map Edge.toWire }

/-- Display a `ZXDiagram` in the InfoView, optionally beside a goal diagram. -/
def ZXDiagram.toHtml (d : ZXDiagram) (goal? : Option ZXDiagram := none) : Html :=
  d.toWire.toHtml (goal?.map ZXDiagram.toWire)

/-- The JSON `zx_debug` prints. Unlike `toWire` this keeps the `none` slots,
    as `{"id": i, "type": "none"}` — when you are debugging a rewrite, where
    the holes are is exactly what you want to see. Never sent to the widget:
    `"none"` is not one of zxcc's node types. -/
def ZXDiagram.debugJson (d : ZXDiagram) : Json :=
  let nodes := d.nodes.zipIdx.map fun (opt, idx) =>
    match opt with
    | some n => (n.toWire idx).toJson
    | none   => .mkObj [("id", .num (Int.toNat idx)), ("type", .str "none")]
  .mkObj [("nodes", .arr nodes.toArray),
          ("edges", .arr (d.edges.map (Wire.Edge.toJson ∘ Edge.toWire)).toArray)]
