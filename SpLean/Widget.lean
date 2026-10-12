import ProofWidgets.Component.HtmlDisplay

/-! # The zxcc wire format

A Lean mirror of the `DiagramData` interface in `@adnathanail/zxcc`'s
`types.d.ts`, together with the ProofWidgets component that consumes it.

This is a data-transfer type, not a ZX one.
It has no `Phase` and no `SpiderColor`:
- a phase has already become the text to draw and
- a colour has already become `"Z"` or `"X"`.
Nothing here knows that a diagram means anything.

This is the only interaction surface for zxcc, so version bumps should be asy
-/

open Lean Server ProofWidgets

namespace SpLean.Wire

/-- zxcc's `DiagramNodeType`, restricted to the kinds this project emits.
    (zxcc also knows `w-input`, `w-output` and `z-box`.) -/
inductive NodeKind where
  | spider | input | output | hadamard | wire
  deriving Repr, DecidableEq, Inhabited

def NodeKind.name : NodeKind → String
  | .spider => "spider" | .input => "input" | .output => "output"
  | .hadamard => "hadamard" | .wire => "wire"

/-- One entry of zxcc's `nodes` array. Every `Option` field is *omitted* from
    the JSON when `none` rather than sent as null, which is what zxcc's `?:`
    fields expect. -/
structure Node where
  id : Nat
  kind : NodeKind
  /-- `"Z"` or `"X"`. Spiders only. -/
  color : Option String := none
  /-- Display-ready phase text, printed verbatim.

      Every node that *has* a phase sends it, including a spider's `"0"` and a
      Hadamard's `"π"`. zxcc draws no text for either of those, and it also
      defaults an absent Hadamard phase to `"π"` — so omitting them would
      render identically. Don't. Whether a phase is worth drawing is a
      rendering decision and belongs at the end of the pipeline, in zxcc,
      where it can be changed for every producer at once; a lowering that
      pre-empts it has quietly moved that decision here.

      `none` means the node has no phase at all: a boundary or a wire. -/
  phase : Option String := none
  /-- Boundary index. `input`/`output` only. -/
  ioId : Option Nat := none
  /-- Pre-computed column. When *any* node carries `col`, zxcc skips its own
      layout entirely, so a diagram supplies positions for all of its nodes
      or for none of them. -/
  col : Option Int := none
  /-- Pre-computed row. May be a half-integer — see `qubitOfHalves`. -/
  qubit : Option JsonNumber := none
  deriving Repr, Inhabited

/-- The qubit `h/2`: `1 ↦ 0.5`, `2 ↦ 1`, `3 ↦ 1.5`. Callers that lay diagrams
    out on half-rows (so that a spider with mismatched arity can sit centred
    on its span) count in halves throughout and encode once, here. -/
-- `JsonNumber` is `mantissa * 10 ^ -exponent` with `exponent : Nat`, so
-- `mantissa = 5h, exponent = 1` is `h/2`.
def qubitOfHalves (h : Nat) : JsonNumber := { mantissa := (h : Int) * 5, exponent := 1 }

structure Edge where
  src : Nat
  tgt : Nat
  deriving Repr, Inhabited

/-- zxcc's `BoxKind`. Closed, unlike `DiagramEdgeKind`, which zxcc leaves open
    to arbitrary strings — a box kind picks the label and styling of a
    rectangle it knows how to draw. -/
inductive BoxKind where
  | stack | compose
  deriving Repr, DecidableEq, Inhabited

def BoxKind.name : BoxKind → String
  | .stack => "stack" | .compose => "compose"

/-- A translucent rectangle drawn behind a set of nodes. Pixel bounds are
    computed by zxcc from the nodes' live positions, so boxes follow drags. -/
structure Box where
  kind : BoxKind
  nodeIds : List Nat
  deriving Repr, Inhabited

/-- zxcc's `DiagramData`.

    zxcc also accepts a `labels` array that overrides the text drawn beside a
    node, and a `pauliWeb`/`scalar` pair. None are mirrored here: a phase is
    already free text by the time it reaches `Node.phase`, so `labels` would
    be a second way to say the same thing, and nothing in this project emits
    the other two. Add them when something does. -/
structure Diagram where
  nodes : List Node
  edges : List Edge
  /-- Omitted from the JSON when empty. -/
  boxes : List Box := []
  deriving Repr, Inhabited

/-! ## Hypergraphs

A mirror of zxcc's `HypergraphInput`, which `<zx-hypergraph>` draws exactly as
given: zxcc lays nothing out here, so every dot carries its position. -/

/-- zxcc's `HyperedgeKind`: which shape and colour a blob is drawn with. -/
inductive HyperedgeKind where
  | zSpider | xSpider | hadamard | boundary
  deriving Repr, DecidableEq, Inhabited

def HyperedgeKind.name : HyperedgeKind → String
  | .zSpider => "z-spider" | .xSpider => "x-spider"
  | .hadamard => "hadamard" | .boundary => "boundary"

/-- One entry of `wires`, drawn as a dot on the column/qubit grid. Grid
    coordinates may be fractional, and are read relative to the lowest. -/
structure HypWire where
  /-- What `show-labels` writes under the dot. Must be unique. -/
  id : Nat
  col : Float
  qubit : Float
  deriving Repr, Inhabited

/-- One entry of `hyperedges`, drawn as a blob around the dots it holds. -/
structure Hyperedge where
  /-- Must be unique among the hyperedges. -/
  id : Nat
  kind : HyperedgeKind
  /-- Positions in `Hypergraph.wires` (not wire ids). A position listed twice is a self-loop. -/
  wires : List Nat
  /-- What `show-labels` writes beside the blob. zxcc defaults it to the letter
      for the kind, and to nothing for a boundary. -/
  name : Option String := none
  /-- Display-ready phase text, as for `Node.phase`. -/
  phase : Option String := none
  deriving Repr, Inhabited

/-- zxcc's `HypergraphInput`. Every wire must be held by one or two hyperedge
    ends; zxcc draws an error in place of the picture otherwise. -/
structure Hypergraph where
  wires : List HypWire
  hyperedges : List Hyperedge
  deriving Repr, Inhabited

-- == JSON ==

private def natJson (n : Nat) : Json := .num { mantissa := (n : Int), exponent := 0 }
private def intJson (n : Int) : Json := .num { mantissa := n, exponent := 0 }

/-- Keep only the fields that are `some`, so an absent optional stays absent
    instead of becoming `null`. -/
private def someFields (fs : List (String × Option Json)) : List (String × Json) :=
  fs.filterMap fun (k, v?) => v?.map (k, ·)

def Node.toJson (n : Node) : Json :=
  .mkObj ([("id", natJson n.id), ("type", .str n.kind.name)] ++
    someFields [("color", n.color.map .str), ("phase", n.phase.map .str),
                ("ioId", n.ioId.map natJson), ("col", n.col.map intJson),
                ("qubit", n.qubit.map .num)])

def Edge.toJson (e : Edge) : Json :=
  .mkObj [("src", natJson e.src), ("tgt", natJson e.tgt)]

def Box.toJson (b : Box) : Json :=
  .mkObj [("kind", .str b.kind.name), ("nodeIds", .arr (b.nodeIds.map natJson).toArray)]

def HypWire.toJson (w : HypWire) : Json :=
  .mkObj [("id", natJson w.id), ("col", Lean.toJson w.col), ("qubit", Lean.toJson w.qubit)]

def Hyperedge.toJson (h : Hyperedge) : Json :=
  .mkObj ([("id", natJson h.id), ("kind", .str h.kind.name),
           ("wires", .arr (h.wires.map natJson).toArray)] ++
    someFields [("name", h.name.map .str), ("phase", h.phase.map .str)])

def Hypergraph.toJson (h : Hypergraph) : Json :=
  .mkObj [("wires", .arr (h.wires.map HypWire.toJson).toArray),
          ("hyperedges", .arr (h.hyperedges.map Hyperedge.toJson).toArray)]

def Diagram.toJson (d : Diagram) : Json :=
  .mkObj ([("nodes", .arr (d.nodes.map Node.toJson).toArray),
           ("edges", .arr (d.edges.map Edge.toJson).toArray)] ++
    (if d.boxes.isEmpty then [] else [("boxes", .arr (d.boxes.map Box.toJson).toArray)]))

-- == The ProofWidgets component ==

/-- Props passed to the widget: the diagram to draw and, optionally, a goal
    diagram to show beside it (`null` = not shown). -/
structure ZXWidgetProps where
  diagram : Json
  goal : Json := .null
  deriving RpcEncodable

@[widget_module]
def ZXWidget : Component ZXWidgetProps where
  javascript := include_str ".." / ".lake" / "build" / "js" / "zxDiagram.js"

/-- Draw a diagram in the InfoView, optionally beside a goal diagram. -/
def Diagram.toHtml (d : Diagram) (goal? : Option Diagram := none) : Html :=
  Html.ofComponent ZXWidget ⟨d.toJson, goal?.elim .null Diagram.toJson⟩ #[]

structure ZXHypergraphWidgetProps where
  hypergraph : Json
  deriving RpcEncodable

@[widget_module]
def ZXHypergraphWidget : Component ZXHypergraphWidgetProps where
  javascript := include_str ".." / ".lake" / "build" / "js" / "zxHypergraph.js"

/-- Draw a hypergraph in the InfoView. -/
def Hypergraph.toHtml (h : Hypergraph) : Html :=
  Html.ofComponent ZXHypergraphWidget ⟨h.toJson⟩ #[]

end SpLean.Wire
