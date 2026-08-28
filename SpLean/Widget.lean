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

/-- A translucent rectangle drawn behind a set of nodes. `kind` is zxcc's
    `BoxKind`: `"stack"` or `"compose"`. Pixel bounds are computed by zxcc
    from the nodes' live positions, so boxes follow drags. -/
structure Box where
  kind : String
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
  .mkObj [("kind", .str b.kind), ("nodeIds", .arr (b.nodeIds.map natJson).toArray)]

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

end SpLean.Wire
