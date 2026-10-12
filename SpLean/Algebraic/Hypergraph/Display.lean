import SpLean.Algebraic.Hypergraph.Defs

/-!
Bare string representation of hypergraphs, for `#eval a.toHyp`

Wires are printed as their bare index.

E.g. `(ZX.spider .Z 1 1 ≫ ZX.wire).toHyp` prints as

```
Hyp 1 1 with 3 wires
  edges:   [Z(0) [0, 1]]
  ids:     [(1, 2)]
  inputs:  [0]
  outputs: [2]
```

i.e.
- one Z spider with phase 0,
- whose legs are wires 0 and 1;
- wires 1 and 2 identified by the composition;
- input port 0 on wire 0 and output port 0 on wire 2.
-/

namespace SpLean.Algebraic.Hypergraph

private def formatList {α : Type} (f : α → Std.Format) (xs : List α) : Std.Format :=
  Std.Format.bracket "[" (Std.Format.joinSep (xs.map f) ("," ++ Std.Format.line)) "]"

private def formatFin {k : ℕ} (i : Fin k) : Std.Format := repr i.val

/-- `Z(φ)`, `X(φ)` or `H`. -/
def Hyp.Label.format : Hyp.Label → Std.Format
  | .spider .Z φ => s!"Z({φ})"
  | .spider .X φ => s!"X({φ})"
  | .hadamard => "H"

instance : Repr Hyp.Label := ⟨fun L _ => L.format⟩

/-- The label followed by the wire on each leg, e.g. `Z(π/2) [0, 1]`. -/
def Hyp.Edge.format {w : ℕ} (e : Hyp.Edge w) : Std.Format :=
  e.label.format ++ " " ++ formatList formatFin (List.ofFn e.legs)

instance {w : ℕ} : Repr (Hyp.Edge w) := ⟨fun e _ => e.format⟩

/-- One field per line: the wire count, then the edges, identified pairs and
boundary as lists. -/
def Hyp.format {n m : ℕ} (H : Hyp n m) : Std.Format :=
  let pair (p : Fin H.wires × Fin H.wires) : Std.Format :=
    "(" ++ formatFin p.1 ++ ", " ++ formatFin p.2 ++ ")"
  s!"Hyp {n} {m} with {H.wires} wires" ++
    Std.Format.nest 2
      (Std.Format.line ++ "edges:   " ++ formatList Hyp.Edge.format (List.ofFn H.edges) ++
       Std.Format.line ++ "ids:     " ++ formatList pair (List.ofFn H.ids) ++
       Std.Format.line ++ "inputs:  " ++ formatList formatFin (List.ofFn H.inputs) ++
       Std.Format.line ++ "outputs: " ++ formatList formatFin (List.ofFn H.outputs))

instance {n m : ℕ} : Repr (Hyp n m) := ⟨fun H _ => H.format⟩

end SpLean.Algebraic.Hypergraph
