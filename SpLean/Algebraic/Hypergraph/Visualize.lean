import SpLean.Algebraic.Hypergraph.Defs
import SpLean.Algebraic.AlgPhase.Display
import SpLean.Widget

/-!
# Drawing a `Hyp`

`Hyp → SpLean.Wire.Hypergraph` lowering, for zxcc's `<zx-hypergraph>`.

## 🚨 high potential for buggy visualisation 🚨

The code below attempts to lay out the hypergraph automatically,
  but for large/complex diagrams it will likely fail.

## Identified wires are merged

zxcc draws a ZX diagram's dual, in which every wire is held by at most two
hyperedge ends. A `Hyp` produced by composition keeps both halves of each
merged wire and records the pair in `ids`, so each half is held by only one
end and nothing can be drawn to join them. Each class of identified wires is
therefore drawn as a single dot, labelled with the least wire in the class.

## Layout

`<zx-hypergraph>` does no layout of its own, and a `Hyp` has no record of the
term's geometry, so positions are worked out here. Each blob (generator or
boundary) is given a grid position, and each dot sits at the midpoint of the
two blobs holding it, which is where zxcc's own dual view puts it.

- **Columns:** input `i` is in column 0; a generator is in the column of its
  breadth-first distance from the inputs (column 1 if no input reaches it); the
  outputs are in the column after the last generator.
- **Qubits:** input `i` and output `j` are on qubits `i` and `j`; a generator
  is repeatedly moved to the mean qubit of the blobs it shares a dot with.
  Generators not reached from an input start below the boundaries, so that a
  disconnected scalar does not land on top of the circuit.
-/

namespace SpLean.Algebraic.Hypergraph

open SpLean

/-- How many rounds of averaging place the generators' qubits. -/
private def qubitRounds : Nat := 50

/-- The wire-format hypergraph of `H`, with identified wires merged and every
dot placed. Blob ids are the generators' indices, then `edgeCount + i` for
input `i`, then `edgeCount + n + j` for output `j`. -/
def Hyp.toWire {n m : ℕ} (H : Hyp n m) : Wire.Hypergraph := Id.run do
  -- The representative of each wire: the least wire identified with it.
  let mut rep : Array Nat := Array.range H.wires
  for (a, b) in List.ofFn H.ids do
    let (ra, rb) := (rep[a.val]!, rep[b.val]!)
    let (lo, hi) := (min ra rb, max ra rb)
    rep := rep.map fun r => if r == hi then lo else r
  -- One dot per class; `dotOf v` is the position of wire `v`'s dot.
  let reps := (List.range H.wires).filter fun v => rep[v]! == v
  let dotOf (v : Nat) : Nat := reps.idxOf rep[v]!

  let k := H.edgeCount
  let blobCount := k + n + m
  -- The dots held by each blob, in leg order.
  let held : Array (List Nat) :=
    (List.ofFn fun i => (List.ofFn (H.edges i).legs).map (dotOf ·.val)) ++
    (List.ofFn fun i => [dotOf (H.inputs i).val]) ++
    (List.ofFn fun j => [dotOf (H.outputs j).val]) |>.toArray
  -- The blobs holding each dot, one entry per end.
  let mut holders : Array (List Nat) := Array.replicate reps.length []
  for b in [0:blobCount] do
    for d in held[b]! do
      holders := holders.modify d (· ++ [b])
  -- Blobs sharing a dot with blob `b`, with multiplicity, excluding `b`.
  let neighbours (b : Nat) : List Nat :=
    held[b]!.flatMap fun d => holders[d]!.filter (· != b)

  -- Columns, by breadth-first search from the inputs over the generators.
  let mut col : Array (Option Nat) := Array.replicate blobCount none
  let mut queue : List Nat := []
  for i in [0:n] do
    col := col.set! (k + i) (some 0)
    queue := queue ++ [k + i]
  while !queue.isEmpty do
    let b := queue.head!
    queue := queue.tail
    let c := col[b]!.getD 0
    for b' in neighbours b do
      if b' < k && col[b']!.isNone then
        col := col.set! b' (some (c + 1))
        queue := queue ++ [b']
  let lastCol := (List.range k).foldl (fun acc i => max acc (col[i]!.getD 1)) 0
  for j in [0:m] do
    col := col.set! (k + n + j) (some (lastCol + 1))

  -- Qubits: boundaries fixed, generators averaged towards their neighbours.
  let mut qubit : Array Float := Array.replicate blobCount 0
  let mut below := (max n m).toFloat
  for i in [0:k] do
    if col[i]!.isNone then
      qubit := qubit.set! i below
      below := below + 1
  for i in [0:n] do qubit := qubit.set! (k + i) i.toFloat
  for j in [0:m] do qubit := qubit.set! (k + n + j) j.toFloat
  for _ in [0:qubitRounds] do
    for i in [0:k] do
      let ns := neighbours i
      unless ns.isEmpty do
        qubit := qubit.set! i ((ns.map (qubit[·]!)).sum / ns.length.toFloat)

  let pos (b : Nat) : Float × Float := ((col[b]!.getD 1).toFloat, qubit[b]!)
  let wires := reps.zipIdx.map fun (v, d) =>
    let (c, q) := match holders[d]! with
      | [a, b] =>
        if a == b then
          -- A self-loop: just above the blob holding both its ends.
          let (c, q) := pos a; (c, q - 0.5)
        else
          let ((ca, qa), (cb, qb)) := (pos a, pos b); ((ca + cb) / 2, (qa + qb) / 2)
      | a :: _ => pos a
      | [] => (0, 0)
    { id := v, col := c, qubit := q : Wire.HypWire }

  let generators := (List.ofFn H.edges).zipIdx.map fun (e, i) =>
    let (kind, phase) := match e.label with
      | .spider .Z φ => (Wire.HyperedgeKind.zSpider, some φ.format)
      | .spider .X φ => (.xSpider, some φ.format)
      | .hadamard => (.hadamard, none)
    { id := i, kind, wires := held[i]!, phase : Wire.Hyperedge }
  let inputs := (List.range n).map fun i =>
    { id := k + i, kind := .boundary, wires := held[k + i]!, name := s!"in{i}" : Wire.Hyperedge }
  let outputs := (List.range m).map fun j =>
    { id := k + n + j, kind := .boundary, wires := held[k + n + j]!, name := s!"out{j}" : Wire.Hyperedge }
  return { wires, hyperedges := generators ++ inputs ++ outputs }

end SpLean.Algebraic.Hypergraph
