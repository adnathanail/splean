# SpLean.Algebraic

A free-algebra ZX representation (`ZX n m`, indexed by input/output arity),
living *alongside* the graph-style `ZXDiagram`. There is a one-way
`ZX → ZXDiagram` translation for **rendering only** (`Visualize.lean` — see
below); the `Axiomatic/Rules/*` rewrite machinery still operates on `ZXDiagram` directly.

## Scope on this branch

This module is currently **structure and rendering only** — `ZX.lean` (the
ADT), `Visualize.lean` (pure lowering to a positioned diagram), and
`Render.lean` (the `MetaM` glue for `#zx`). There is no denotational semantics
here: no `ZX.sem`, no `≃ZX`, no `Semantics.lean`, no `SpiderFusion.lean`.

Those live on the stacked `algebraic-semantics` branch, and are the *reason*
this module exists: `SpLean/Axiomatic/Axioms.lean` defines `≈z` as syntactic equality
after compaction, which is too weak to prove rewrite-rule soundness, so every
rule in `SpLean/Axiomatic/Rules/` is axiomatised. A semantic equivalence (matrix
equality) is what lets those rules be proved outright. Do not document that
work as present here — check what the branch actually contains before writing
about semantics.

## Conventions

- **Composition order**: `compose a b` reads "first `a`, then `b`". Written
  `a ≫ b`; stacking is `a ⊗ b`. Both are `scoped` notation, so a file needs
  `open SpLean.Algebraic` (see `Main.lean`).
- **`spider c n m φ`** takes its phase last and defaults it to `0`, so a
  phase-free spider is just `.spider .Z 1 2`.

## Visualization (`Visualize.lean`, `Render.lean`)

`ZX.toHtml` renders an algebraic term in the existing `ZXWidget`.
`Visualize.lean` is the pure part (term → positioned diagram → `Html`);
`Render.lean` is the `MetaM` part that turns a `ZX n m` *`Expr`* into `Html`,
so `#zx myAlgTerm` displays algebraic terms at the top level the same way it
displays a `ZXDiagram`. Arity is recovered from `Meta.inferType`: the term
itself isn't evaluable because `ZX n m` is index-dependent, but the `Html`
application is.

The walker threads a private `Frag` (diagram + open `left`/`right` port lists,
each port paired with the qubit-in-halves at which it enters/leaves the body,
+ `(width, height, pos, boxes)`) through the constructors. Every node carries
an algebraic-grid `(col, qubitHalves)` position emitted alongside the JSON, so
the renderer skips its own layout and the visual reflects the term's
structure. Each `stack`/`compose` subtree also records a `BoxRecord` covering
its extent, drawn as a translucent rectangle behind the diagram so the
algebraic nesting is visible at a glance.

Qubit positions are stored internally as `2 ×` the actual qubit (i.e.
"halves") so a spider with mismatched arity (e.g. `Z 1→2`) can sit on a
half-row at the centre of its span. The structural `Frag.height` stays a count
of integer slots; `stack` shifts the lower fragment's qubits by
`2 * a.height`. JSON emission divides by two — `qubit` is a real number
(e.g. `0.5`, `1`, `1.5`) on the wire.

Per-constructor layout (all qubit values are halves; `centre = max(n, m) - 1`
is the midpoint of slots `0..max-1` in halves):

- `wire` → one `.wire` node at `(col 0, q 0)`, drawn as a small dot. Wires
  stay as real nodes so that `stack`/`compose` boxes around them are
  non-empty and the visual extent of a subtree matches its algebraic shape.
  `left = right = [(id, 0)]`, width 1, height 1.
- `hadamard` → one `.hadamard` node at `(col 0, q 0)`. `left = right = [(id, 0)]`,
  width 1, height 1.
- `spider c n m φ` → one node at `(col 0, q centre)` (centre of its span).
  Each port is paired with its qubitHalves: when the arity is `1` the lone
  port sits at `centre` (so a single-leg connection is horizontal); when
  arity > 1 the ports occupy integer slots `0, 2, …, 2(k-1)`. Width 1,
  height `max n m`.
- `stack a b` → concatenate; shift `b`'s qubitHalves by `2 * a.height`.
  Width `max a.width b.width`, height `a.height + b.height`.
- `compose a b` → connect `a.right` to `b.left` (by node id, qubits do not
  need to match) and shift `b`'s cols by `a.width`. Width `a.width + b.width`,
  height `max a.height b.height`.

`stack` and `compose` each emit a `BoxRecord {kind, nodeIds}` listing the ids
of every node in their subtree (with appropriate shifts on `compose`/`stack`).
Leaves emit no box. `algebraicJson` emits every box verbatim — it does no
filtering. Pixel bounds are computed by the renderer from each node's live
position, so boxes follow drags.

Boundary `.input`/`.output` nodes are added **only** at the top level by
`ZX.toPositionedDiagram`. Each boundary inherits the qubit of the body port
it connects to: input `i` sits at `(col -1, q (f.left[i].2))`, and output
`j` at `(col width, q (f.right[j].2))`. So a top-level input feeding a
`Z 1→2` spider lands on the spider's centred half-row, and an input feeding
a wire that has been pushed downward by a sibling stack lands at that wire's
shifted qubit — no big diagonal jumps from the boundary into the body.
Internal fragments stay arity-pure during recursion.

The JSON shape extends `ZXDiagram.toJson` with `col` (Int) and `qubit`
(real number, possibly half-integer) fields per node, plus a top-level
`boxes` array of `{kind, nodeIds}` records.

## Where the drawing actually happens

Layout and SVG rendering are **not in this repo** — they live in the
[zxcc](https://github.com/adnathanail/zxcc) web component, consumed as the
`@adnathanail/zxcc` npm package by `zx_view_widget/`. This module's only job
is to emit JSON that zxcc understands (`DiagramData` in its `types.d.ts`:
`col`, `qubit`, `boxes`, `labels`, …). zxcc skips its BFS auto-layout whenever
any node carries `col`, turns off H-box barycentre repositioning in that case
so supplied positions aren't overwritten, and sorts boxes largest-first so
outer ones paint behind inner ones.

Changing how any of that *looks* means changing zxcc and releasing a new
version, not editing anything here.

## Not proved

`ZX.toZXDiagram` (used by callers that just need the graph) delegates to
`ZX.toPositionedDiagram` and discards the position list. Rendering-only —
there is no proof that the lowering preserves semantics (that would need a
`ZXDiagram` denotation, which doesn't exist yet).
