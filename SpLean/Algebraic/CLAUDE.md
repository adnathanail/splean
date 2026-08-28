# SpLean.Algebraic

A free-algebra ZX representation (`ZX n m`, indexed by input/output arity),
living *alongside* the graph-style `ZXDiagram` and sharing nothing with it.
This module renders straight to the zxcc wire format (`Visualize.lean` — see
below); the `Axiomatic/Rules/*` rewrite machinery operates on `ZXDiagram` and
renders through its own lowering.

## Scope

This module holds the `ZX n m` ADT (`ZX.lean`), its phase type (`AlgPhase/`),
a denotational semantics (`Semantics.lean`), the equivalence proved against it
(`Equiv.lean` + `Rules/`) and the tactic that rewrites with it
(`Tactics.lean`), a handful of named gates (`Gate.lean`), and the rendering
path (`Visualize.lean` + `Render.lean`).

### The semantics

`ZX.sem` denotes a term as a boundary tensor
`(Fin n → Bool) → (Fin m → Bool) → ℂ` — one complex amplitude per assignment of
Booleans to the open wires — rather than as a `Matrix (Fin (2^m)) (Fin (2^n)) ℂ`.
That choice is load-bearing: `stack` splits a boundary assignment with
`Fin.castAdd`/`Fin.natAdd` and `compose` is a `Fintype` sum over the shared
boundary, so no `2^(n+p)` cast lemmas ever appear. It is also the
tensor-network view, which is the right vocabulary for the planned
hypergraph-isomorphism work: permuting wires becomes reindexing a sum (an
`Equiv`), not conjugating a matrix. `xSpiderSem` is *defined* as `zSpiderSem`
conjugated by Hadamards on every wire, so colour-change facts should be proved
through that route rather than from scratch.

### The equivalence

`Equiv.lean` defines `a ≈zx b` as proportionality — VyZX's `∝` — namely
`∃ c ≠ 0, ∀ f g, a.sem f g = c * b.sem f g`. Equality up to a nonzero global
scalar, not on the nose, because ZX rules are only true up to scalars: `(Z0)-`
denotes `√2|+⟩`, not `|+⟩`. The scalar is currently *discarded* rather than
tracked, which is why the definition is an `∃`; recovering it (so that a chain
of rewrites reports the accumulated factor) is the `TODO` on the definition.

`refl`/`symm`/`trans` are proved, and `compose_congr`/`stack_congr` say `≈zx` is
a congruence for `≫` and `⊗` — which is what lets a rule fire inside a larger
diagram. See the root `CLAUDE.md` for how `zx_rw` uses them.

`Rules/` proves rules against `sem` rather than assuming them.
`Rules/SpiderFusion.lean` has Z and X fusion; both come out with `c = 1`, and X
fusion goes through the Hadamard-conjugated definition of `xSpiderSem` rather
than being proved from scratch. Note that fusion is stated only for
`(n,1) ≫ (1,m)` — spiders joined by *k* parallel wires do not follow from it,
and that is the shape the axiomatic rule actually covers.
`Rules/Lemmas.lean` holds the shared sum-collapsing machinery (`sum_wires1`,
the `sum_bool_*` endpoint lemmas, the `√2` arithmetic), moved here out of
`SemanticsTesting/Utils.lean` when the rules started needing it.

### What is not here yet

Nothing connects this module to `SpLean/Axiomatic/`: `≈z` there is still
syntactic equality after compaction, which is too weak to prove rewrite-rule
soundness, so every rule in `SpLean/Axiomatic/Rules/` remains axiomatised.
Proving those rules instead of assuming them is the *reason* this module
exists, and the machinery is now in place on this side, but the bridge is not
built — check what the tree actually contains before writing about it.

### `SemanticsTesting/`

`ZX.sem` is exercised by the separate `SemanticsTesting` lake library (not part
of `SpLean`, not imported by `SpLean.All`), which pins concrete denotations
against Mathlib vectors and matrices: the empty diagram and wire, scalars, Z
spiders (plus/minus/Bell/GHZ states, Z rotation), X spiders, Hadamard, and
`compose`/`stack` — including the Hadamard Euler decomposition. `08Equiv.lean`
and `09Rules.lean` then exercise `≈zx` and `zx_rw` themselves, so a change to
the tactic fails the build rather than being found later.

`SemanticsTesting/Utils.lean` holds what is only useful for pinning concrete
denotations: the `wiresVec*`/`wiresMat*` coercions that let a goal be stated as
`!![1, 0; 0, -1]`. The lemmas the *rules* also need — `sum_wires1` and friends
— live in `SpLean/Algebraic/Rules/Lemmas.lean` and are imported back here.

## Conventions

- **Composition order**: `compose a b` reads "first `a`, then `b`". Written
  `a ≫ b`; stacking is `a ⊗ b`. Both are `scoped` notation, so a file needs
  `open SpLean.Algebraic` (see `Main.lean`).
- **`spider c n m φ`** takes its phase last and defaults it to `0`, so a
  phase-free spider is just `.spider .Z 1 2`.
- **A spider's colour here is `AlgSpColor`**, not the `SpiderColor` in
  `Axiomatic/ZXDiagram.lean`. Same two constructors, deliberately duplicated: it
  was the last thread tying the two representations together and it bought
  nothing, since this one only ever becomes a `"Z"`/`"X"` on the wire. The
  names differ so that neither has to be identified by its namespace.

## Visualization (`Visualize.lean`, `Render.lean`)

`#zx myAlgTerm` renders an algebraic term in the existing widget.
`Visualize.lean` is the pure part (skeleton → `SpLean.Wire.Diagram` → `Html`);
`Render.lean` is the `MetaM` part that turns a `ZX n m` *`Expr`* into that
skeleton.

This module owns its rendering end to end. It has **no** dependency on
`SpLean/Axiomatic/` — not on `ZXDiagram`, not on `Node`, not on `Phase`, and
not even on `SpiderColor` — `ZX.lean` defines its own `AlgSpColor`. The only shared
thing is `SpLean/Widget.lean`, the zxcc wire format, which is a JSON DTO
rather than a ZX type. Keep it that way: if something here starts wanting a
graph-style type, the answer is a lowering into `Wire`, not an import.

### The skeleton, and parametric phases

Both halves meet at `ZXSkel`: an arity-erased mirror of `ZX n m` whose spiders
carry the *text* to draw (a `String`) rather than a phase value. There is
exactly one way in — `Render.lean`'s `zxSkelOfExpr`, which walks the `Expr`
constructor by constructor (`whnf` between steps, so an `abbrev` naming a
subdiagram is transparent). Nothing builds a skeleton from a `ZX n m` *value*:
there was a `ZX.toSkel` doing that, but once `#zx` walked `Expr`s it had no
callers, so a value goes through the walker like everything else.

Not evaluating the term as a whole is what lets a *parameterized* diagram be
drawn: `zxTermHtml?` binds any leading `∀`s with `forallTelescopeReducing`, so
`#zx greenAlphaCircle` — of type `(α : AlgPhase) → ZX 0 0` — draws a Z spider
labelled `α`. A phase argument mentioning no free or metavariable is evaluated
and formatted with `AlgPhase.format`, so what the viewer draws is exactly what
`AlgPhase`'s own `Repr` says. (Rendering used to convert to the graph-style
`Phase` first, which normalizes mod 2π, so the viewer drew `7π/4` where
`format` promised `-π/4`. That conversion is gone along with the dependency.)
Anything else becomes its own pretty-printed source (`α`, `β + π`, `α + π/4`,
`2 • β`).

`Meta.evalExpr` is what formats that closed phase, and it is the only `unsafe`
step in the module: `phaseTextOfExpr` is an `opaque` with an
`@[implemented_by]` impl, so the walk around it stays ordinary `MetaM` code.
Keep the seal there rather than at the top of the walk.

Spider *arities* get no such treatment — the layout has to place the legs, so
a non-literal `n`/`m` is an error rather than a label.

This is why the display of the `π` notations in `AlgPhase/Notation.lean`
matters: a symbolic phase is whatever the pretty-printer produces. The four
forms are `syntax` + `macro_rules` rather than `notation` precisely so that
display is not left to `notation`'s per-form generated unexpanders, whose
priority is the order the declarations appear in the file. One hand-written
`unexpandOfRat` matches the specific shapes before the `kπ` catch-all, so
`π` does not print as `1π` and `π/4` does not print as `1 / 4π`.

### The layout walk

The walker threads a private `Frag` through the constructors: a list of
`PlacedNode`s (a `NodeShape` — spider / hadamard / wire / input / output —
plus `col` and `qubitHalves`), `Wire.Edge`s, the open `left`/`right` port
lists, `width`, `height`, and the `Wire.Box`es recorded so far. Node ids are
list indices into `nodes`, so concatenating two fragments renumbers the second
by exactly the length of the first. Each open port is paired with the
qubit-in-halves at which it enters or leaves the body.

Qubit positions are `2 ×` the actual qubit ("halves") so a spider with
mismatched arity (e.g. `Z 1→2`) can sit on a half-row at the centre of its
span. `Frag.height` stays a count of whole slots; `stack` shifts the lower
fragment by `2 * a.height`. Only `PlacedNode.toWire` divides by two, via
`Wire.qubitOfHalves`, so `qubit` reaches the widget as `0.5`, `1`, `1.5`, ….

Per-constructor layout (all qubit values are halves; `centre = max(n, m) - 1`
is the midpoint of slots `0..max-1` in halves):

- `wire` → one `wire` node at `(col 0, q 0)`, drawn as a small dot. Wires stay
  real nodes so that `stack`/`compose` boxes around them are non-empty and the
  visual extent of a subtree matches its algebraic shape.
  `left = right = [(id, 0)]`, width 1, height 1.
- `hadamard` → one `hadamard` node at `(col 0, q 0)`, same ports, width 1,
  height 1. Its `phase` is sent as `π` explicitly, like every other phase —
  zxcc draws no text for it, but that is zxcc's decision to make.
- `spider c n m phase` → one node at `(col 0, q centre)`. Each port is paired
  with its qubitHalves: when the arity is `1` the lone port sits at `centre`
  (so a single-leg connection is horizontal); when arity > 1 the ports occupy
  whole slots `0, 2, …, 2(k-1)`. Width 1, height `max n m`.
- `stack a b` → concatenate; shift `b`'s qubitHalves by `2 * a.height`.
  Width `max a.width b.width`, height `a.height + b.height`.
- `compose a b` → connect `a.right` to `b.left` (by node id, qubits do not
  need to match) and shift `b`'s cols by `a.width`. Width `a.width + b.width`,
  height `max a.height b.height`.

`stack` and `compose` each emit a `Wire.Box` — a `Wire.BoxKind` and the ids —
over every node
in their subtree; leaves emit none, and so does a subtree with no nodes at all
(`empty ⊗ empty`). zxcc computes pixel bounds from the nodes' live positions,
so boxes follow drags, and sorts them largest-first so outer ones paint
behind inner ones.

Boundary `input`/`output` nodes are added **only** at the top level, by
`ZXSkel.toWire`; fragments stay arity-pure during the walk. The arity comes
from the fragment's own open ports (`left.length`/`right.length`) — the
skeleton has no index to read it off. Each boundary inherits the qubit of the
body port it connects to: input `i` sits at `(col -1, q (left[i].2))` and
output `j` at `(col width, q (right[j].2))`. So an input feeding a `Z 1→2`
spider lands on the spider's centred half-row, and one feeding a wire pushed
down by a sibling `stack` lands at that wire's shifted qubit — no diagonal
jumps from the boundary into the body.

## Where the drawing actually happens

Layout and SVG rendering are **not in this repo** — they live in the
[zxcc](https://github.com/adnathanail/zxcc) web component, consumed as the
`@adnathanail/zxcc` npm package by `zx_view_widget/`. This module's only job
is to emit a `Wire.Diagram`; `SpLean/Widget.lean` mirrors zxcc's `DiagramData`
from its `types.d.ts` and is the only place the field names live. zxcc skips
its BFS auto-layout whenever any node carries `col`, and turns off H-box
barycentre repositioning in that case so supplied positions aren't
overwritten.

Changing how any of that *looks* means changing zxcc and releasing a new
version, not editing anything here.

## Not proved

There is no proof that the lowering to `Wire` draws anything faithful — it is
rendering, and there is nothing to prove it against. There used to be a
`ZX.toZXDiagram` producing a graph-style diagram; it had no callers and was
the last arrow from here into `Axiomatic/`, so it is gone. If a real
`ZX → ZXDiagram` translation is ever wanted it should be written as its own
thing, with a semantics to justify it, not as a by-product of the renderer.
