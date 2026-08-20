# LeanSpider

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

## Committing

Sometimes this repository is managed with GitButler.
Check whether you are on the `gitbutler/workspace` branch; if so, use the `but` CLI to interact with it.
Make changes in new commits, as opposed to modifying existing commits, unless explicitly told to.

**Do not add attributions to yourself in commit messages**

## Project structure

- `LeanSpider/` — Lean 4 library: ZX diagram types, spider fusion, JSON serialization
- `zx_view_widget/` — TypeScript ProofWidgets widget (React, rollup). A thin shell that hands the Lean diagram JSON to the `<zx-diagram>` web component from [`@adnathanail/zxcc`](https://www.npmjs.com/package/@adnathanail/zxcc), which does the layout and SVG rendering.
- `Main.lean` — Entry point with example diagrams shown in InfoView

## Build commands

```sh
lake build
```

The JS bundle is built by rollup and written to `.lake/build/js/`. zxcc is bundled at build time; there are no runtime network requests.

## Key conventions

- `ZXDiagram` uses `List (Option Node)` for nodes (list indices are node IDs) and `List Edge` for edges.
- Construct diagrams with `ZXDiagram.ofList` (list indices become IDs) or `ZXDiagram.addNode`/`ZXDiagram.addEdge`
- Look up nodes with `d.getNode? id`, not direct list indexing
- ZXDiagram nodes: `.input ioId`, `.output ioId`, `.spider color phase`, `.hadamard` where phase is a `Phase` (num/den)
- Phases cross the wire as display-ready strings (`π/2`, `-π/4`, `0`) — `Phase.format` in `LeanSpider/Visualize.lean` is the single source of truth; the widget prints them verbatim
- JSON wire format from Lean to the widget: `{"nodes": [...], "edges": [{"src": id, "tgt": id}]}`
- Layout and rendering both live in the separate [zxcc](https://github.com/adnathanail/zxcc) repo, not here — change them there and release a new version.

## Widget architecture

`zx_view_widget/src/zxDiagram.tsx` handles only the InfoView shell: the goal/diagram side-by-side layout and its persisted toggle. For each panel it renders a `<zx-diagram>` element and assigns the Lean JSON to its `.diagram` property; zxcc lays the graph out and draws the interactive SVG. Nodes are draggable, H-boxes auto-position at the barycenter of their neighbours, and parallel edges are drawn as bezier arcs.

## Lean tips

- `ZXDiagram` has a manual `BEq` instance that sorts edges before comparison, so edge order doesn't affect equality
