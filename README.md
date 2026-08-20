# LeanSpider

[![CI](https://github.com/adnathanail/LeanSpider/actions/workflows/ci.yml/badge.svg)](https://github.com/adnathanail/LeanSpider/actions/workflows/ci.yml)
[![prek](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/j178/prek/master/docs/assets/badge-v0.json)](https://github.com/j178/prek)
[![TypeScript](https://img.shields.io/badge/TypeScript-3178C6?logo=typescript&logoColor=fff)](https://www.typescriptlang.org)

## Usage

Install the [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

Create a diagram and view it in the InfoView:
```lean
import LeanSpider.All

open LeanSpider

def zCnotZ : ZXDiagram :=
  .ofList [
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]

#zx zCnotZ
```

### In proofs

To view the current state of a proof as a diagram:
```lean
import LeanSpider.All

open LeanSpider

show_panel_widgets [local ZXPanel]
```

### Other InfoWindow options

To enable the `Selection Panel` (allows you to shift click sub-expressions in the InfoWindow, to view them separately)
```lean
import ProofWidgets.Component.Panel.SelectionPanel
show_panel_widgets [local ZXPanel, local ProofWidgets.SelectionPanel]
```

To enable the `Goal Panel` (displays the main goal of a proof in a separate section in the InfoWindow)
```lean
import ProofWidgets.Component.Panel.GoalTypePanel
show_panel_widgets [local ZXPanel, local ProofWidgets.GoalTypePanel]
```

## Development

### Prek

[Install prek](https://github.com/j178/prek) and run
```
prek --install
```

### ZX viewing widget

The InfoView widget lives in `zx_view_widget/src/`.

It is a React component wrapping the [zxcc](https://github.com/adnathanail/zxcc) web component.

`lake` handles `npm install` and the JS bundle automatically:

```sh
lake build
```
