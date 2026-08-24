## Definitions and abbreviations
```lean
-- Definitions must be expanded in proofs
def greenCircle : ZX 0 0 := .spider .Z 0 0 ⟨0, 1⟩
theorem something := by
  rw [greenCircle, nextStep]

-- Abbreviations are automatic
abbrev greenCircle : ZX 0 0 := .spider .Z 0 0 ⟨0, 1⟩
theorem something := by
  rw [nextStep]

-- Parametric defs/abbrevs
def greenAlphaCircle (α : Phase) : ZX 0 0 := .spider .Z 0 0 α
abbrev greenAlphaCircle (α : Phase) : ZX 0 0 := .spider .Z 0 0 α
```

## Tactics

`field_simp`
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html
Tactic to clear denominators in algebraic expressions.

`norm_num`
Tactic to 'normalise' (simplify) numerical expressions
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Core.html

## Commands

Show type signature
```lean
#check yourDefinitionHere
```

## Tips

To see what rewrites a `simp` (or `simp` wrapper like `norm_num`) used:
```lean
-- Must go after imports
set_option trace.Meta.Tactic.simp.rewrite true
```

Sometimes theorems statements are hard to discern in the mess of a file.
Using [this VS Code extension](https://marketplace.visualstudio.com/items?itemName=fabiospampinato.vscode-highlight), you can set custom highglight regexes.
Put this in your `.vscode/settings.json`:

```json
{
  "highlight.enabled": true,
  // Highlight extension: box around Lean theorem/lemma statements
  // (from the `theorem` keyword up to, but not including, the `:=`).
  "highlight.regexes": {
      "\\b(?:theorem|lemma)\\b[\\s\\S]*?(?=:=)": {
          "regexFlags": "g",
          "filterFileRegex": ".*\\.lean",
          "decorations": [
              {
                // rgba hex, partially transparent to allow selection to show through
                  "backgroundColor": "#00880055",
                  "borderRadius": "3px"
              }
          ]
      }
  },
  "highlight.decorations": {
      "rangeBehavior": 3
  }
}
```

Note that because this uses a regex not a full parser, if you have a `:=` somewhere in your theorem statement, the highglight will end there :/

## Keywords

Proof things
```lean
def emptyDiagram : ZX 0 0 := .empty
abbrev emptyDiagram : ZX 0 0 := .empty
theorem myTheorem (f g : Wires 0) : greenCircle.sem f g = 2 := by
  rfl
example myTheorem (f g : Wires 0) : greenCircle.sem f g = 2 := by
```

Data type things
```lean
inductive ZX : Nat → Nat → Type
  | empty    : ZX 0 0
  | wire     : ZX 1 1
  | hadamard : ZX 1 1
  | spider   (c : SpiderColor) (n m : Nat) (φ : Phase := ⟨0, 1⟩) : ZX n m
  | stack    {n m p q : Nat} : ZX n m → ZX p q → ZX (n + p) (m + q)
  | compose  {n m k : Nat} : ZX n m → ZX m k → ZX n k
structure ZXWidgetProps where
  diagram : Json      -- JSON representation of ZXDiagram
  goal : Json := .null -- optional goal diagram (null = not shown)
  deriving RpcEncodable
```

open, namespace, section, end

noncomputable, private, protected, partial, unsafe and the doc comment are declaration modifiers (declModifiers)