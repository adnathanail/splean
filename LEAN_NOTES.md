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

`simp`
- Very general; anyone can define theorems to be used in simps
- The simp set should aim to reach a normal form
https://leanprover-community.github.io/extras/simp.html#non-terminal-simps

`field_simp`
- If you have common terms on both sides, this will fully remove them from the goal
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html

`norm_num`
Tactic to 'normalise' (simplify) numerical expressions
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Core.html

### Casting

- `norm_cast` moves casts as far outwards as possible
- `push_cast` moves casts as far inwards as possible
- Useful just before `ring`/`linear_combination`

Mythical (never worked for me yet):
- `exact_mod_cast h` / `apply_mod_cast h`: Allows you to apply a hypothesis `h` even if it differs from your goal by the placement of cast arrows
- `rw_mod_cast [h]`: Rewrites using `h` while ignoring differences in cast locations

### Cases

`cases` takes an inductive value and splits all the options into separate goals.
E.g. below `g 0 ` is a `Wires 1` which has two output values: `true` or `false`, so we then have two concrete expressions to simplify with `norm_num`

```lean
abbrev plusState : ZX 0 1 := .spider .Z 0 1 ⟨0, 1⟩
#zx plusState
theorem z_sem_plus_state (f : Wires 0) : plusState.sem f = (![1, 1] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, ZX.sem, zSpiderSem, Phase.angle]
  norm_num
  cases g 0 <;> norm_num
  -- Could also have done:
  --   cases g 0
  --   all_goals norm_num
  -- Or if we need the expressions to stay the same, we can have cases create a hypothesis for each value.
  -- E.g. we could remove the norm_num the line before, and then pass the hypothesis to the second norm_num:
  --   cases h : g 0 <;> norm_num [h]
```

Tactic combinator (`<;>`):
- Sometimes called 'angle-semi' or 'seq-focus`
- Often read as 'and then on all goals'
- Nice for chaining multiple `cases`

```lean
theorem two_wire_sem :
    twoWires.sem = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, wiresMat2]
  rw [show ZX.wire.sem = fun x x_1 => if x 0 = x_1 0 then 1 else 0 from rfl]
  norm_num
  field_simp
  cases f 0 <;> cases g 0 <;> norm_num <;> decide
```


## Commands

Show type signature
```lean
#check yourDefinitionHere
```

## Tips

### Completing proofs

- `exact?` — searches for a single lemma closing the goal.
- `apply?` for up-to-unification.
- `rw?` — every rewrite that applies at the current goal.
- `simp? / aesop?` — run the automation, then show you which lemmas it used. Excellent for discovery, since it hands you the names of lemmas in the neighbourhood.
- `hint` — runs a batch of standard tactics and reports what worked.
- `exact?` with a partial term and _ holes is underrated.

To see what rewrites a `simp` (or `simp` wrapper like `norm_num`) used:
```lean
-- Must go after imports
set_option trace.Meta.Tactic.simp.rewrite true
```

#### Other searching methods

- [Loogle](https://loogle.lean-lang.org)
  - `Loogle "Finset.sum, tsum"`
  - `|- _ * _ = _ * _`
- [Moogle](https://www.moogle.ai) - natural-language semantic search over Mathlib.
- `#leansearch` and `#loogle` commands

### Theorem highlighting

Sometimes theorems statements are hard to discern in the mess of a file.
Using [this VS Code extension](https://marketplace.visualstudio.com/items?itemName=fabiospampinato.vscode-highlight), you can set custom highglight regexes.
Put this in your `.vscode/settings.json`:

```json
{
  "highlight.enabled": true,
  "highlight.regexes": {
      // Box around Lean theorem/lemma statements
      //   (from the `theorem` keyword up to, but not including, the `:=`).
      "(?<!--[^\\n]*)(?<!/-(?:(?!-/)[\\s\\S])*)\\b(?:theorem|lemma)\\b[\\s\\S]*?(?=:=)": {
          "regexFlags": "g",
          "filterFileRegex": ".*\\.lean",
          "decorations": [
              {
                  // rgba hex, partially transparent to allow selection to show through
                  "backgroundColor": "#fa8ce655",
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
