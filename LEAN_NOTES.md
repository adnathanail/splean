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