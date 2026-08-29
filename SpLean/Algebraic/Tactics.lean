import SpLean.Algebraic.Equiv
import Mathlib.Tactic.GRewrite

/-!
# Rewriting with `≈zx`

`≈zx` is a `def`, not an `Eq`, so `rw` can't use rules like `zSpider_fusion`
Mathlib's `grw` generalises `rw` to any relation

`zx_rw` does `grw` then phase-normalisation
-/

namespace SpLean.Algebraic

attribute [gcongr] ZX.Equiv.compose_congr ZX.Equiv.stack_congr

/-- Normalise phase arithmetic left behind by a rewrite.

Spider fusion's output phase is `α + β`, so it would leave `π/4 + π/4`
  where we wanted `π/2`
`← AlgPhase.ofRat_add` pushes `AlgPhase`s together so that `norm_num`
  can simplify
-/
macro "zx_phase" : tactic =>
  `(tactic| (try simp only [← AlgPhase.ofRat_add]
             try norm_num
             try rfl))

open Lean.Parser.Tactic in
/-- `rw`, but for `≈zx` rules.

    zx_rw [zSpider_fusion]           -- fire once
    zx_rw [zSpider_fusion, zSpider_fusion]
    zx_rw [← zSpider_fusion]         -- unfuse

Each resulting goal gets a `zx_phase` pass, kept behind `done` so a goal
it cannot close is handed back unchanged rather than half-rewritten. -/
macro "zx_rw " s:rwRuleSeq : tactic =>
  `(tactic| (grw $s:rwRuleSeq <;> try (zx_phase; done)))

end SpLean.Algebraic
