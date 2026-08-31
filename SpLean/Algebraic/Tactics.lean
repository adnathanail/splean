import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Cast
import Mathlib.Tactic.GRewrite

/-!
# Rewriting with `≈zx`

`≈zx` is a `def`, not an `Eq`, so `rw` can't use rules like `spider_fusion_Z_one_wire`
Mathlib's `grw` generalises `rw` to any relation

`zx_rw` does `grw` then phase-normalisation
-/

namespace SpLean.Algebraic

attribute [gcongr] ZX.Equiv.compose_congr ZX.Equiv.stack_congr ZX.Equiv.cast_congr

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

/-- Reduce a phase to its normal form in `[0, 2)`.

`spider_normalize`'s output phase is an `AlgPhase.normalize` that has not been
computed yet, and `zx_phase` deliberately leaves it alone: unfolding `normalize`
means unfolding `red`, and on a *symbolic* phase that shreds the `AlgPhase`
arithmetic into raw `toRat` with a stuck `Int.floor` in it, which is worse than
where it started. So normalisation is opt-in — `zx_rw [spider_normalize]` hands
the goal back and you follow it with `zx_normalize`.

`norm_num` rather than `decide` because `Int.floor` on `ℚ` does not reduce in
the kernel. -/
macro "zx_normalize" : tactic =>
  `(tactic| (try simp only [← AlgPhase.ofRat_add]
             norm_num [AlgPhase.normalize, AlgPhase.red]
             try rfl))

open Lean.Parser.Tactic in
/-- `rw`, but for `≈zx` rules.

    zx_rw [spider_fusion_Z_one_wire]           -- fires everywhere once in parallel
    zx_rw [spider_fusion_Z_one_wire, spider_fusion_Z_one_wire]
    zx_rw [← spider_fusion_Z_one_wire]         -- unfuse

Each resulting goal gets a `zx_phase` pass, kept behind `done` so a goal
it cannot close is handed back unchanged rather than half-rewritten. -/
macro "zx_rw " s:rwRuleSeq : tactic =>
  `(tactic| (grw $s:rwRuleSeq <;> try (zx_phase; done)))

open Lean.Parser.Tactic in
/-- `nth_rw`, but for `≈zx` rules — rewrite only at the given occurrences.

    nth_zx_rw 2 [colour_change_Z_X_one_wire]     -- only the second Z spider
    nth_zx_rw 1 3 [colour_change_Z_X_one_wire]   -- the first and the third

`zx_rw` fires a rule everywhere it matches, which for a rule like colour change
(whose RHS contains the LHS's shape again on the other colour) is rarely what
you want in a diagram with several spiders. Occurrences are counted the way
`nth_rw` counts them, left to right through the goal.

Like `zx_rw`, each resulting goal gets a `zx_phase` pass behind `done`. -/
macro "nth_zx_rw " nums:(ppSpace num)+ s:rwRuleSeq : tactic =>
  `(tactic| (grw (occs := .pos [$[$nums],*]) $s:rwRuleSeq <;> try (zx_phase; done)))

end SpLean.Algebraic
