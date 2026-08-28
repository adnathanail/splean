import SpLean.Algebraic.AlgPhase.Defs

namespace AlgPhase

noncomputable def angle (p : AlgPhase) : ℝ := (p.toRat : ℝ) * Real.pi

/-- The bridge out of `AlgPhase`: an angle is `π` times a rational.

Tagged `@[push_cast]` (together with the `toRat` lemmas above), so `push_cast`
turns any `AlgPhase` arithmetic buried under `angle` — and under the `ℝ → ℂ`
coercion — into plain rational arithmetic on `π`, at which point `ring` can
finish. That is what makes goals like
`↑θ.angle * I + ↑(-2 • θ).angle * I = -↑θ.angle * I` a one-liner instead of
needing a bespoke lemma per shuffle. -/
theorem angle_eq (p : AlgPhase) : p.angle = (p.toRat : ℝ) * Real.pi := rfl

attribute [push_cast] angle_eq toRat_zero toRat_one toRat_add toRat_neg toRat_sub
  toRat_natCast toRat_intCast toRat_ofNat toRat_nsmul toRat_zsmul

@[simp] theorem angle_add (p q : AlgPhase) : (p + q).angle = p.angle + q.angle := by
  push_cast; ring

@[simp] theorem angle_neg (p : AlgPhase) : (-p).angle = -p.angle := by
  push_cast; ring

@[simp] theorem angle_zero : (0 : AlgPhase).angle = 0 := by
  push_cast; ring

end AlgPhase
