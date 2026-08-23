import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

-- Common scalar values
noncomputable abbrev eiTheta (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
noncomputable abbrev rootTwo : ℂ := Real.sqrt 2

-- Boundary assignments of a single wire. `abbrev`, not `def`, so `simp` and
-- `norm_num` can still see through to `false`/`true`.
abbrev zeroAmpl : Wires 1 := fun _ => false
abbrev oneAmpl : Wires 1 := fun _ => true
