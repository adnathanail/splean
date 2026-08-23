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

/-! ### Mathlib-style vector conversion

`Wires n → ℂ` is isomorphic to `Fin (2^n) → ℂ` since `Wires n` has `2^n` elements.
We provide a noncomputable bijection-based conversion for arbitrary `n`, and a
computable direct-indexing version for the common `n=1` case.
-/

/-- Convert a Mathlib-style vector `Fin (2^n) → ℂ` to `Wires n → ℂ`.
Noncomputable because `Fintype.equivFin` is noncomputable. -/
noncomputable def wiresVec {n : ℕ} (v : Fin (2^n) → ℂ) : Wires n → ℂ :=
  λ w => v (Fin.cast (by simp [Wires]) ((Fintype.equivFin (Wires n)) w))

/-- Computable version for `n=1`: `Fin 2 → ℂ` to `Wires 1 → ℂ`. -/
def wiresVec1 (v : Fin 2 → ℂ) : Wires 1 → ℂ := λ g => if g 0 then v 1 else v 0

instance : Coe (Fin 2 → ℂ) (Wires 1 → ℂ) := ⟨wiresVec1⟩
