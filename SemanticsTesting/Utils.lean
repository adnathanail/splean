import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

-- Common scalar values
noncomputable abbrev eiTheta (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
noncomputable abbrev rootTwo : ℂ := Real.sqrt 2

/-! ### Mathlib-style vector conversion

`Wires n → ℂ` is isomorphic to `Fin (2^n) → ℂ` since `Wires n` has `2^n` elements.
We provide a noncomputable bijection-based conversion for arbitrary `n`, and
  computable direct-indexing versions for `n=1` and `n=2`.
-/

/-- Convert a Mathlib-style vector `Fin (2^n) → ℂ` to `Wires n → ℂ`.
  Noncomputable because `Fintype.equivFin` is noncomputable. -/
noncomputable def wiresVec {n : ℕ} (v : Fin (2^n) → ℂ) : Wires n → ℂ :=
  λ w => v (Fin.cast (by simp [Wires]) ((Fintype.equivFin (Wires n)) w))

/-- Computable version for `n=1`: `Fin 2 → ℂ` to `Wires 1 → ℂ`. -/
def wiresVec1 (v : Fin 2 → ℂ) : Wires 1 → ℂ := λ g => if g 0 then v 1 else v 0

instance : Coe (Fin 2 → ℂ) (Wires 1 → ℂ) := ⟨wiresVec1⟩

/-- Computable version for `n=2`: `Fin 4 → ℂ` to `Wires 2 → ℂ`.
  `g 0` is LSB, `g 1` is MSB. -/
def wiresVec2 (v : Fin 4 → ℂ) : Wires 2 → ℂ := λ g =>
  if g 0 then
    if g 1 then v 3 else v 1
  else
    if g 1 then v 2 else v 0

instance : Coe (Fin 4 → ℂ) (Wires 2 → ℂ) := ⟨wiresVec2⟩
