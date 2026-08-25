import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

-- Common scalar values
noncomputable abbrev eiTheta (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
noncomputable abbrev rootTwo : ℂ := Real.sqrt 2

-- Common lemmas
lemma two_times_one_over_root_two_eq_root_two :
    (√2)⁻¹ + (√2)⁻¹ = √2 := by
  field_simp
  norm_num
lemma two_times_one_over_root_two_eq_root_two_complex :
    ((√2 : ℝ) : ℂ)⁻¹ + ((√2 : ℝ) : ℂ)⁻¹ = √2 := by
  norm_cast
  rw [two_times_one_over_root_two_eq_root_two]

lemma one_over_root_two_times_itself_eq_half :
    (√2)⁻¹ * (√2)⁻¹ = 1/2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
lemma one_over_root_two_times_itself_eq_half_complex :
    ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1/2 := by
  norm_cast
  rw [one_over_root_two_times_itself_eq_half]
  norm_num

-- Boundary assignments of a single wire. `abbrev`, not `def`, so `simp` and
-- `norm_num` can still see through to `false`/`true`.
abbrev zeroAmpl : Wires 1 := fun _ => false
abbrev oneAmpl : Wires 1 := fun _ => true

/-- A single-wire boundary assignment is the constant function at its one bit. -/
lemma wires1_eq_const (g : Wires 1) : g = fun _ => g 0 :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]

/-! ### Vector bits helpers -/

/-- `vec1Bits a b x₀`
  Body of a length-1 vector, as a function of the wire's bit:
  - `a` at `0`
  - `b` at `1`.
-/
@[simp] def vec1Bits {T : Type*} (a b : T) : Bool → T
  | false => a
  | true  => b

/-- `vec2Bits a b c d x₀ x₁` -/
@[simp] def vec2Bits {T : Type*} (a b c d : T) : Bool → Bool → T
  | false, x₁ => vec1Bits a c x₁
  | true,  x₁ => vec1Bits b d x₁

@[simp] def vec3Bits {T : Type*} (a b c d e f g h : T) : Bool → Bool → Bool → T
  | false, x₁, x₂ => vec2Bits a c e g x₁ x₂
  | true,  x₁, x₂ => vec2Bits b d f h x₁ x₂

/-! ### Mathlib-style vector conversion

`Wires n → ℂ` is isomorphic to `Fin (2^n) → ℂ` since `Wires n` has `2^n` elements.
We provide a noncomputable bijection-based conversion for arbitrary `n`, and
  computable direct-indexing versions for `n ∈ {1, 2, 3}`.
-/

/-- Convert a Mathlib-style vector `Fin (2^n) → ℂ` to `Wires n → ℂ`.
  Noncomputable because `Fintype.equivFin` is noncomputable. -/
noncomputable def wiresVec {n : ℕ} (v : Fin (2^n) → ℂ) : Wires n → ℂ :=
  λ w => v (Fin.cast (by simp [Wires]) ((Fintype.equivFin (Wires n)) w))

/-- Computable version for `n=1`: `Fin 2 → ℂ` to `Wires 1 → ℂ`. -/
def wiresVec1 (v : Fin 2 → ℂ) : Wires 1 → ℂ := λ g => vec1Bits (v 0) (v 1) (g 0)
/-- Computable version for `n=2`: `Fin 4 → ℂ` to `Wires 2 → ℂ`.
  `g 0` is LSB, `g 1` is MSB. -/
def wiresVec2 (v : Fin 4 → ℂ) : Wires 2 → ℂ := λ g => vec2Bits (v 0) (v 1) (v 2) (v 3) (g 0) (g 1)
/-- Computable version for `n=3`: `Fin 8 → ℂ` to `Wires 3 → ℂ`. -/
def wiresVec3 (v : Fin 8 → ℂ) : Wires 3 → ℂ := λ g => vec3Bits (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (g 0) (g 1) (g 2)

instance : Coe (Fin 2 → ℂ) (Wires 1 → ℂ) := ⟨wiresVec1⟩
instance : Coe (Fin 4 → ℂ) (Wires 2 → ℂ) := ⟨wiresVec2⟩
instance : Coe (Fin 8 → ℂ) (Wires 3 → ℂ) := ⟨wiresVec3⟩

/-! ### Matrix helpers -/

-- #### 2×2
/-- Computable conversion from a Mathlib 2x2 matrix to `Wires 1 → Wires 1 → ℂ`.
`f 0` is the row index, `g 0` the column index (both as `Bool → Fin 2`). -/
def wiresMat2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Wires 1 → Wires 1 → ℂ := λ f g =>
  M (vec1Bits 0 1 (f 0)) (vec1Bits 0 1 (g 0))

instance : Coe (Matrix (Fin 2) (Fin 2) ℂ) (Wires 1 → Wires 1 → ℂ) := ⟨wiresMat2⟩
