import SemanticsTesting.Utils
import SemanticsTesting.«02Scalars»

open SpLean.Algebraic

-- pqs ex 3.5
-- By combining the diagrams from 02Scalars,
--   find a ZX-diagram to represent the following scalar values z:

-- a) z = -1
abbrev scalarDiagNegOne := redPiCircleAnyGreen 1 ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagNegOne
lemma scalar_univ_neg_one (f g : Wires 0) :
  scalarDiagNegOne.sem f g = -1 := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton]
  rw [scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two, AlgPhase.angle, AlgPhase.toRat]
  unfold rootTwo eiTheta
  norm_num


-- b) z = e^{i θ} for any θ
abbrev scalarDiagEuler (θ : AlgPhase) := redPiCircleAnyGreen θ ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagEuler (1 / 4)
lemma scalar_univ_euler_form (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagEuler θ).sem f g = eiTheta θ.angle := by
  -- Composition of scalars is a sum over the unique element of `Wires 0`
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton,
    scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
  unfold rootTwo eiTheta
  field_simp

-- c) z = 1/2
abbrev scalarDiagHalf := redCircleTripleLinkGreenCircle ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagHalf
lemma scalar_univ_half (f g : Wires 0) :
  scalarDiagHalf.sem f g = 1/2 := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton]
  rw [scalar_sem_one_over_sqrt_two, scalar_sem_one_over_sqrt_two]
  unfold rootTwo
  norm_cast
  ring_nf
  norm_num

-- d) z = cos θ for any value of θ
abbrev scalarDiagCosTheta (θ : AlgPhase) :=
  redPiCircleAnyGreen θ ≫
  redCircleTripleLinkGreenCircle ≫
  greenAlphaCircle (-2 * θ) ≫
  redCircleTripleLinkGreenCircle ≫
  redCircleTripleLinkGreenCircle
#zx scalarDiagCosTheta (1 / 4)
lemma scalar_uni_cos_theta (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagCosTheta θ).sem f g = Complex.cos θ.angle := by
  -- Replace diagram semantics with scalars from previous lemmas
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_alpha]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two, scalar_sem_sqrt_two_e_i_alpha]
  unfold rootTwo eiTheta
  -- Rewrite cos in terms of exp
  rw [Complex.cos]
  -- Shuffle expressions around
  nth_rw 4 [mul_right_comm]
  rw [mul_one_div_cancel]
  on_goal 2 => norm_num
  rw [one_mul, mul_add]
  -- e^x * e^y = e^{x + y}
  rw [← Complex.exp_add]
  -- Turn every `angle` into `π` times a rational, so `ring_nf` can normalise the
  -- exponents (`θ + -2θ = -θ`) instead of needing a hand-rolled lemma
  push_cast
  -- Normalise expressions
  ring_nf
  -- Deal with complex casting nastiness
  rw [show ((√2 : ℂ)⁻¹ ^ 2) = 1 / 2 by norm_cast ; simp]

-- TODO complete proof
--   our phases are rationals, so they cannot be used to construct ℝ and therefore ℂ
