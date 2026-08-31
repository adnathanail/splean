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
  rw [scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
  norm_num


-- b) z = e^{i θ} for any θ
abbrev scalarDiagEuler (θ : AlgPhase) := redPiCircleAnyGreen θ ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagEuler
lemma scalar_univ_euler_form (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagEuler θ).sem f g = θ.expI := by
  -- Composition of scalars is a sum over the unique element of `Wires 0`
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton,
    scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
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
  greenAlphaCircle (-2 • θ) ≫
  redCircleTripleLinkGreenCircle ≫
  redCircleTripleLinkGreenCircle
#zx scalarDiagCosTheta
lemma scalar_uni_cos_theta (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagCosTheta θ).sem f g = Complex.cos θ.angle := by
  -- Replace diagram semantics with scalars from previous lemmas
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_sqrt_two_e_i_alpha]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_alpha]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two,
    scalar_sem_one_over_sqrt_two]
  unfold rootTwo
  -- Rewrite cos in terms of exp, and put both sides in terms of `expI`.
  -- `expI_eq_exp_angle` is the bridge back.
  rw [Complex.cos, ← AlgPhase.expI_eq_exp_angle, neg_mul, Complex.exp_neg,
    ← AlgPhase.expI_eq_exp_angle, AlgPhase.expI_zsmul]
  -- `θ + -2θ = -θ` is now `z * z⁻² = z⁻¹`, plain field arithmetic
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp
  rw [hsq]
  ring

-- TODO complete proof
--   our phases are rationals, so they cannot be used to construct ℝ and therefore ℂ
