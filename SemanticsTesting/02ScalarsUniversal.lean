import SemanticsTesting.Utils
import SemanticsTesting.«02Scalars»

open SpLean.Algebraic

-- pqs ex 3.5
-- By combining the diagrams from 02Scalars,
--   find a ZX-diagram to represent the following scalar values z:

-- a) z = -1
abbrev scalarDiagNegOne := redPiCircleAnyGreen ⟨1, 1⟩ ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagNegOne
lemma scalar_univ_neg_one (f g : Wires 0) :
  scalarDiagNegOne.sem f g = -1 := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton]
  rw [scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two, Phase.angle]
  unfold rootTwo eiTheta
  norm_num


-- b) z = e^{i θ} for any θ
abbrev scalarDiagEuler (θ : Phase) := redPiCircleAnyGreen θ ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagEuler ⟨1, 4⟩
lemma scalar_univ_euler_form (θ : Phase) (f g : Wires 0) :
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
