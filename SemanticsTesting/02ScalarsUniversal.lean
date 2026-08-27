import SemanticsTesting.Utils
import SemanticsTesting.«02Scalars»

open SpLean.Algebraic

-- Every phase e^{iθ} is realised by a scalar diagram: √2 e^{iθ} · 1/√2
lemma scalar_univ_euler_form (θ : Phase) :
    ∃ d : ZX 0 0, ∀ f g : Wires 0, d.sem f g = Complex.exp (θ.angle * Complex.I) := by
  use redPiCircleAnyGreen θ ≫ redCircleTripleLinkGreenCircle
  intro f g
  -- Composition of scalars is a sum over the unique element of `Wires 0`
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton,
    scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
  unfold rootTwo eiTheta
  field_simp
