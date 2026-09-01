import SemanticsTesting.Utils
import SemanticsTesting.«03ZSpiders»
import SemanticsTesting.«05XSpiders»

open SpLean.Algebraic

abbrev identityMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

abbrev twoWires : ZX 1 1 := .wire ≫ .wire
#zx twoWires
theorem two_wire_sem : twoWires.sem = identityMatrix := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem]
  rw [show ZX.wire.sem = fun x x_1 => if x 0 = x_1 0 then 1 else 0 from rfl]
  norm_num
  field_simp
  cases f 0 <;> cases g 0 <;> norm_num <;> decide

abbrev twoZGates : ZX 1 1 := (.spider .Z 1 1 π) ≫ (.spider .Z 1 1 π)
#zx twoZGates
theorem two_z_gates_sem : twoZGates.sem = identityMatrix := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  simp only [ZX.sem, sum_wires1, vec1Bits, zSpiderSem, Fin.forall_fin_one]
  cases f 0 <;> cases g 0 <;> simp

abbrev twoXGates : ZX 1 1 := (.spider .X 1 1 π) ≫ (.spider .X 1 1 π)
#zx twoXGates
theorem two_x_gates_sem : twoXGates.sem = identityMatrix := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, sum_wires1]
  rw [x_gate_sem, x_gate_sem, x_gate_sem, x_gate_sem]
  cases f 0 <;> cases g 0 <;> norm_num

-- ## Hadamard decomp (pqs 3.81)
lemma z_rotation_matrix_values (f g : Wires 1) :
    (ZX.spider .Z 1 1 (π/2)).sem f g =
      if (f 0 = false) ∧ (g 0 = false) then 1
      else if (f 0 = true) ∧ (g 0 = true) then Complex.I
      else 0
    := by
  -- Use Z phase gate semantics proof
  rw [z_sem_z_rotation, wiresMat2, AlgPhase.expI_def]
  -- Split into the four corners of the matrix and simplify
  cases f 0 <;> cases g 0 <;> norm_num
  rw [mul_comm (1 / 2), mul_one_div, Complex.exp_pi_div_two_mul_I]

lemma x_rotation_one_plus_i_div_two :
  Complex.exp (Real.pi / 4 * Complex.I) / √2 = (1 + Complex.I) / 2 := by
  rw [Complex.exp_mul_I]
  norm_cast
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  field_simp

lemma x_rotation_one_minus_i_div_two :
  -(Complex.exp (Real.pi / 4 * Complex.I) / √2 * Complex.I) = (1 - Complex.I) / 2 := by
  rw [x_rotation_one_plus_i_div_two]
  field_simp
  rw [mul_add, Complex.I_mul_I]
  ring_nf

lemma x_rotation_matrix_values (f g : Wires 1) :
    (ZX.spider .X 1 1 (π/2)).sem f g =
      Complex.exp (Real.pi / 4 * Complex.I) / Real.sqrt 2 * (if f 0 = g 0 then 1 else - Complex.I) := by
  rw [x_sem_x_rotation, wiresMat2, AlgPhase.expI_def]
  cases f 0 <;> cases g 0 <;> simp [x_rotation_one_minus_i_div_two]
  all_goals
  rw [show Complex.exp (2⁻¹ * (Real.pi : ℂ) * Complex.I) = Complex.I by
        rw [show (2 : ℂ)⁻¹ * (Real.pi : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I by ring,
            Complex.exp_pi_div_two_mul_I]]
  all_goals exact x_rotation_one_plus_i_div_two.symm

noncomputable abbrev eIPiOvFourTimesOneOverRootTwo := Complex.exp (Real.pi / 4 * Complex.I) / rootTwo
noncomputable abbrev hadamardUnnorm : Matrix (Fin 2) (Fin 2) ℂ := !![eIPiOvFourTimesOneOverRootTwo, eIPiOvFourTimesOneOverRootTwo; eIPiOvFourTimesOneOverRootTwo, -eIPiOvFourTimesOneOverRootTwo]
abbrev hadamardEulerDecomp : ZX 1 1 := (.spider .Z 1 1 (π/2)) ≫ (.spider .X 1 1 (π/2)) ≫ (.spider .Z 1 1 (π/2))
#zx hadamardEulerDecomp
-- Showing that
-- e^{-iπ/4} --Z(π/2)---X(π/2)---Z(π/2)-- = --◾--
--           --Z(π/2)---X(π/2)---Z(π/2)-- = e^{iπ/4} * (1/√2) !![1, 1; 1, -1]
--                                        = !![e^{iπ/4}/√2, e^{iπ/4}/√2; e^{iπ/4}/√2, -e^{iπ/4}/√2]
theorem hadamard_euler_decomp_sem : hadamardEulerDecomp.sem = hadamardUnnorm := by
  -- Unfold definitions
  unfold hadamardUnnorm eIPiOvFourTimesOneOverRootTwo wiresMat2
  -- Introduce variables for indexes of matrices
  apply funext; intro f
  apply funext; intro g
  -- Unfold definitions
  rw [ZX.sem, Matrix.of_apply]
  -- Expand the sum over `Wires 1` into its two terms
  simp only [sum_wires1]
  -- Use Zπ/2 matrix values lemma
  rw [z_rotation_matrix_values, z_rotation_matrix_values]
  -- Unfold ZX compositions into sums over wire indices
  rw [ZX.sem, ZX.sem]
  -- Expand the two new sums and use the lemmas
  simp only [sum_wires1, x_rotation_matrix_values, z_rotation_matrix_values]
  -- Split on the four corners of the matrix
  cases f 0 <;> cases g 0 <;>
  -- Throw some Lean magic maths simplifiers at it
  norm_num <;> field_simp <;> simp only [Complex.I_sq, neg_neg]
