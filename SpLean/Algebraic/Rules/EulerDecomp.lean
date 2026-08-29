import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas

namespace SpLean.Algebraic

theorem inv_root_two_eq_div : ((√2 : ℝ))⁻¹ = √2 / 2 := by
  rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), inv_mul_eq_div,
    div_eq_iff (Real.sqrt_ne_zero'.2 (by norm_num))]
  exact (Real.mul_self_sqrt (by norm_num)).symm

/-- The scalar for Euler decomp
    casted nicely for `hadSem` and `√2` lemmas in `Rules/Lemmas.lean` -/
theorem exp_neg_i_pi_over_four_eq :
    Complex.exp (- (Complex.I * Real.pi / 4))
      = ((√2 : ℝ) : ℂ)⁻¹ - ((√2 : ℝ) : ℂ)⁻¹ * Complex.I := by
  rw [show (- (Complex.I * (Real.pi : ℂ) / 4)) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
    ← inv_root_two_eq_div]
  push_cast
  ring

/-- Euler decomposition: `H = e^{-iπ/4} Z(π/2) ≫ X(π/2) ≫ Z(π/2)` -/
theorem euler_decomp_ZXZ :
    ZX.hadamard
      ≈zx (ZX.spider .Z 1 1 (π/2) ≫ ZX.spider .X 1 1 (π/2) ≫ ZX.spider .Z 1 1 (π/2)) := by
  refine ⟨Complex.exp (- (Complex.I * Real.pi / 4)), Complex.exp_ne_zero _, fun f g => ?_⟩
  simp only [ZX.sem, hadSem, zSpiderSem, xSpiderSem, sum_wires1]
  norm_num
  cases f 0 <;> cases g 0 <;>
    simp <;>
    field_simp
  all_goals
  rw [exp_neg_i_pi_over_four_eq,
      show ((√2 : ℝ) : ℂ)⁻¹ = ((√2 / 2 : ℝ) : ℂ) by
        rw [← Complex.ofReal_inv, inv_root_two_eq_div]]
  apply Complex.ext <;> simp [Complex.I_sq] <;> ring

end SpLean.Algebraic
