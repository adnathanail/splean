import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Rules.Structural

/-!
# The copy rule

X spiders with no inputs and phase `0` or `π` (`|0⟩` or `|1⟩` up to scalar)
are copied by a Z spider: it passes through and comes out once on every output leg.
-/

namespace SpLean.Algebraic

noncomputable abbrev stateCopyScalar (a : Fin 2) (n : ℕ) (α : AlgPhase) := α.expI^(a : ℕ) * (√2)^(-((n : ℤ) - 1))
lemma stateCopyScalar_ne_zero (a : Fin 2) (n : ℕ) (α : AlgPhase) :
    stateCopyScalar a n α ≠ 0 := by
  unfold stateCopyScalar
  simp only [neg_sub, ne_eq, mul_eq_zero, pow_eq_zero_iff', AlgPhase.expI_ne_zero,
    Fin.val_eq_zero_iff, Fin.isValue, false_and, false_or]
  rw [← not_ne_iff, not_not]
  apply zpow_ne_zero
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- A phase-free X state is copied by a Z spider of any phase. -/
theorem state_copy_Z_zero (m : ℕ) (β : AlgPhase) :
    (ZX.spider .X 0 1 ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1) := by
  refine ⟨stateCopyScalar 0 m β, stateCopyScalar_ne_zero 0 m β, fun f g => ?_⟩
  simp only [ZX.sem, nStackState_sem, xSpiderSem, zSpiderSem, hadSem, sum_wires1]
  simp
  split
  · rename_i h
    simp [h]
    field_simp
    have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hsq : ((√2 : ℝ) : ℂ) * (√2 : ℝ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have hdiv : ((1 : ℂ) + 1) / (√2 : ℝ) = (√2 : ℝ) := by
      rw [div_eq_iff h2, hsq]; norm_num
    have hexp : ((√2 : ℝ) : ℂ) ^ (-((m : ℤ) - 1)) * ((√2 : ℝ) : ℂ) ^ m = (√2 : ℝ) := by
      rw [← zpow_natCast ((√2 : ℝ) : ℂ) m, ← zpow_add₀ h2,
        show -((m : ℤ) - 1) + (m : ℤ) = 1 by ring, zpow_one]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, mul_one, hdiv, mul_assoc, hexp, hsq]
    norm_num
  · rename_i h
    push_neg at h
    obtain ⟨j, hj⟩ := h
    have hj' : g j = true := by simpa using hj
    rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
    simp [hj']

/-- A π-phase X state is copied by a Z spider of any phase. -/
theorem state_copy_Z_pi (m : ℕ) (β : AlgPhase) :
    (ZX.spider .X 0 1 π ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1 π) := by
  sorry

/-- An X state with phase equivalent to `0` or `π` is copied by a Z spider of any phase. -/
theorem state_copy_Z_mod_pi (m : ℕ) {α : AlgPhase} (β : AlgPhase)
    (h : AlgPhase.equiv α 0 ∨ AlgPhase.equiv α π) :
    (ZX.spider .X 0 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1 α) := by
  sorry

/-- A phase-free Z state is copied by an X spider of any phase. -/
theorem state_copy_X_zero (m : ℕ) (β : AlgPhase) :
    (ZX.spider .Z 0 1 ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1) := by
  sorry

/-- A π-phase Z state is copied by an X spider of any phase. -/
theorem state_copy_X_pi (m : ℕ) (β : AlgPhase) :
    (ZX.spider .Z 0 1 π ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1 π) := by
  sorry

/-- A Z state with phase equivalent to `0` or `π` is copied by an X spider of any phase. -/
theorem state_copy_X_mod_pi (m : ℕ) {α : AlgPhase} (β : AlgPhase)
    (h : AlgPhase.equiv α 0 ∨ AlgPhase.equiv α π) :
    (ZX.spider .Z 0 1 α ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1 α) := by
  sorry

end SpLean.Algebraic
