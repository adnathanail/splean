import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev bellState : ZX 0 2 := .spider .Z 0 2 ⟨0, 1⟩
#zx bellState

-- Initial theorem with simp in the middle
theorem z_sem_bell_state_1 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem, Phase.angle]
  simp [Fin.forall_fin_succ]
  cases g 0 <;> cases g 1 <;> norm_num

-- Use simp?
theorem z_sem_bell_state_2 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem, Phase.angle]
  simp? [Fin.forall_fin_succ]
  cases g 0 <;> cases g 1 <;> norm_num

-- Use the suggested simp only
theorem z_sem_bell_state_3 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem, Phase.angle]
  simp only [IsEmpty.forall_iff, Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one, and_true,
    true_and, Int.cast_zero, PNat.val_ofNat, Nat.cast_one, div_one, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_ite, mul_one, mul_zero, Matrix.cons_val, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  cases g 0 <;> cases g 1 <;> norm_num

-- Remove lemmas until you have the minimal set
theorem z_sem_bell_state_4 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem, Phase.angle]
  simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Matrix.cons_val]
  cases g 0 <;> cases g 1 <;> norm_num
