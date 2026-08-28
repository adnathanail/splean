import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev bellState : ZX 0 2 := .spider .Z 0 2
#zx bellState

-- Initial theorem with simp in the middle
theorem z_sem_bell_state_1 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem]
  simp [Fin.forall_fin_succ]
  cases g 0 <;> cases g 1 <;> norm_num

-- Use simp?
theorem z_sem_bell_state_2 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem]
  simp? [Fin.forall_fin_succ]
  cases g 0 <;> cases g 1 <;> norm_num

-- Use the suggested simp only
theorem z_sem_bell_state_3 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem]
  simp only [IsEmpty.forall_iff, Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one, and_true, true_and,
    AlgPhase.angle_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_ite, mul_one, mul_zero, vec2Bits,
    vec1Bits, Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one]
  cases g 0 <;> cases g 1 <;> norm_num

-- Remove lemmas until you have the minimal set
theorem z_sem_bell_state_4 (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem]
  simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Matrix.cons_val]
  cases g 0 <;> cases g 1 <;> norm_num
