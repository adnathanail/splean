import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  # Z-basis states (pqs eq 3.6)
-/

-- ## 0 state
-- (X0)- = √2|0⟩
abbrev zeroState : ZX 0 1 := .spider .X 0 1 ⟨0, 1⟩
#zx zeroState
lemma x_sem_zero_state_zero_ampl (f : Wires 0) : zeroState.sem f zeroAmpl = rootTwo := by
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique, rootTwo]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp [zSpiderSem, hadSem, Phase.angle]
  norm_cast
  rw [two_times_one_over_root_two_eq_root_two]
lemma x_sem_zero_state_one_ampl (f : Wires 0) : zeroState.sem f oneAmpl = 0 := by
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp [zSpiderSem, hadSem, Phase.angle]
theorem x_sem_zero_state (f : Wires 0) : zeroState.sem f = (![rootTwo, 0] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, wires1_eq_const g]
  cases g 0 <;> simp [x_sem_zero_state_zero_ampl f, x_sem_zero_state_one_ampl f]

-- ## 1 state
-- (Xπ)- = √2|1⟩
abbrev oneState : ZX 0 1 := .spider .X 0 1 ⟨1, 1⟩
#zx oneState
lemma x_sem_one_state_zero_ampl (f : Wires 0) : oneState.sem f zeroAmpl = 0 := by
  -- Same as x_sem_zero_state_one_ampl
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp [zSpiderSem, hadSem, Phase.angle]
lemma x_sem_one_state_one_ampl (f : Wires 0) : oneState.sem f oneAmpl = rootTwo := by
  -- Same as x_sem_zero_state_zero_ampl
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique, rootTwo]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp [zSpiderSem, hadSem, Phase.angle]
  norm_cast
  rw [two_times_one_over_root_two_eq_root_two]
theorem x_sem_one_state (f : Wires 0) : oneState.sem f = (![0, rootTwo] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, wires1_eq_const g]
  cases g 0 <;> simp [x_sem_one_state_zero_ampl f, x_sem_one_state_one_ampl f]
