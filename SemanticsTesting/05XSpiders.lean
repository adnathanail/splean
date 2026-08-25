import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  # Z-basis states (pqs eq 3.6)
-/

-- ## 0 state
-- (X0)- = √2|0⟩
abbrev zeroState : ZX 0 1 := .spider .X 0 1 ⟨0, 1⟩
#zx zeroState
-- First prove link between indicator true/false and vector amplitude
lemma x_sem_zero_state_ampl (f : Wires 0) (b : Bool) :
    zeroState.sem f (fun _ => b) = if b then 0 else rootTwo := by
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [hadSem, zSpiderSem, Phase.angle]
  cases b <;> norm_num [two_times_one_over_root_two_eq_root_two_complex]

-- Then use it in the proof against a vector
theorem x_sem_zero_state (f : Wires 0) : zeroState.sem f = (![rootTwo, 0] : Fin 2 → ℂ) := by
  unfold wiresVec1 vec1Bits
  ext g
  rw [wires1_eq_const g]
  cases g 0 <;> simp only [x_sem_zero_state_ampl f, Matrix.cons_val_zero, Matrix.cons_val_one]

-- ## 1 state
-- (Xπ)- = √2|1⟩
abbrev oneState : ZX 0 1 := .spider .X 0 1 ⟨1, 1⟩
#zx oneState
lemma x_sem_one_state_ampl (f : Wires 0) (b : Bool) :
    oneState.sem f (fun _ => b) = if b then rootTwo else 0 := by
  rw [ZX.sem, xSpiderSem, Fintype.sum_unique, rootTwo]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [hadSem, zSpiderSem, Phase.angle]
  cases b <;> norm_num [two_times_one_over_root_two_eq_root_two_complex]
theorem x_sem_one_state (f : Wires 0) : oneState.sem f = (![0, rootTwo] : Fin 2 → ℂ) := by
  unfold wiresVec1 vec1Bits
  ext g
  rw [wires1_eq_const g]
  cases g 0 <;> simp only [x_sem_one_state_ampl f, Matrix.cons_val_zero, Matrix.cons_val_one]

/--
  # X-spiders (pqs eq 3.5)
-/
abbrev xIdentity : ZX 1 1 := .spider .X 1 1 ⟨0, 1⟩
#zx xIdentity
theorem x_sem_x_identity : xIdentity.sem = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2 vec1Bits
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, xSpiderSem]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  simp only [Finset.sum_pair (show zeroAmpl ≠ oneAmpl from by decide)]
  rw [wires1_eq_const f, wires1_eq_const g]
  cases f 0 <;> cases g 0 <;> simp [zSpiderSem, hadSem, Phase.angle]
    <;> norm_cast  -- Make everything into reals
    <;> ring_nf    -- Normalize form
    <;> norm_num   -- Solve

abbrev xGate : ZX 1 1 := .spider .X 1 1 ⟨1, 1⟩
#zx xGate
theorem x_sem_x_gate : xGate.sem = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- same as x_sem_x_identity
  unfold wiresMat2 vec1Bits
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, xSpiderSem]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  simp only [Finset.sum_pair (show zeroAmpl ≠ oneAmpl from by decide)]
  rw [wires1_eq_const f, wires1_eq_const g]
  cases f 0 <;> cases g 0 <;> simp [zSpiderSem, hadSem, Phase.angle] <;> norm_cast <;> ring_nf <;> norm_num

abbrev xRotation (α : Phase) : ZX 1 1 := .spider .X 1 1 α
#zx xRotation ⟨1, 4⟩
theorem x_sem_x_rotation (α : Phase) :
    (xRotation α).sem = (!![
      (1 + Complex.exp (α.angle * Complex.I)) / 2, (1 - Complex.exp (α.angle * Complex.I)) / 2;
      (1 - Complex.exp (α.angle * Complex.I)) / 2, (1 + Complex.exp (α.angle * Complex.I)) / 2
    ] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2 vec1Bits
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, xSpiderSem]
  rw [wires1_eq_const f, wires1_eq_const g]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  simp only [Finset.sum_pair (show zeroAmpl ≠ oneAmpl from by decide)]
  simp only [zSpiderSem, hadSem, Bool.and_true, Bool.false_eq_true]
  cases f 0 <;> cases g 0 <;>
  norm_num <;>
  -- `mul_right_comm` pulls the two `(√2)⁻¹` factors flanking `e^{iα}` together.
  rw [mul_right_comm, one_over_root_two_times_itself_eq_half_complex] <;> ring
