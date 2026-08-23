import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

/--
  X-basis states (pqs eq 3.3)
-/

-- Boundary assignments of a single wire
abbrev zeroAmpl : Wires 1 := fun _ => false
abbrev oneAmpl : Wires 1 := fun _ => true

-- TODO track scalar factors
-- (Z0)- = √2|+⟩ = |0⟩ + |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ and |1⟩ both have amplitude 1
abbrev plusState : ZX 0 1 := .spider .Z 0 1 ⟨0, 1⟩
#zx plusState
theorem z_sem_plus_state_zero_ampl (f : Wires 0) :
    plusState.sem f zeroAmpl = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num
theorem z_sem_plus_state_one_ampl (f : Wires 0) :
    plusState.sem f oneAmpl = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num
-- We can prove both with one theorem by splitting on the output wire indicator
theorem z_sem_plus_state (f : Wires 0) (g : Wires 1) :
    plusState.sem f g = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  simp only [Fin.forall_fin_one]
  -- cases hg : g 0 <;> simp <;> rw [hg] <;> simp
  -- cases hg : g 0 <;> simp [Fin.forall_fin_one, hg]
  split_ifs with h1 h2 <;> simp_all

-- (Zπ)- = √2|-⟩ = |0⟩ - |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ has amplitude 1, |1⟩ has amplitude -1
abbrev minusState : ZX 0 1 := .spider .Z 0 1 ⟨1, 1⟩
#zx minusState
theorem z_sem_minus_state_zero_ampl (f : Wires 0) :
    minusState.sem f zeroAmpl = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num
theorem z_sem_minus_state_one_ampla (f : Wires 0) :
    minusState.sem f oneAmpl = -1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num [Complex.exp_pi_mul_I]
