import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev identityMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

abbrev twoWires : ZX 1 1 := .wire ≫ .wire
#zx twoWires
theorem two_wire_sem : twoWires.sem = identityMatrix := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, wiresMat2]
  rw [show ZX.wire.sem = fun x x_1 => if x 0 = x_1 0 then 1 else 0 from rfl]
  norm_num
  field_simp
  cases f 0 <;> cases g 0 <;> norm_num <;> decide

abbrev twoZGates : ZX 1 1 := (.spider .Z 1 1 ⟨1, 1⟩) ≫ (.spider .Z 1 1 ⟨1, 1⟩)
#zx twoZGates
theorem two_z_gates_sem : twoZGates.sem = identityMatrix := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, wiresMat2]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp [ZX.sem, zSpiderSem, Phase.angle]
  cases f 0 <;> cases g 0 <;> simp

abbrev twoXGates : ZX 1 1 := (.spider .X 1 1 ⟨1, 1⟩) ≫ (.spider .X 1 1 ⟨1, 1⟩)
#zx twoXGates
/-- The X gate flips the bit: its amplitude is `1` off the diagonal, `0` on it.
Proved separately so the composition below never unfolds `xSpiderSem`'s double
sum twice over. -/
lemma x_gate_ampl (f g : Wires 1) :
    (ZX.spider .X 1 1 (⟨1, 1⟩ : Phase)).sem f g = if f 0 = g 0 then 0 else 1 := by
  rw [ZX.sem, xSpiderSem]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  simp only [Finset.sum_pair (show zeroAmpl ≠ oneAmpl from by decide)]
  simp only [zSpiderSem, hadSem, Phase.angle]
  cases hf : f 0 <;> cases hg : g 0 <;>
    norm_num [hf, hg, one_over_root_two_times_itself_eq_half_complex]

theorem two_x_gates_sem : twoXGates.sem = identityMatrix := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, wiresMat2]
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  rw [Finset.sum_pair (by decide)]
  rw [x_gate_ampl, x_gate_ampl, x_gate_ampl, x_gate_ampl]
  cases hf : f 0 <;> cases hg : g 0 <;> norm_num
