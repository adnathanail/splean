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
