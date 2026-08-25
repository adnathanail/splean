import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev twoWires : ZX 1 1 := .wire × .wire
#zx twoWires
theorem two_wire_sem :
    twoWires.sem = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, wiresMat2]
  rw [show ZX.wire.sem = fun x x_1 => if x 0 = x_1 0 then 1 else 0 from rfl]
  norm_num
  field_simp
  cases f 0 <;> cases g 0 <;> norm_num <;> decide
