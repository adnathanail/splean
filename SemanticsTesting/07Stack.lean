import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev twoQubitidentityMatrix : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
abbrev twoWiresStacked : ZX 2 2 := .wire ⊗ .wire
#zx twoWiresStacked
theorem two_wire_stack_sem : twoWiresStacked.sem = twoQubitidentityMatrix := by
  -- Unfold definitions
  unfold wiresMat4 twoQubitidentityMatrix
  -- Introduce variables for indexes of matrices
  apply funext; intro f
  apply funext; intro g
  -- Split the boundary between the two wires: `f 0`/`g 0` go to the left copy
  --   (via `Fin.castAdd`), `f 1`/`g 1` to the right (via `Fin.natAdd`)
  rw [ZX.sem]
  -- Show the wires are identity
  rw [show ZX.wire.sem = fun x y => if x 0 = y 0 then 1 else 0 from rfl]
  -- Split on the sixteen entries of the 4x4 matrix
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hg0 : g 0 <;> cases hg1 : g 1 <;>
    simp [hf0, hf1, hg0, hg1]
