import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

-- Empty diagram = 1
abbrev emptyDiagram : ZX 0 0 := .empty
#zx emptyDiagram
theorem empty_sem (f g : Wires 0) : emptyDiagram.sem f g = 1 := by
  rw [ZX.sem]
