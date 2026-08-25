import SemanticsTesting.Utils

open SpLean.Algebraic

-- Empty diagram = 1
abbrev emptyDiagram : ZX 0 0 := .empty
#zx emptyDiagram
theorem empty_sem (f g : Wires 0) : emptyDiagram.sem f g = 1 := by
  rw [ZX.sem]

-- Wire = identity
abbrev wireDiagram : ZX 1 1 := .wire
#zx wireDiagram
theorem wire_sem :
    wireDiagram.sem = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2 vec1Bits
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem]
  cases f 0 <;> cases g 0 <;> norm_num
