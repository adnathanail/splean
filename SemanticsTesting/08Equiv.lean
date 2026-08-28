import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev plusState : ZX 0 1 := .spider .Z 0 1
theorem plusStateIsEquivalentToItself :
    ZX.Equiv plusState plusState := by
  rw [ZX.Equiv]
  use 1
  norm_num
