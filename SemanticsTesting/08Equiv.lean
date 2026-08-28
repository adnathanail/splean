import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev plusState : ZX 0 1 := .spider .Z 0 1
theorem plusStateIsEquivalentToItself :
    plusState ≈zx plusState := by
  rw [ZX.Equiv]
  use 1
  norm_num

abbrev plusStateTwoPi : ZX 0 1 := .spider .Z 0 1 2
#zx plusStateTwoPi
theorem plusStateEquivModPi :
    plusState ≈zx plusStateTwoPi := by
    rw [ZX.Equiv]
    use 1
    norm_num
    intro g
    simp only [ZX.sem, zSpiderSem]
    push_cast
    simp
