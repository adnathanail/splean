import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev plusState : ZX 0 1 := .spider .Z 0 1
theorem plus_state_is_equivalent_to_itself :
    plusState ≈zx plusState := by
  rw [ZX.Equiv]
  use 1
  norm_num

abbrev plusStateTwoPi : ZX 0 1 := .spider .Z 0 1 (2π)
#zx plusStateTwoPi
theorem plus_state_equiv_mod_two_pi :
    plusState ≈zx plusStateTwoPi := by
    rw [ZX.Equiv]
    use 1
    norm_num
    intro g
    simp only [ZX.sem, zSpiderSem]
    push_cast
    simp
