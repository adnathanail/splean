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
    -- `2π` is `ofRat 2`, so `expI_ofRat_ofNat` reduces it to `(-1) ^ 2`
    simp [ZX.sem, zSpiderSem]
