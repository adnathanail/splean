import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev twoTGates : ZX 1 1 := .spider .Z 1 1 (π/4) ≫ .spider .Z 1 1 (π/4)
#zx twoTGates
abbrev sGate : ZX 1 1 := .spider .Z 1 1 (π/2)
#zx sGate

theorem two_t_gates_equiv_z_gate :
    twoTGates ≈zx sGate := by
  unfold twoTGates sGate
  rw [show ((π/2) = (π/4) + (π/4)) by rw [← AlgPhase.ofRat_add] ; norm_num]
  exact zSpider_fusion 1 1 _ _
