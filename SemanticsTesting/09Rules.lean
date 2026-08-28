import SemanticsTesting.Utils

open SpLean.Algebraic

theorem two_t_gates_equiv_s_gate :
    Gate.T ≫ Gate.T ≈zx Gate.S := by
  zx_rw [zSpider_fusion]

theorem three_t_gates_fusion :
    Gate.T ≫ Gate.T ≫ Gate.T ≈zx ZX.spider .Z 1 1 (3π/4) := by
  zx_rw [zSpider_fusion, zSpider_fusion]
