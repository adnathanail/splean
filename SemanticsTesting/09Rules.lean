import SemanticsTesting.Utils

open SpLean.Algebraic

theorem two_t_gates_equiv_s_gate :
    Gate.T ≫ Gate.T ≈zx Gate.S := by
  zx_rw [zSpider_fusion]

theorem three_t_gates_fusion :
    Gate.T ≫ Gate.T ≫ Gate.T ≈zx ZX.spider .Z 1 1 (3π/4) := by
  zx_rw [zSpider_fusion, zSpider_fusion]

theorem two_x_gates_fusion :
    Gate.X ≫ Gate.X ≈zx ZX.spider .X 1 1 (2π) := by
  zx_rw [xSpider_fusion]
