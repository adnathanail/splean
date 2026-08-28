import SemanticsTesting.Utils

open SpLean.Algebraic

-- Draw each goal as LHS/RHS diagrams in the InfoView as the cursor moves.
show_panel_widgets [local SpLean.ZXPanel]

theorem two_t_gates_equiv_s_gate :
    Gate.T ≫ Gate.T ≈zx Gate.S := by
  zx_rw [zSpider_fusion]

theorem three_t_gates_fusion :
    Gate.T ≫ Gate.T ≫ Gate.T ≈zx ZX.spider .Z 1 1 (3π/4) := by
  zx_rw [zSpider_fusion, zSpider_fusion]

theorem two_x_gates_fusion :
    Gate.X ≫ Gate.X ≈zx ZX.spider .X 1 1 (2π) := by
  zx_rw [xSpider_fusion]

theorem fuse_under_stack :
    (ZX.wire ⊗ (ZX.hadamard ≫ (Gate.T ≫ Gate.T))) ≈zx
      (ZX.wire ⊗ (ZX.hadamard ≫ Gate.S)) := by
  zx_rw [zSpider_fusion]

theorem fuse_symbolic (α β γ : AlgPhase) :
    ((ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) ≫ ZX.spider .Z 1 1 γ) ≈zx
      ZX.spider .Z 1 1 (α + β + γ) := by
  zx_rw [zSpider_fusion, zSpider_fusion]

theorem unfuse (α β : AlgPhase) :
    ZX.spider .Z 1 1 (α + β) ≈zx (ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) := by
  zx_rw [← zSpider_fusion]

theorem colour_change_fusion :
    (Gate.Z ≫ ZX.hadamard) ≫ Gate.X ≈zx Gate.I := by
  unfold Gate.X
  zx_rw [← colour_change_one]
