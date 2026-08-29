import SemanticsTesting.Utils
import SpLean.Claude

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
    Gate.Z ≫ ZX.hadamard ≫ Gate.X  ≫ ZX.hadamard ≈zx Gate.I := by
  unfold Gate.Z Gate.X Gate.I
  -- Colour change
  zx_rw [← colour_change_one]
  -- Shuffle compositions around
  zx_rw [compose_assoc ZX.hadamard]
  zx_rw [compose_assoc Gate.Z]
  zx_rw [← compose_assoc ZX.hadamard]
  -- Hadamard hadamard
  zx_rw [hadamard_hadamard, wire_compose]
  -- Shuffle
  zx_rw [← compose_assoc Gate.Z]
  -- Spider fusion
  zx_rw [zSpider_fusion]
  zx_phase
  zx_rw [identity_removal_Z_two_pi]
  zx_rw [wire_compose]
  zx_rw [hadamard_hadamard]
  zx_rw [identity_removal_Z]

theorem two_pi_spider_is_phaseless :
    ZX.spider .Z 0 1 (2π) ≈zx ZX.spider .Z 0 1 0 := by
  zx_rw [spider_normalize]

theorem three_pi_spider_is_pi :
    ZX.spider .X 1 1 (3π) ≈zx ZX.spider .X 1 1 π := by
  zx_rw [spider_normalize]

/-- The rule fires inside a larger diagram, not only at the top. -/
theorem two_pi_spider_normalizes_under_compose :
    (ZX.spider .Z 0 1 (2π) ≫ ZX.hadamard) ≈zx (ZX.spider .Z 0 1 0 ≫ ZX.hadamard) := by
  zx_rw [spider_normalize]
