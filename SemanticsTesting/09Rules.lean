import SemanticsTesting.Utils

open SpLean.Algebraic

-- Draw each goal as LHS/RHS diagrams in the InfoView as the cursor moves.
show_panel_widgets [local SpLean.ZXPanel]

-- two_t_gates_equiv_s_gate
example :
    Gate.T ≫ Gate.T ≈zx Gate.S := by
  zx_rw [spider_fusion_Z_one_wire]

-- three_t_gates_fusion
example :
    Gate.T ≫ Gate.T ≫ Gate.T ≈zx ZX.spider .Z 1 1 (3π/4) := by
  zx_rw [spider_fusion_Z_one_wire, spider_fusion_Z_one_wire]

-- two_x_gates_fusion
example :
    Gate.X ≫ Gate.X ≈zx ZX.spider .X 1 1 (2π) := by
  zx_rw [spider_fusion_X_one_wire]

-- fuse_under_stack
example :
    (ZX.wire ⊗ (ZX.hadamard ≫ (Gate.T ≫ Gate.T))) ≈zx
      (ZX.wire ⊗ (ZX.hadamard ≫ Gate.S)) := by
  zx_rw [spider_fusion_Z_one_wire]

-- fuse_symbolic
example (α β γ : AlgPhase) :
    ((ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) ≫ ZX.spider .Z 1 1 γ) ≈zx
      ZX.spider .Z 1 1 (α + β + γ) := by
  zx_rw [spider_fusion_Z_one_wire, spider_fusion_Z_one_wire]

-- unfuse
example (α β : AlgPhase) :
    ZX.spider .Z 1 1 (α + β) ≈zx (ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) := by
  zx_rw [← spider_fusion_Z_one_wire]

-- colour_change_fusion
example :
    Gate.Z ≫ ZX.hadamard ≫ Gate.X  ≫ ZX.hadamard ≈zx Gate.I := by
  unfold Gate.Z Gate.X Gate.I
  -- Colour change
  zx_rw [colour_change_X_Z_one]
  -- Shuffle compositions around
  zx_rw [compose_assoc ZX.hadamard]
  zx_rw [compose_assoc Gate.Z]
  zx_rw [← compose_assoc ZX.hadamard]
  -- Hadamard hadamard
  zx_rw [hadamard_hadamard, wire_compose]
  -- Shuffle
  zx_rw [← compose_assoc Gate.Z]
  -- Spider fusion
  zx_rw [spider_fusion_Z_one_wire]
  zx_phase
  zx_rw [identity_removal_Z_two_pi]
  zx_rw [wire_compose]
  zx_rw [hadamard_hadamard]
  zx_rw [identity_removal_Z]

-- two_pi_spider_is_phaseless
example :
    ZX.spider .Z 0 1 (2π) ≈zx ZX.spider .Z 0 1 0 := by
  zx_rw [spider_normalize]
  zx_normalize

-- three_pi_spider_is_pi
example :
    ZX.spider .X 1 1 (3π) ≈zx ZX.spider .X 1 1 π := by
  zx_rw [spider_normalize]
  zx_normalize

/-- The rule fires inside a larger diagram, not only at the top. -/
-- two_pi_spider_normalizes_under_compose
example :
    (ZX.spider .Z 0 1 (2π) ≫ ZX.hadamard) ≈zx (ZX.spider .Z 0 1 0 ≫ ZX.hadamard) := by
  zx_rw [spider_normalize]
  zx_normalize

-- pqs p123
-- TODO finish once we have pi copy
-- euler_decomp1
example :
    Gate.S ≫ ZX.hadamard ≫ Gate.S ≈zx Gate.Z ≫ ZX.spider .X 1 1 (π/2) ≫ Gate.Z := by
  zx_rw [euler_decomp_ZXZ]
  zx_rw [← compose_assoc Gate.S]
  zx_rw [← compose_assoc Gate.S]
  zx_rw [compose_assoc _ _ Gate.S]
  zx_rw [spider_fusion_Z_one_wire]

-- big_fusion
example :
    ZX.spider .Z 1 5 (π) ≫ ZX.spider .Z 5 1 (π/2) ≫ (ZX.spider .X 1 3 ≫ ZX.spider .X 3 4  ≫ ZX.spider .X 4 1) ≈zx
      ZX.spider .Z 1 1 (3π/2) ≫ ZX.spider .X 1 1 := by
  zx_rw [spider_fusion_Z]
  zx_rw [spider_fusion_X]
  zx_rw [spider_fusion_X]
