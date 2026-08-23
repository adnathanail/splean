import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

noncomputable abbrev eiTheta (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
noncomputable abbrev rootTwo : ℂ := Real.sqrt 2

-- Empty diagram = 1
abbrev emptyDiagram : ZX 0 0 := .empty
#zx emptyDiagram
theorem empty_sem (f g : Wires 0) : emptyDiagram.sem f g = 1 := by
  rw [ZX.sem]

/--
  Scalars (pqs 3.1.4)
--/

-- Zero-arity phaseless Z spider = 2
abbrev greenCircle : ZX 0 0 := .spider .Z 0 0 ⟨0, 1⟩
#zx greenCircle
theorem scalar_sem_two (f g : Wires 0) : greenCircle.sem f g = 2 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num

-- Zero-arity π-phase Z-spider = 0
abbrev greenPiCircle : ZX 0 0 := .spider .Z 0 0 ⟨1, 1⟩
#zx greenPiCircle
theorem scalar_sem_pi (f g : Wires 0) : greenPiCircle.sem f g = 0 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num

-- Zero-arity α-phase Z-spider = 1 + e^{iα}
abbrev greenAlphaCircle (α : Phase) : ZX 0 0 := .spider .Z 0 0 α
#zx greenAlphaCircle ⟨1, 4⟩  -- TODO display parametric phases
theorem scalar_sem_alpha (α : Phase) (f g : Wires 0) :
    (greenAlphaCircle α).sem f g = 1 + eiTheta α.angle := by
  rw [ZX.sem, zSpiderSem]
  norm_num

-- -- Phaseless X spider linked to α-phase Z spider = √2
-- abbrev redCircleAnyGreen (α : Phase) : ZX 0 0 := (.spider .X 0 1 ⟨0, 1⟩) × (.spider .Z 1 0 α)
-- #zx redCircleAnyGreen ⟨1, 4⟩  -- TODO display parametric phases
-- theorem scalar_sem_sqrt_two (α : Phase) (f g : Wires 0) :
--     (redCircleAnyGreen α).sem f g = rootTwo := by
--   rw [ZX.sem]

-- -- π-phase X spider linked to α-phase Z spider = √2 e^{iα}
-- abbrev redPiCircleAnyGreen (α : Phase) : ZX 0 0 := (.spider .X 0 1 ⟨1, 1⟩) × (.spider .Z 1 0 α)
-- #zx redPiCircleAnyGreen ⟨1, 4⟩  -- TODO display parametric phases
-- theorem scalar_sem_sqrt_two_e_i_alpha (α : Phase) (f g : Wires 0) :
--     (redPiCircleAnyGreen α).sem f g = rootTwo * eiTheta α.angle := by
--   rw [ZX.sem]

-- -- Phaseles X spider triple-linked to phaseless Z spider = 1/√2
-- abbrev redCircleTripleLinkGreenCircle : ZX 0 0 := (.spider .X 0 3 ⟨0, 1⟩) × (.spider .Z 3 0 ⟨0, 1⟩)
-- #zx redCircleTripleLinkGreenCircle
-- theorem scalar_sem_one_over_sqrt_two (f g : Wires 0) :
--     redCircleTripleLinkGreenCircle.sem f g = 1 / rootTwo := by
--   rw [ZX.sem]

/--
  Z-spiders
-/

-- √2|+⟩ = |0⟩ + |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ and |1⟩ both have amplitude 1
abbrev plusState : ZX 0 1 := .spider .Z 0 1 ⟨0, 1⟩
#zx plusState
theorem z_sem_plus_state_zero_ampl (f : Wires 0) :
  plusState.sem f (fun _ => false) = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num
theorem z_sem_plus_state_one_ampl (f : Wires 0) :
  plusState.sem f (fun _ => true) = 1 := by
  rw [ZX.sem, zSpiderSem, Phase.angle]
  norm_num
