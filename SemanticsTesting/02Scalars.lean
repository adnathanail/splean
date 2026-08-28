import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  Scalars (pqs 3.1.4)
--/

-- Zero-arity phaseless Z spider = 2
abbrev greenCircle : ZX 0 0 := .spider .Z 0 0
#zx greenCircle
theorem scalar_sem_two (f g : Wires 0) : greenCircle.sem f g = 2 := by
  rw [ZX.sem, zSpiderSem]
  norm_num

-- Zero-arity π-phase Z-spider = 0
abbrev greenPiCircle : ZX 0 0 := .spider .Z 0 0 π
#zx greenPiCircle
theorem scalar_sem_pi (f g : Wires 0) : greenPiCircle.sem f g = 0 := by
  rw [ZX.sem, zSpiderSem]
  push_cast
  norm_num

-- Zero-arity α-phase Z-spider = 1 + e^{iα}
abbrev greenAlphaCircle (α : AlgPhase) : ZX 0 0 := .spider .Z 0 0 α
#zx greenAlphaCircle
theorem scalar_sem_alpha (α : AlgPhase) (f g : Wires 0) :
    (greenAlphaCircle α).sem f g = 1 + eiTheta α.angle := by
  rw [ZX.sem, zSpiderSem]
  norm_num

-- Phaseless X spider linked to α-phase Z spider = √2
abbrev redCircleAnyGreen (α : AlgPhase) : ZX 0 0 := (.spider .X 0 1) ≫ (.spider .Z 1 0 α)
#zx redCircleAnyGreen
theorem scalar_sem_sqrt_two (α : AlgPhase) (f g : Wires 0) :
    (redCircleAnyGreen α).sem f g = rootTwo := by
  rw [ZX.sem]
  simp only [sum_wires1, ZX.sem, xSpiderSem, zSpiderSem, hadSem]
  norm_num
  rw [inv_root_two_add_inv_root_two_eq_root_two_complex]

-- π-phase X spider linked to α-phase Z spider = √2 e^{iα}
abbrev redPiCircleAnyGreen (α : AlgPhase) : ZX 0 0 := (.spider .X 0 1 π) ≫ (.spider .Z 1 0 α)
#zx redPiCircleAnyGreen
theorem scalar_sem_sqrt_two_e_i_alpha (α : AlgPhase) (f g : Wires 0) :
    (redPiCircleAnyGreen α).sem f g = rootTwo * eiTheta α.angle := by
  unfold rootTwo eiTheta
  rw [ZX.sem]
  simp only [sum_wires1, ZX.sem, xSpiderSem, zSpiderSem, hadSem]
  push_cast
  norm_num
  rw [inv_root_two_add_inv_root_two_eq_root_two_complex]

-- Phaseles X spider triple-linked to phaseless Z spider = 1/√2
abbrev redCircleTripleLinkGreenCircle : ZX 0 0 := (.spider .X 0 3) ≫ (.spider .Z 3 0)
#zx redCircleTripleLinkGreenCircle
theorem scalar_sem_one_over_sqrt_two (f g : Wires 0) :
    redCircleTripleLinkGreenCircle.sem f g = 1 / rootTwo := by
  -- Simp definitions
  simp only [ZX.sem, xSpiderSem, zSpiderSem, hadSem]
  -- Simplify ifs
  simp only [mul_ite]
  -- Lean magic
  ring_nf
  norm_num
  field_simp
  -- Simplify booleans
  simp only [Bool.false_eq_true, false_and, true_and]
  simp_all only [Bool.false_eq_true]
  -- Simplify ifs
  simp only [↓reduceIte]
  -- Simplify product of constants
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Simplify all false/true wires
  simp only [sum_bool_endpoints]
  -- Lean magic
  norm_cast
  field_simp
  norm_num
