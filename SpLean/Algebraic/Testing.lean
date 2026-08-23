import SpLean.Algebraic.Semantics
import SpLean.Panel

open SpLean.Algebraic

-- Empty diagram = 1
def emptyDiagram : ZX 0 0 := .empty
#zx emptyDiagram
theorem empty_sem (f g : Wires 0) : emptyDiagram.sem f g = 1 := by
  rw [emptyDiagram, ZX.sem]

/-- Zero-arity phaseless Z spider = 2 -/
def greenCircle : ZX 0 0 := .spider .Z 0 0 ⟨0, 1⟩
#zx greenCircle
theorem scalar_sem_two (f g : Wires 0) : greenCircle.sem f g = 2 := by
  rw [greenCircle, ZX.sem, zSpiderSem, Phase.angle]
  norm_num

/-- Zero-arity π-phase Z-spider = 0 -/
def greenPiCircle : ZX 0 0 := .spider .Z 0 0 ⟨1, 1⟩
#zx greenPiCircle
theorem scalar_sem_pi (f g : Wires 0) : greenPiCircle.sem f g = 0 := by
  rw [greenPiCircle, ZX.sem, zSpiderSem, Phase.angle]
  norm_num

/-- Zero-arity α-phase Z-spider = 1 + e^{iα} -/
def greenAlphaCircle (α : Phase) : ZX 0 0 := .spider .Z 0 0 α
#zx greenAlphaCircle ⟨1, 4⟩  -- TODO display parametric phases
theorem scalar_sem_alpha (α : Phase) (f g : Wires 0) :
    (greenAlphaCircle α).sem f g = 1 + Complex.exp (α.angle * Complex.I) := by
  rw [greenAlphaCircle, ZX.sem, zSpiderSem]
  norm_num
