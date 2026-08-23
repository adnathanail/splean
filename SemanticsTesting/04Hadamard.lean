import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  # Hadamard boxes (pqs 3.1.6)
-/

abbrev hadamard : ZX 1 1 := .hadamard
#zx hadamard
theorem hadamard_sem :
    hadamard.sem = (!![rootTwo⁻¹, rootTwo⁻¹; rootTwo⁻¹, -rootTwo⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, hadSem, wiresMat2, rootTwo]
  cases f 0 <;> cases g 0 <;> norm_num
