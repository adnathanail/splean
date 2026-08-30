import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Tactics
import SpLean.Algebraic.Rules.Structural
import SpLean.Algebraic.Rules.HadamardHadamard

namespace SpLean.Algebraic

/-- Colour change (arity 1 1): swap X spider for H Z H -/
theorem colour_change_X_Z_one_wire (α : AlgPhase) :
    ZX.spider .X 1 1 α ≈zx (ZX.hadamard ≫ ZX.spider .Z 1 1 α ≫ ZX.hadamard) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem]
  nth_rw 3 [Finset.univ_unique]
  rw [Finset.prod_singleton']
  simp only [Fin.isValue, Fin.default_eq_zero, Finset.univ_unique, Finset.prod_singleton, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Colour change (arity 1 1): swap Z spider for H X H -/
theorem colour_change_Z_X_one_wire (α : AlgPhase) :
    ZX.spider .Z 1 1 α ≈zx (ZX.hadamard ≫ ZX.spider .X 1 1 α ≫ ZX.hadamard) := by
  zx_rw [colour_change_X_Z_one_wire]
  zx_rw [← compose_assoc _ _ ZX.hadamard]
  zx_rw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard]
  zx_rw [wire_compose]
  zx_rw [compose_assoc]
  zx_rw [hadamard_hadamard]
  zx_rw [compose_wire]

/-- Colour change (arity n m): a Z spider with a Hadamard on every leg is an X spider. -/
theorem colour_change_X_Z (n m : ℕ) (α : AlgPhase) :
    ZX.spider .X n m α ≈zx (ZX.nHadamard n ≫ ZX.spider .Z n m α ≫ ZX.nHadamard m) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem, n_hadamard_sem]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Colour change (arity n m): an X spider with a Hadamard on every leg is a Z spider. -/
theorem colour_change_Z_X (n m : ℕ) (α : AlgPhase) :
    ZX.spider .Z n m α ≈zx (ZX.nHadamard n ≫ ZX.spider .X n m α ≫ ZX.nHadamard m) := by
  zx_rw [colour_change_X_Z]
  zx_rw [← compose_assoc _ _ (ZX.nHadamard m)]
  zx_rw [← compose_assoc (ZX.nHadamard _) (ZX.nHadamard _)]
  zx_rw [hadamard_hadamard_n]
  zx_rw [nWire_compose]
  zx_rw [compose_assoc]
  zx_rw [hadamard_hadamard_n]
  zx_rw [compose_nWire]

end SpLean.Algebraic
