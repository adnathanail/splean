import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv

namespace SpLean.Algebraic

theorem colour_change_one (α : AlgPhase) :
    (ZX.hadamard ≫ ZX.spider .Z 1 1 α ≫ ZX.hadamard) ≈zx ZX.spider .X 1 1 α := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem]
  nth_rw 5 [Finset.univ_unique]
  rw [Finset.prod_singleton']
  simp only [Fin.isValue, Fin.default_eq_zero, Finset.univ_unique, Finset.prod_singleton, Finset.sum_mul]
  rw [Finset.sum_comm]
