import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas

namespace SpLean.Algebraic

theorem hadamard_hadamard :
    ZX.hadamard ≫ ZX.hadamard ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, hadSem, sum_wires1]
  cases f 0 <;> cases g 0 <;> norm_num [inv_root_two_mul_self_complex]
