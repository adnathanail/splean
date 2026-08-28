import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas

/-!
# Structural laws for `≫`

`(a ≫ b) ≫ c` and `a ≫ (b ≫ c)` are different terms, with the same semantics

`compose_assoc` allows regrouping a diagram so the rule can see its redex:
  `hadamard ≫ (hadamard ≫ c)` has no `hadamard ≫ hadamard` subterm for
    `hadamard_hadamard` to hit until it is reassociated.

`wire_compose`/`compose_wire` then clear away the `wire` such a cancellation
leaves behind.
-/

namespace SpLean.Algebraic

/-- Composition is associative up to `≈zx`.

Use it with `zx_rw` to regroup before another rule fires; the arguments are
explicit so a particular grouping can be targeted:
`zx_rw [← compose_assoc ZX.hadamard ZX.hadamard]`. -/
theorem compose_assoc {n m k l : ℕ} (a : ZX n m) (b : ZX m k) (c : ZX k l) :
    ((a ≫ b) ≫ c) ≈zx (a ≫ (b ≫ c)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A `wire` on the left of a composition does nothing. -/
theorem wire_compose {m : ℕ} (a : ZX 1 m) : (ZX.wire ≫ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires1]
  cases h : f 0 <;> simp
  · rw [wires1_eq_of_head (g := zeroAmpl) h]
  · rw [wires1_eq_of_head (g := oneAmpl) h]

/-- A `wire` on the right of a composition does nothing. -/
theorem compose_wire {n : ℕ} (a : ZX n 1) : (a ≫ ZX.wire) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires1]
  cases h : g 0 <;> simp
  · rw [wires1_eq_of_head (g := zeroAmpl) h]
  · rw [wires1_eq_of_head (g := oneAmpl) h]

end SpLean.Algebraic
