import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Combinators

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

/-- `nWire n` is a left identity for `≫` — the `n`-wire form of `wire_compose`. -/
theorem nWire_compose {n m : ℕ} (a : ZX n m) : (ZX.nWire n ≫ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, n_wire_sem]
  have h : ∀ x : Wires n,
    (if f = x then 1 else 0) * a.sem x g = if f = x then a.sem f g else 0 := by
      simp_all only [ite_mul, one_mul, zero_mul, implies_true]
  simp only [h]
  norm_num

/-- `nWire m` is a right identity for `≫` — the `n`-wire form of `compose_wire`. -/
theorem compose_nWire {n m : ℕ} (a : ZX n m) : (a ≫ ZX.nWire m) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, n_wire_sem]
  have h : ∀ x : Wires m,
    (a.sem f x * if x = g then 1 else 0) = if x = g then a.sem f g else 0 := by
      simp_all only [mul_ite, mul_one, mul_zero, implies_true]
  simp only [h]
  norm_num

end SpLean.Algebraic
