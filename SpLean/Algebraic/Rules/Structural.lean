import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Tactics

open SpLean.Algebraic

/-!
# Combinator semantics
-/

theorem nWire_sem (k : ℕ) (u v : Wires k) :
    (ZX.nWire k).sem u v = if u = v then 1 else 0 := by
  induction k with
  | zero =>
    simp only [ZX.nWire, ZX.nStack, ZX.sem]
    trivial
  | succ k ih =>
    simp only [ZX.nWire, ZX.nStack, ZX.sem]
    rw [ih]
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero]
    rw [← ite_and]
    refine if_congr ?_ rfl rfl
    rw [funext_iff, funext_iff]
    rw [Fin.forall_fin_succ', and_comm]
    rfl

theorem nHadamard_sem (k : ℕ) (u v : Wires k) :
    (ZX.nHadamard k).sem u v = ∏ i, hadSem (u i) (v i) := by
  induction k with
  | zero =>
    simp only [ZX.nHadamard, ZX.nStack, ZX.sem]
    norm_num
  | succ k ih =>
    simp only [ZX.nHadamard, ZX.nStack, ZX.sem]
    rw [ih]
    exact Eq.symm (Fin.prod_univ_castSucc fun i => hadSem (u i) (v i))


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
  simp only [ZX.sem, nWire_sem]
  have h : ∀ x : Wires n,
    (if f = x then 1 else 0) * a.sem x g = if f = x then a.sem f g else 0 := by
      simp_all only [ite_mul, one_mul, zero_mul, implies_true]
  simp only [h]
  norm_num

/-- `nWire m` is a right identity for `≫` — the `n`-wire form of `compose_wire`. -/
theorem compose_nWire {n m : ℕ} (a : ZX n m) : (a ≫ ZX.nWire m) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, nWire_sem]
  have h : ∀ x : Wires m,
    (a.sem f x * if x = g then 1 else 0) = if x = g then a.sem f g else 0 := by
      simp_all only [mul_ite, mul_one, mul_zero, implies_true]
  simp only [h]
  norm_num

/-- Stacking the empty diagram on the right does nothing. -/
theorem stack_empty {n m : ℕ} (a : ZX n m) : (a ⊗ .empty) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, mul_one]
  congr 1

 /-- Stacking the empty diagram on the left does nothing either
  needs the cast because `0 + n` does not reduce. -/
theorem empty_stack {n m : ℕ} (a : ZX n m) :
    ZX.cast (Nat.zero_add n) (Nat.zero_add m) (.empty ⊗ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul, ZX.sem_cast]
  simp only [ZX.sem, one_mul]
  congr 1 <;> funext i <;> congr 1 <;> (apply Fin.ext; simp)

theorem nStack_one (d : ZX 1 1) :
    (ZX.nStack 1 d) ≈zx d := by
  simp only [ZX.nStack]
  zx_rw [← ZX.cast_self _ _ (ZX.empty ⊗ d)]
  zx_rw [empty_stack]

end SpLean.Algebraic
