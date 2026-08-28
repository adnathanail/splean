import SpLean.Algebraic.Semantics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SpLean.Algebraic

/-- Semantic equivalence of ZX terms: equal tensors up to a nonzero global
scalar (VyZX's proportionality). -/
-- TODO track scalar factors
def ZX.Equiv {n m : ℕ} (a b : ZX n m) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f g, a.sem f g = c * b.sem f g

@[inherit_doc] scoped infix:50 " ≈zx " => ZX.Equiv

namespace ZX.Equiv

theorem refl {n m : ℕ} (a : ZX n m) : a ≈zx a := by
  use 1
  norm_num

theorem symm {n m : ℕ} {a b : ZX n m} : a ≈zx b → b ≈zx a := by
  -- Expand a→b equivalence into existential
  rw [ZX.Equiv]
  -- Split implication into hypothesis and goal
  intro h
  -- Split up existential hypothesis
  obtain ⟨c, hc, hab⟩ := h
  -- Expand b→a equivalence
  rw [ZX.Equiv]
  -- Rewrite b→a to have the constant on RHS
  refine ⟨c⁻¹, inv_ne_zero hc, fun f g => ?_⟩
  rw [
    -- Use hypothesis to replace a.sem with b.sem
    hab f g,
    -- Simplify constants (using non-negativity hypothesis)
    inv_mul_cancel_left₀ hc
  ]

end ZX.Equiv

end SpLean.Algebraic
