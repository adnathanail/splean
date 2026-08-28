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

end ZX.Equiv

end SpLean.Algebraic
