import SpLean.Algebraic.Semantics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SpLean.Algebraic

/-- Semantic equivalence of ZX terms: equal tensors up to a nonzero global
scalar (VyZX's proportionality). -/
-- TODO track scalar factors
def ZX.Equiv {n m : ℕ} (a b : ZX n m) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f g, a.sem f g = c * b.sem f g
