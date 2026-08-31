import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

/-!
# π-commutation ("π-copy")

An X spider with phase π pushed through a Z spider negates the Z spider's phase
and comes out copied onto every one of its output legs.

`ZX.nStack m (ZX.spider .X 1 1 π)` is
  "a π spider on each of the `m` outputs".
-/

namespace SpLean.Algebraic

/-- A π-phase X spider commutes through a Z spider, negating its phase and
copying itself onto every output leg. -/
theorem pi_copy_Z (m : ℕ) (α : AlgPhase) :
    (ZX.spider .X 1 1 π ≫ ZX.spider .Z 1 m α)
      ≈zx (ZX.spider .Z 1 m (-α) ≫ ZX.nStack m (ZX.spider .X 1 1 π)) := by
  sorry

/-- π-commutation, colours swapped. -/
theorem pi_copy_X (m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z 1 1 π ≫ ZX.spider .X 1 m α)
      ≈zx (ZX.spider .X 1 m (-α) ≫ ZX.nStack m (ZX.spider .Z 1 1 π)) := by
  sorry

end SpLean.Algebraic
