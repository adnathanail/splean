import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

/-!
# The copy rule

X spiders with no inputs and phase `0` or `π` (`|0⟩` or `|1⟩` up to scalar)
are copied by a Z spider: it passes through and comes out once on every output leg.
-/

namespace SpLean.Algebraic

/-- A phase-free X state is copied by a Z spider of any phase. -/
theorem state_copy_Z_zero (m : ℕ) (β : AlgPhase) :
    (ZX.spider .X 0 1 ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1) := by
  sorry

/-- A π-phase X state is copied by a Z spider of any phase. -/
theorem state_copy_Z_pi (m : ℕ) (β : AlgPhase) :
    (ZX.spider .X 0 1 π ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1 π) := by
  sorry

/-- An X state with phase equivalent to `0` or `π` is copied by a Z spider of any phase. -/
theorem state_copy_Z_mod_two_pi (m : ℕ) {α : AlgPhase} (β : AlgPhase)
    (h : AlgPhase.equiv α 0 ∨ AlgPhase.equiv α π) :
    (ZX.spider .X 0 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.nStackState m (ZX.spider .X 0 1 α) := by
  sorry

/-- A phase-free Z state is copied by an X spider of any phase. -/
theorem state_copy_X_zero (m : ℕ) (β : AlgPhase) :
    (ZX.spider .Z 0 1 ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1) := by
  sorry

/-- A π-phase Z state is copied by an X spider of any phase. -/
theorem state_copy_X_pi (m : ℕ) (β : AlgPhase) :
    (ZX.spider .Z 0 1 π ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1 π) := by
  sorry

/-- A Z state with phase equivalent to `0` or `π` is copied by an X spider of any phase. -/
theorem state_copy_X_mod_two_pi (m : ℕ) {α : AlgPhase} (β : AlgPhase)
    (h : AlgPhase.equiv α 0 ∨ AlgPhase.equiv α π) :
    (ZX.spider .Z 0 1 α ≫ ZX.spider .X 1 m β) ≈zx ZX.nStackState m (ZX.spider .Z 0 1 α) := by
  sorry

end SpLean.Algebraic
