import SpLean.Algebraic.AlgPhase.Defs

/-!
# Notation for phase literals

A phase is a rational multiple of π, so these write it the way the ZX
literature does: `π`, `2π`, `π/4`, `3π/4`.

They are `scoped` in `SpLean.Algebraic` rather than in `AlgPhase` so that the
single `open SpLean.Algebraic` a file already needs for `≫` and `⊗` brings the
phase syntax along with it.

Precedence: the `k "π"` form is deliberately at `70` rather than `max`. At `max`
it would win against a bare `π` in argument position, so `.spider .Z 1 1 π`
would parse the arity `1` and the `π` together as `1π` and the arity would go
missing. At `70` it cannot start an argument, which leaves `π` — the one form
common enough to matter — usable unparenthesised:

    .spider .Z 0 0 π           -- fine
    .spider .Z 1 1 (π/4)       -- everything else takes parentheses
    .spider .Z 0 0 (2π)

`π` and `π/` are registered as tokens, so a `Real.pi` division elsewhere in this
project has to be written with spaces (`π / 4`) if `Real` is open. Nothing in
the project currently uses `π` for `Real.pi`; it is spelled out.
-/

namespace SpLean.Algebraic

/-- The phase `π`. -/
scoped notation:max "π" => AlgPhase.ofRat 1

/-- The phase `π/n`. -/
scoped notation:max "π/" n => AlgPhase.ofRat (1 / n)

/-- The phase `kπ/n`. -/
scoped notation:max k "π/" n => AlgPhase.ofRat (k / n)

/-- The phase `kπ`. See the note above on why this is not `notation:max`. -/
scoped notation:70 k "π" => AlgPhase.ofRat k

end SpLean.Algebraic
