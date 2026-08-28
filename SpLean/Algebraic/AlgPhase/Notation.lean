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

/-! ### Parsing

Plain `syntax` + `macro_rules` rather than `notation`, because `notation` also
generates one unexpander per form, and *which* of the four then prints is
decided by the order the declarations happen to appear in this file (the
last-declared is tried first). Display order matters here — a symbolic phase
reaches the viewer as pretty-printer output, see `Algebraic/Render.lean` — so
it is written out in `unexpandOfRat` below instead of left to file order.
These four parsers are byte-identical to the ones `notation` built. -/

/-- The phase `kπ`. See the note above on why this is not at `max`. -/
scoped syntax:70 (name := kPi) term:0 "π" : term

/-- The phase `π`. -/
scoped syntax:max (name := piLit) "π" : term

/-- The phase `π/n`. -/
scoped syntax:max (name := piOver) "π/" term : term

/-- The phase `kπ/n`. -/
scoped syntax:max (name := kPiOver) term:0 "π/" term : term

-- The `kind :=` is needed because `$k π` also parses as an application of `$k`
-- to `π`, and a `macro_rules` pattern may not be ambiguous.
-- TODO can we improve the binding here?
--   e.g. failures:
--   ZX.spider .X 1 1 2π
--   (π/2 + π/2)
macro_rules (kind := kPi)     | `($k π)     => `(AlgPhase.ofRat $k)
macro_rules (kind := piLit)   | `(π)        => `(AlgPhase.ofRat 1)
macro_rules (kind := piOver)  | `(π/ $n)    => `(AlgPhase.ofRat (1 / $n))
macro_rules (kind := kPiOver) | `($k π/ $n) => `(AlgPhase.ofRat ($k / $n))

/-! ### Display

One unexpander for all four forms, tried top to bottom: the specific shapes
first and `kπ` as the catch-all. `AlgPhase.format` is what a *closed* phase is
drawn with, so this is what governs the symbolic ones — `α`, `β + π`, `α + π/4`.

The `kπ` and `kπ/n` results are built as nodes rather than written as
quotations for the same reason the `macro_rules` above need their `kind :=`:
`` `($k π) `` is ambiguous with an application. -/

open Lean in
/-- Print `AlgPhase.ofRat` back as phase notation. -/
@[app_unexpander AlgPhase.ofRat]
def unexpandOfRat : PrettyPrinter.Unexpander := fun stx => do
  let `($_ $q) := stx | throw ()
  match q with
  | `(1)       => `(π)
  | `(1 / $n)  => `(π/ $n)
  | `($k / $n) => return mkNode ``kPiOver #[k, mkAtom "π/", n]
  | _          => return mkNode ``kPi #[q, mkAtom "π"]

end SpLean.Algebraic
