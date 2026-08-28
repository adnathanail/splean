import SpLean.Algebraic.AlgPhase.Defs
import SpLean.ZXDiagram

namespace AlgPhase

def num (p : AlgPhase) : ℤ := p.toRat.num
def den (p : AlgPhase) : ℕ := p.toRat.den

theorem den_pos (p : AlgPhase) : 0 < p.den := Rat.den_pos p.toRat

/-- The denominator as a `ℕ+`, for building a graph-style `Phase`. -/
def den' (p : AlgPhase) : ℕ+ := ⟨p.den, p.den_pos⟩

-- TODO create agnostic representation for sending to zxcc
def toPhase (p : AlgPhase) : Phase := ⟨p.num, p.den'⟩

/-- Human-readable form of the phase `q·π`: `0`, `π`, `-π`, `π/2`, `3π/2`, … -/
def formatRat (q : ℚ) : String :=
  if q.num = 0 then "0"
  else
    let ns := if q.num = 1 then "" else if q.num = -1 then "-" else toString q.num
    let ds := if q.den = 1 then "" else s!"/{q.den}"
    s!"{ns}π{ds}"

/-- Renders the phase (unnormalized): `ofRat (-1/4)` shows `-π/4`, `ofRat (5/2)`
      shows `5π/2`.
    Nothing has silently moved it into `[0, 2π)`. -/
def format (p : AlgPhase) : String := formatRat p.toRat

instance : Repr AlgPhase := ⟨fun p _ => Std.Format.text p.format⟩
instance : ToString AlgPhase := ⟨format⟩

end AlgPhase
