import SpLean.Algebraic.AlgPhase.Defs

namespace AlgPhase

def num (p : AlgPhase) : ℤ := p.toRat.num
def den (p : AlgPhase) : ℕ := p.toRat.den

theorem den_pos (p : AlgPhase) : 0 < p.den := Rat.den_pos p.toRat

/-- The denominator as a `ℕ+`, for building a graph-style `Phase`. -/
def den' (p : AlgPhase) : ℕ+ := ⟨p.den, p.den_pos⟩

end AlgPhase
