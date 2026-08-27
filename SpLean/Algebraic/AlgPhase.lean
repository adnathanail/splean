import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

def AlgPhase : Type := ℚ

namespace AlgPhase

/-- The phase `q·π`. -/
def ofRat (q : ℚ) : AlgPhase := q

/-- The rational multiple of π that this phase is. -/
def toRat (p : AlgPhase) : ℚ := p

def num (p : AlgPhase) : ℤ := p.toRat.num
def den (p : AlgPhase) : ℕ := p.toRat.den

theorem den_pos (p : AlgPhase) : 0 < p.den := Rat.den_pos p.toRat

/-- The denominator as a `ℕ+`, for building a graph-style `Phase`. -/
def den' (p : AlgPhase) : ℕ+ := ⟨p.den, p.den_pos⟩

noncomputable def angle (p : AlgPhase) : ℝ := (p.toRat : ℝ) * Real.pi

end AlgPhase
