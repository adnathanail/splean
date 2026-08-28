import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

def AlgPhase : Type := ℚ

namespace AlgPhase

/-! `AlgPhase` is a `def` rather than an `abbrev` so that the representation can
change later, but that hides `ℚ`'s instances: without them a literal phase like
`1 / 2` has no `OfNat`/`Div` to elaborate against and every use site needs a
`(· : ℚ)` ascription. Transport the ones needed to write and compute with phase
literals. -/

instance : Field AlgPhase := inferInstanceAs (Field ℚ)
instance : DecidableEq AlgPhase := inferInstanceAs (DecidableEq ℚ)
instance : Repr AlgPhase := inferInstanceAs (Repr ℚ)
instance : Inhabited AlgPhase := inferInstanceAs (Inhabited ℚ)

/-- The phase `q·π`. -/
def ofRat (q : ℚ) : AlgPhase := q

/-- The rational multiple of π that this phase is. -/
def toRat (p : AlgPhase) : ℚ := p

@[simp] theorem toRat_ofRat (q : ℚ) : (ofRat q).toRat = q := rfl
@[simp] theorem ofRat_toRat (p : AlgPhase) : ofRat p.toRat = p := rfl

theorem ext {p q : AlgPhase} (h : p.toRat = q.toRat) : p = q := h

/-! ### The whole algebra is inherited, and every law is `rfl` -/

@[simp] theorem toRat_zero : (0 : AlgPhase).toRat = 0 := rfl
@[simp] theorem toRat_add (p q : AlgPhase) : (p + q).toRat = p.toRat + q.toRat := rfl
@[simp] theorem toRat_neg (p : AlgPhase) : (-p).toRat = -p.toRat := rfl
@[simp] theorem toRat_sub (p q : AlgPhase) : (p - q).toRat = p.toRat - q.toRat := rfl

@[simp] theorem toRat_zsmul (n : ℤ) (p : AlgPhase) : (n • p).toRat = (n : ℚ) * p.toRat := by
  show n • p.toRat = (n : ℚ) * p.toRat
  exact zsmul_eq_mul _ _

@[simp] theorem ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := rfl

/-! ### Display -/

def num (p : AlgPhase) : ℤ := p.toRat.num
def den (p : AlgPhase) : ℕ := p.toRat.den

theorem den_pos (p : AlgPhase) : 0 < p.den := Rat.den_pos p.toRat

/-- The denominator as a `ℕ+`, for building a graph-style `Phase`. -/
def den' (p : AlgPhase) : ℕ+ := ⟨p.den, p.den_pos⟩

noncomputable def angle (p : AlgPhase) : ℝ := (p.toRat : ℝ) * Real.pi

@[simp] theorem angle_add (p q : AlgPhase) : (p + q).angle = p.angle + q.angle := by
  unfold angle
  rw [toRat_add]
  push_cast
  ring

@[simp] theorem angle_neg (p : AlgPhase) : (-p).angle = -p.angle := by
  unfold angle
  rw [toRat_neg]
  push_cast
  ring

@[simp] theorem angle_zero : (0 : AlgPhase).angle = 0 := by
  unfold angle
  rw [toRat_zero]
  push_cast
  ring

end AlgPhase
