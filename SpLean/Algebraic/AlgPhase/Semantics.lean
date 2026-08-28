import SpLean.Algebraic.AlgPhase.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential

namespace AlgPhase

/-! ## The real angle a phase denotes -/

noncomputable def angle (p : AlgPhase) : ℝ := (p.toRat : ℝ) * Real.pi

theorem angle_eq (p : AlgPhase) : p.angle = (p.toRat : ℝ) * Real.pi := rfl

/-! `push_cast` turns `AlgPhase` arithmetic sitting under a cast into plain
rational arithmetic, at which point `ring` can finish. -/
attribute [push_cast] toRat_ofRat toRat_zero toRat_one toRat_add toRat_neg toRat_sub
  toRat_natCast toRat_intCast toRat_ofNat toRat_nsmul toRat_zsmul

/-! ## The unit complex number a phase denotes

`e^{iqπ}` is the only observation of a phase that is blind to the choice of
representative mod 2π, so it is what `ZX.sem` runs on. Everything below is its
API: a proof should not have to unfold `expI`, because an unfolded `expI` has
already thrown away the invariance that is the whole point of it. -/

noncomputable def expI (p : AlgPhase) : ℂ :=
  Complex.exp ((p.toRat : ℂ) * (Real.pi : ℂ) * Complex.I)

/-- The single escape hatch, for goals that genuinely need `Complex.exp`.
Prefer the lemmas below. -/
theorem expI_def (p : AlgPhase) :
    p.expI = Complex.exp ((p.toRat : ℂ) * (Real.pi : ℂ) * Complex.I) := rfl

theorem expI_ofRat (q : ℚ) :
    (ofRat q).expI = Complex.exp ((q : ℂ) * (Real.pi : ℂ) * Complex.I) := rfl

/-- The bridge to `angle`, so the two exits from `AlgPhase` are related rather
than rival. -/
theorem expI_eq_exp_angle (p : AlgPhase) :
    p.expI = Complex.exp ((p.angle : ℂ) * Complex.I) := by
  unfold expI angle
  congr 1
  push_cast
  ring

@[simp] theorem expI_ne_zero (p : AlgPhase) : p.expI ≠ 0 := Complex.exp_ne_zero _

/-! ### Arithmetic

`+` becomes `*`, which is the entire content of spider fusion. -/

@[simp] theorem expI_add (p q : AlgPhase) : (p + q).expI = p.expI * q.expI := by
  unfold expI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem expI_neg (p : AlgPhase) : (-p).expI = (p.expI)⁻¹ := by
  unfold expI
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

@[simp] theorem expI_sub (p q : AlgPhase) : (p - q).expI = p.expI / q.expI := by
  rw [sub_eq_add_neg, expI_add, expI_neg, div_eq_mul_inv]

@[simp] theorem expI_zsmul (n : ℤ) (p : AlgPhase) : (n • p).expI = p.expI ^ n := by
  unfold expI
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

@[simp] theorem expI_nsmul (n : ℕ) (p : AlgPhase) : (n • p).expI = p.expI ^ n := by
  rw [← natCast_zsmul p n, expI_zsmul, zpow_natCast]

/-! ### Values

The phase notation elaborates to `ofRat`, so both the `ofRat` form and the
numeral form of each constant are given: they are definitionally equal but not
syntactically, and `simp` matches syntactically. -/

@[simp] theorem expI_zero : (0 : AlgPhase).expI = 1 := by
  rw [expI_def, toRat_zero]
  norm_num

/-- The phase `π`. -/
@[simp] theorem expI_one : (1 : AlgPhase).expI = -1 := by
  have h : ((1 : AlgPhase).toRat : ℂ) * (Real.pi : ℂ) * Complex.I
      = (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [expI_def, h, Complex.exp_pi_mul_I]

@[simp] theorem expI_ofRat_zero : (ofRat 0).expI = 1 := by
  have h : (((ofRat 0).toRat : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I = 0 := by
    push_cast; ring
  rw [expI_def, h, Complex.exp_zero]

/-- `π`, as the notation writes it. -/
@[simp] theorem expI_ofRat_one : (ofRat 1).expI = -1 := by
  have h : (((ofRat 1).toRat : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I
      = (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [expI_def, h, Complex.exp_pi_mul_I]

/-- `π/2`, as the notation writes it. -/
@[simp] theorem expI_ofRat_half : (ofRat (1 / 2)).expI = Complex.I := by
  have h : (((ofRat (1 / 2)).toRat : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I
      = (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
  rw [expI_def, h, Complex.exp_pi_div_two_mul_I]

@[simp] theorem expI_intCast (n : ℤ) : ((n : AlgPhase)).expI = (-1 : ℂ) ^ n := by
  have h : (((n : AlgPhase).toRat : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I
      = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [expI_def, h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

@[simp] theorem expI_natCast (n : ℕ) : ((n : AlgPhase)).expI = (-1 : ℂ) ^ n := by
  rw [← Int.cast_natCast (R := AlgPhase), expI_intCast, zpow_natCast]

@[simp] theorem expI_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : AlgPhase).expI = (-1 : ℂ) ^ (OfNat.ofNat n : ℕ) := by
  rw [← Nat.cast_ofNat (R := AlgPhase), expI_natCast]

/-- `kπ` for a numeral `k ≥ 2` — `2π`, `3π`, … — as the notation writes it. The
`ofRat` forms need their own lemmas because `simp` matches syntactically and the
notation never produces the `AlgPhase` numeral. -/
@[simp] theorem expI_ofRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofRat (no_index (OfNat.ofNat n) : ℚ)).expI = (-1 : ℂ) ^ (OfNat.ofNat n : ℕ) := by
  rw [show (ofRat (OfNat.ofNat n : ℚ)) = ((OfNat.ofNat n : ℕ) : AlgPhase) from
        ext (by push_cast; ring),
      expI_natCast]

/-! ### Equivalence mod 2π -/

@[simp] theorem expI_ofRat_two_mul_intCast (n : ℤ) : (ofRat (2 * (n : ℚ))).expI = 1 := by
  have h : (((ofRat (2 * (n : ℚ))).toRat : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [expI_def, h, Complex.exp_int_mul_two_pi_mul_I]

@[simp] theorem expI_add_two_mul_intCast (p : AlgPhase) (n : ℤ) :
    (p + ofRat (2 * (n : ℚ))).expI = p.expI := by
  rw [expI_add, expI_ofRat_two_mul_intCast, mul_one]

/-! ## Equality of phases -/

/-- Equality of phases mod 2π. -/
def equiv (p q : AlgPhase) : Prop := p.expI = q.expI

theorem equiv_iff {p q : AlgPhase} : equiv p q ↔ p.expI = q.expI := Iff.rfl

theorem expI_congr {p q : AlgPhase} (h : equiv p q) : p.expI = q.expI := h

@[refl] theorem equiv_refl (p : AlgPhase) : equiv p p := rfl

@[symm] theorem equiv_symm {p q : AlgPhase} (h : equiv p q) : equiv q p := h.symm

theorem equiv_trans {p q r : AlgPhase} (h₁ : equiv p q) (h₂ : equiv q r) : equiv p r :=
  h₁.trans h₂

instance : Trans equiv equiv equiv := ⟨equiv_trans⟩

theorem equiv_equivalence : Equivalence equiv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-! ### `equiv` is a congruence for the whole phase algebra

This is what `AlgPhase/Defs.lean` promises when it restricts phases to an
`AddCommGroupWithOne`: `+`, `-` and `•` respect `equiv`, and `*` and `/` — which
do not elaborate — would not. -/

theorem equiv_add {p p' q q' : AlgPhase} (hp : equiv p p') (hq : equiv q q') :
    equiv (p + q) (p' + q') := by
  unfold equiv at *
  rw [expI_add, expI_add, hp, hq]

theorem equiv_neg {p p' : AlgPhase} (h : equiv p p') : equiv (-p) (-p') := by
  unfold equiv at *
  rw [expI_neg, expI_neg, h]

theorem equiv_sub {p p' q q' : AlgPhase} (hp : equiv p p') (hq : equiv q q') :
    equiv (p - q) (p' - q') := by
  unfold equiv at *
  rw [expI_sub, expI_sub, hp, hq]

theorem equiv_zsmul (n : ℤ) {p p' : AlgPhase} (h : equiv p p') : equiv (n • p) (n • p') := by
  unfold equiv at *
  rw [expI_zsmul, expI_zsmul, h]

theorem equiv_nsmul (n : ℕ) {p p' : AlgPhase} (h : equiv p p') : equiv (n • p) (n • p') := by
  unfold equiv at *
  rw [expI_nsmul, expI_nsmul, h]

/-- The period, at the level of `equiv`. -/
theorem equiv_add_two_mul_intCast (p : AlgPhase) (n : ℤ) :
    equiv (p + ofRat (2 * (n : ℚ))) p :=
  expI_add_two_mul_intCast p n

end AlgPhase
