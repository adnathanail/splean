import SpLean.Algebraic.AlgPhase.Semantics
import Mathlib.Data.Rat.Floor

namespace AlgPhase

/-!
## Reduction of rationals to `[0, 2)`

A phase is a *rational multiple of π*: the rational `q` denotes the angle `q·π`,
so `1/2` is `π/2` and the period is `q ↦ q + 2`.
-/

def red (q : ℚ) : ℚ := q - 2 * ⌊q / 2⌋

theorem red_nonneg (q : ℚ) : 0 ≤ red q := by
  have h : ((⌊q / 2⌋ : ℤ) : ℚ) ≤ q / 2 := Int.floor_le _
  unfold red
  linarith

theorem red_lt_two (q : ℚ) : red q < 2 := by
  have h : q / 2 < ((⌊q / 2⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  unfold red
  linarith

/-- `red` is the identity on `[0, 2)`. -/
theorem red_of_mem (q : ℚ) (h0 : 0 ≤ q) (h2 : q < 2) : red q = q := by
  have hz : ⌊q / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    constructor <;> linarith
  unfold red
  rw [hz]
  push_cast
  ring

@[simp] theorem red_idem (q : ℚ) : red (red q) = red q :=
  red_of_mem _ (red_nonneg q) (red_lt_two q)

theorem red_add_two_mul_int (q : ℚ) (n : ℤ) : red (q + 2 * (n : ℚ)) = red q := by
  unfold red
  have h : (q + 2 * (n : ℚ)) / 2 = q / 2 + (n : ℚ) := by ring
  rw [h, Int.floor_add_intCast]
  push_cast
  ring

/-- Two rationals reduce alike exactly when they differ by an even integer. This
is the combinatorial half of `expI_eq_iff` below. -/
theorem red_eq_red_iff (a b : ℚ) : red a = red b ↔ ∃ n : ℤ, a - b = 2 * (n : ℚ) := by
  constructor
  · intro h
    refine ⟨⌊a / 2⌋ - ⌊b / 2⌋, ?_⟩
    unfold red at h
    push_cast
    linarith
  · rintro ⟨n, hn⟩
    have h : a = b + 2 * (n : ℚ) := by linarith
    rw [h, red_add_two_mul_int]

/-!
## Normal forms for phases

`normalize` is a *decision procedure* for `equiv`, not its definition —
`AlgPhase/Semantics.lean` defines `equiv` as the kernel of `expI`, and
`expI_eq_iff` below proves the two agree. Stating it this way round means the
property the semantics needs is true by construction and the arithmetic here is
what has to be justified, rather than the other way about.
-/

def normalize (p : AlgPhase) : AlgPhase := ofRat (red p.toRat)

@[simp] theorem normalize_idem (p : AlgPhase) : normalize (normalize p) = normalize p :=
  congrArg ofRat (red_idem p.toRat)

@[simp] theorem expI_normalize (p : AlgPhase) : (normalize p).expI = p.expI := by
  have h : normalize p = p + ofRat (2 * ((-⌊p.toRat / 2⌋ : ℤ) : ℚ)) := by
    apply ext
    simp only [normalize, toRat_ofRat, toRat_add, red]
    push_cast
    ring
  rw [h, expI_add_two_mul_intCast]

/-- `q ↦ e^{iqπ}` is injective on reduced representatives, so the kernel of the
denotation is decided by comparing normal forms. Together with `equiv`'s
definition this says `normalize` and `expI` cut `AlgPhase` into exactly the same
classes — the claim the rest of the file rests on. -/
theorem expI_eq_iff (p q : AlgPhase) : p.expI = q.expI ↔ normalize p = normalize q := by
  rw [expI_def, expI_def, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    have hbase : ((Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
    have h0 : ((p.toRat : ℂ) - (q.toRat : ℂ) - 2 * (n : ℂ)) * ((Real.pi : ℂ) * Complex.I) = 0 := by
      linear_combination hn
    have h1 : (p.toRat : ℂ) - (q.toRat : ℂ) - 2 * (n : ℂ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hbase
    have h2 : ((p.toRat - q.toRat : ℚ) : ℂ) = ((2 * (n : ℚ) : ℚ) : ℂ) := by
      push_cast
      linear_combination h1
    exact congrArg ofRat ((red_eq_red_iff _ _).mpr ⟨n, by exact_mod_cast h2⟩)
  · intro h
    have h1 : red p.toRat = red q.toRat := congrArg toRat h
    obtain ⟨n, hn⟩ := (red_eq_red_iff _ _).mp h1
    refine ⟨n, ?_⟩
    have h2 : p.toRat = q.toRat + 2 * (n : ℚ) := by linarith
    rw [h2]
    push_cast
    ring

theorem equiv_iff_normalize_eq {p q : AlgPhase} : equiv p q ↔ normalize p = normalize q :=
  expI_eq_iff p q

/-- Decidability comes from the normal form, which is why `red` is worth having
at all: `equiv` as defined is an equation between two transcendental numbers.

Note that this is a *runtime* decision procedure — `#eval`, `Decidable.decide`,
LSpec tests — and not one `decide` can use in a proof: `Int.floor` on `ℚ` does
not reduce in the kernel, so `decide` gets stuck inside `red`. In a proof, unfold
instead: `rw [equiv_iff_normalize_eq]; norm_num [normalize, red]`.

`scoped` so that `decide`, `simp (decide := true)` or `ite` elaboration work.
Opt in with `open scoped AlgPhase` where the runtime procedure is what you want -/
scoped instance decidableEquiv (p q : AlgPhase) : Decidable (equiv p q) :=
  decidable_of_iff _ equiv_iff_normalize_eq.symm

end AlgPhase
