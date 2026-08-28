import SpLean.Algebraic.Semantics

namespace SpLean.Algebraic

-- Boundary assignments of a single wire. `abbrev`, not `def`, so `simp` and
-- `norm_num` can still see through to `false`/`true`.
abbrev zeroAmpl : Wires 1 := fun _ => false
abbrev oneAmpl : Wires 1 := fun _ => true

/-- A sum over every single-wire boundary assignment is a two-term sum: there
are only `zeroAmpl` and `oneAmpl`. Replaces the
`rw [show Finset.univ = {zeroAmpl, oneAmpl} from by decide]; rw [Finset.sum_pair (by decide)]`
pair; use `simp only [sum_wires1]` to hit nested sums in one go. -/
lemma sum_wires1 {M : Type*} [AddCommMonoid M] (F : Wires 1 → M) :
    ∑ g : Wires 1, F g = F zeroAmpl + F oneAmpl := by
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  exact Finset.sum_pair (by decide)

-- Boundary assignments for wires where all are false/true
lemma all_wires_false {n : ℕ} :
  ∀ x : Fin n → Bool, (∀ i, x i = false) ↔ x = fun _ => false := by
  exact fun x => Iff.symm funext_iff
lemma all_wires_true {n : ℕ} :
  ∀ x : Fin n → Bool, (∀ i, x i = true) ↔ x = fun _ => true := by
  exact fun x => Iff.symm funext_iff

lemma sum_bool_all_false {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        (if ∀ i, x i = false then a x else 0) = a (fun _ => false) := by
  simp only [all_wires_false]
  norm_num

lemma sum_bool_all_true {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        (if ∀ i, x i = true then a x else 0) = a (fun _ => true) := by
  simp only [all_wires_true]
  norm_num

/-- Both endpoints at once. Just the two one-sided lemmas, split apart with
`Finset.sum_add_distrib`. -/
lemma sum_bool_endpoints {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a b : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        ((if ∀ i, x i = false then a x else 0) + if ∀ i, x i = true then b x else 0)
      = a (fun _ => false) + b (fun _ => true) := by
  rw [Finset.sum_add_distrib, sum_bool_all_false, sum_bool_all_true]

/-- The two-boundary version of `sum_bool_endpoints`: a double sum whose only
surviving terms are "everything false" and "everything true" on *both*
boundaries at once. This is the shape the RHS of a spider-fusion goal takes,
where the `∀ i, x i = false` and `∀ j, y j = false` guards are conjoined
inside a single `ite`. -/
lemma sum_bool_endpoints₂ {n m : ℕ} {M : Type*} [AddCommMonoid M]
    (a b : (Fin n → Bool) → (Fin m → Bool) → M) :
    ∑ x : Fin n → Bool, ∑ y : Fin m → Bool,
        ((if (∀ i, x i = false) ∧ (∀ j, y j = false) then a x y else 0)
          + if (∀ i, x i = true) ∧ (∀ j, y j = true) then b x y else 0)
      = a (fun _ => false) (fun _ => false) + b (fun _ => true) (fun _ => true) := by
  simp only [all_wires_false, all_wires_true, ite_and, Finset.sum_add_distrib]
  simp


/-! ### `√2` arithmetic -/

lemma inv_root_two_add_self : (√2)⁻¹ + (√2)⁻¹ = √2 := by
  field_simp
  norm_num
lemma inv_root_two_add_self_complex :
    ((√2 : ℝ) : ℂ)⁻¹ + ((√2 : ℝ) : ℂ)⁻¹ = √2 := by
  norm_cast
  rw [inv_root_two_add_self]

lemma inv_root_two_mul_self : (√2)⁻¹ * (√2)⁻¹ = 1/2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
lemma inv_root_two_mul_self_complex :
    ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1/2 := by
  norm_cast
  rw [inv_root_two_mul_self]
  norm_num

lemma inv_root_two_sq : (√2)⁻¹ ^ 2 = 1/2 := by
  rw [sq, inv_root_two_mul_self]
lemma inv_root_two_sq_complex : ((√2 : ℝ) : ℂ)⁻¹ ^ 2 = 1/2 := by
  rw [sq, inv_root_two_mul_self_complex]

end SpLean.Algebraic
