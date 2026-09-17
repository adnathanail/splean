import SpLean.Algebraic.Rules.Structural
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# `ZX` as a monoidal category

`ZX.compose`/`ZX.stack` are not associative or unital *on the nose* — `(a ≫ b) ≫ c` and
`a ≫ (b ≫ c)` are different terms of a free-algebra ADT — only up to `≈zx`. So the category
lives not on `ZX n m` itself but on `ZX n m` quotiented by `≈zx`: `≈zx` is already an
equivalence relation and a congruence for `≫`/`⊗` (`Equiv.lean`), which is exactly what's
needed to descend `compose`/`stack` to well-defined operations on the quotient, and the
identity/associativity/unit laws (`Rules/Structural.lean`) become literal `Eq`s there via
`Quotient.sound`.

Objects live on `ZXCat`, a type synonym for `ℕ`, rather than on `ℕ` directly, so this
`Category`/`MonoidalCategory` instance can't collide with any other category structure some
other file or a future Mathlib import attaches to `ℕ` itself.

Scope: monoidal only. No `SymmetricCategory`/`BraidedCategory` instance — that needs a `swap`
primitive ZX doesn't have yet.
-/

namespace SpLean.Algebraic

open CategoryTheory

/-- Type synonym for `ℕ` carrying the `ZX`-diagram category structure. -/
def ZXCat := ℕ

instance : Add ZXCat := ⟨Nat.add⟩

instance ZX.equivSetoid (n m : ℕ) : Setoid (ZX n m) where
  r := ZX.Equiv
  iseqv := ⟨ZX.Equiv.refl, ZX.Equiv.symm, ZX.Equiv.trans⟩

instance : CategoryStruct ZXCat where
  Hom n m := Quotient (ZX.equivSetoid n m)
  id n := Quotient.mk _ (ZX.nWire n)
  comp := Quotient.map₂ ZX.compose (fun {_ _} ha {_ _} hb => ZX.Equiv.compose_congr ha hb)

instance : Category ZXCat where
  id_comp f := Quotient.inductionOn f fun a => Quotient.sound (nWire_compose a)
  comp_id f := Quotient.inductionOn f fun a => Quotient.sound (compose_nWire a)
  assoc f g h := Quotient.inductionOn₃ f g h fun a b c => Quotient.sound (compose_assoc a b c)

/-! ## The identity, cast along an arity equality

Used to build the associator/unitors: `Nat.add` is only associative/unital up to a proved
`Eq`, not on the nose (`Nat.add_assoc`/`Nat.zero_add` are not `rfl` for general arguments —
only `Nat.add_zero` is, since `Nat.add` recurses on its *second* argument). -/

/-- The `ZX` diagram that connects `n` legs to `n'` legs with no crossings — the identity,
cast along an arity equality. -/
def ZX.castHom {n n' : ℕ} (h : n = n') : ZX n n' := ZX.cast rfl h (ZX.nWire n)

theorem ZX.castHom_comp_castHom_symm {n n' : ℕ} (h : n = n') :
    (ZX.castHom h ≫ ZX.castHom h.symm) ≈zx ZX.nWire n := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using nWire_compose (ZX.nWire n)

theorem ZX.castHom_symm_comp_castHom {n n' : ℕ} (h : n = n') :
    (ZX.castHom h.symm ≫ ZX.castHom h) ≈zx ZX.nWire n' := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using nWire_compose (ZX.nWire n)

/-- Composing with a `castHom` on the right is the same as casting the output arity. -/
theorem ZX.compose_castHom {n m m' : ℕ} (h : m = m') (a : ZX n m) :
    (a ≫ ZX.castHom h) ≈zx ZX.cast rfl h a := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using compose_nWire a

/-- Composing with a `castHom` on the left is the same as casting the input arity. -/
theorem ZX.castHom_compose {n n' m : ℕ} (h : n = n') (a : ZX n' m) :
    (ZX.castHom h ≫ a) ≈zx ZX.cast h.symm rfl a := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using nWire_compose a

/-- `nWire` is compatible with `⊗`, needed for `id_tensorHom_id`. No cast: `nStack`
recurses on its *first* index, so `n + (m+1)` and `(n+m)+1` are the same `Nat` term and
`stack_assoc`'s cast trivialises at each inductive step. -/
theorem ZX.nWire_stack (n m : ℕ) : (ZX.nWire n ⊗ ZX.nWire m) ≈zx ZX.nWire (n + m) := by
  induction m with
  | zero => exact stack_empty _
  | succ m ih =>
    show (ZX.nWire n ⊗ (ZX.nWire m ⊗ ZX.wire) : ZX (n + (m + 1)) (n + (m + 1))) ≈zx
        (ZX.nWire (n + m) ⊗ ZX.wire : ZX (n + m + 1) (n + m + 1))
    have h := stack_assoc (ZX.nWire n) (ZX.nWire m) ZX.wire
    have hcast : ZX.cast (Nat.add_assoc n m 1) (Nat.add_assoc n m 1)
        ((ZX.nWire n ⊗ ZX.nWire m) ⊗ ZX.wire) = (ZX.nWire n ⊗ ZX.nWire m) ⊗ ZX.wire := rfl
    rw [hcast] at h
    exact h.symm.trans (ZX.Equiv.stack_congr ih (ZX.Equiv.refl ZX.wire))

/-! ## `castHom` algebra, for `pentagon`/`triangle`

Both are equations between composites of *only* identities and associators/unitors — no
general morphism ever appears — so every term reduces to a single `castHom`, and two
`castHom`s of the same arity equation are equal outright: `ZX.castHom` only pattern-matches on
its proof's *type* via `▸`, and `Prop` is proof-irrelevant, so which proof is supplied never
matters. Collapsing both sides of an equation down to `castHom` of *some* proof of the same
`Nat` equality is enough — no arithmetic identity between the proofs themselves is needed. -/

theorem ZX.castHom_trans {n n' n'' : ℕ} (h1 : n = n') (h2 : n' = n'') :
    (ZX.castHom h1 ≫ ZX.castHom h2) ≈zx ZX.castHom (h1.trans h2) := by
  subst h1; subst h2
  simpa only [ZX.castHom, ZX.cast_self] using nWire_compose (ZX.nWire n)

theorem ZX.castHom_stack_right {n n' k : ℕ} (h : n = n') :
    (ZX.castHom h ⊗ ZX.nWire k) ≈zx ZX.castHom (congrArg (· + k) h) := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using ZX.nWire_stack n k

theorem ZX.castHom_stack_left {n n' k : ℕ} (h : n = n') :
    (ZX.nWire k ⊗ ZX.castHom h) ≈zx ZX.castHom (congrArg (k + ·) h) := by
  subst h
  simpa only [ZX.castHom, ZX.cast_self] using ZX.nWire_stack k n

/-- Any two `castHom`s between the same arities agree — different proofs of the same `Nat`
equation give definitionally equal `ZX.cast`s (proof irrelevance), so this needs no induction. -/
theorem ZX.castHom_proof_irrel {n n' : ℕ} (h1 h2 : n = n') : ZX.castHom h1 = ZX.castHom h2 := rfl

/-! ## The interchange law, `tensorHom_comp_tensorHom`

`(a⊗b)≫(c⊗d) ≈zx (a≫c)⊗(b≫d)`: proved directly from `ZX.sem`, since it isn't a consequence
of anything already in `Rules/`. The sum over the shared `Wires (m+q)` boundary splits into
independent sums over `Wires m` and `Wires q` via the `Fin (m+q) ≃ Fin m ⊕ Fin q` equivalence
(`finSumFinEquiv`), after which the summand's factors regroup by plain `ring`. -/

theorem ZX.sum_stack_split {m q : ℕ} (F : Wires m → Wires q → ℂ) :
    (∑ g : Wires (m + q), F (fun i => g (Fin.castAdd q i)) (fun j => g (Fin.natAdd m j)))
      = ∑ g1 : Wires m, ∑ g2 : Wires q, F g1 g2 := by
  let e : Wires (m + q) ≃ Wires m × Wires q :=
    (_root_.Equiv.arrowCongr finSumFinEquiv.symm (_root_.Equiv.refl Bool)).trans
      (_root_.Equiv.sumArrowEquivProdArrow (Fin m) (Fin q) Bool)
  have hcomp : ∀ g : Wires (m + q),
      F (fun i => g (Fin.castAdd q i)) (fun j => g (Fin.natAdd m j)) = F (e g).1 (e g).2 := by
    intro g
    have h1 : (e g).1 = fun i => g (Fin.castAdd q i) := by
      funext i
      simp [e, _root_.Equiv.arrowCongr, _root_.Equiv.sumArrowEquivProdArrow,
        _root_.Equiv.trans_apply, finSumFinEquiv_apply_left]
    have h2 : (e g).2 = fun j => g (Fin.natAdd m j) := by
      funext j
      simp [e, _root_.Equiv.arrowCongr, _root_.Equiv.sumArrowEquivProdArrow,
        _root_.Equiv.trans_apply, finSumFinEquiv_apply_right]
    rw [h1, h2]
  have step1 :
      (∑ g : Wires (m + q), F (fun i => g (Fin.castAdd q i)) (fun j => g (Fin.natAdd m j)))
        = ∑ g : Wires (m + q), F (e g).1 (e g).2 :=
    Finset.sum_congr rfl (fun g _ => hcomp g)
  have step2 : (∑ g : Wires (m + q), F (e g).1 (e g).2) = ∑ p : Wires m × Wires q, F p.1 p.2 :=
    _root_.Equiv.sum_comp e (fun p => F p.1 p.2)
  have step3 : (∑ p : Wires m × Wires q, F p.1 p.2) = ∑ g1, ∑ g2, F g1 g2 :=
    Fintype.sum_prod_type (f := fun p => F p.1 p.2)
  exact step1.trans (step2.trans step3)

theorem ZX.compose_stack_interchange {n m k p q r : ℕ}
    (a : ZX n m) (c : ZX m k) (b : ZX p q) (d : ZX q r) :
    ((a ⊗ b) ≫ (c ⊗ d)) ≈zx ((a ≫ c) ⊗ (b ≫ d)) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  have hreorder : (fun g : Wires (m + q) =>
      (a.sem (fun i => f (Fin.castAdd p i)) (fun j => g (Fin.castAdd q j)) *
          b.sem (fun i => f (Fin.natAdd n i)) (fun j => g (Fin.natAdd m j))) *
        (c.sem (fun j => g (Fin.castAdd q j)) (fun i => h (Fin.castAdd r i)) *
          d.sem (fun j => g (Fin.natAdd m j)) (fun i => h (Fin.natAdd k i))))
      = fun g : Wires (m + q) =>
        (a.sem (fun i => f (Fin.castAdd p i)) (fun j => g (Fin.castAdd q j)) *
            c.sem (fun j => g (Fin.castAdd q j)) (fun i => h (Fin.castAdd r i))) *
          (b.sem (fun i => f (Fin.natAdd n i)) (fun j => g (Fin.natAdd m j)) *
            d.sem (fun j => g (Fin.natAdd m j)) (fun i => h (Fin.natAdd k i))) := by
    funext g; ring
  rw [hreorder]
  rw [ZX.sum_stack_split
    (F := fun g1 g2 =>
      (a.sem (fun i => f (Fin.castAdd p i)) g1 * c.sem g1 (fun i => h (Fin.castAdd r i))) *
        (b.sem (fun i => f (Fin.natAdd n i)) g2 * d.sem g2 (fun i => h (Fin.natAdd k i))))]
  rw [← Finset.sum_mul_sum]

/-! ## The `MonoidalCategoryStruct` -/

def ZXCat.tensorHom {X₁ Y₁ X₂ Y₂ : ZXCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (X₁ + X₂ : ZXCat) ⟶ (Y₁ + Y₂) :=
  Quotient.map₂ ZX.stack (fun {_ _} ha {_ _} hb => ZX.Equiv.stack_congr ha hb) f g

instance : MonoidalCategoryStruct ZXCat where
  tensorObj X Y := X + Y
  tensorHom := ZXCat.tensorHom
  whiskerLeft := fun X {_ _} f => ZXCat.tensorHom (𝟙 X) f
  whiskerRight := fun {_ _} f Y => ZXCat.tensorHom f (𝟙 Y)
  tensorUnit := (0 : ℕ)
  associator X Y Z :=
    { hom := Quotient.mk _ (ZX.castHom (Nat.add_assoc X Y Z))
      inv := Quotient.mk _ (ZX.castHom (Nat.add_assoc X Y Z).symm)
      hom_inv_id := Quotient.sound (ZX.castHom_comp_castHom_symm _)
      inv_hom_id := Quotient.sound (ZX.castHom_symm_comp_castHom _) }
  leftUnitor X :=
    { hom := Quotient.mk _ (ZX.castHom (Nat.zero_add X))
      inv := Quotient.mk _ (ZX.castHom (Nat.zero_add X).symm)
      hom_inv_id := Quotient.sound (ZX.castHom_comp_castHom_symm _)
      inv_hom_id := Quotient.sound (ZX.castHom_symm_comp_castHom _) }
  rightUnitor X :=
    { hom := 𝟙 X
      inv := 𝟙 X }

/-! ## `MonoidalCategory` -/

theorem ZX.stack_assoc_naturality {X₁ Y₁ X₂ Y₂ X₃ Y₃ : ℕ}
    (a : ZX X₁ Y₁) (b : ZX X₂ Y₂) (c : ZX X₃ Y₃) :
    (((a ⊗ b) ⊗ c) ≫ ZX.castHom (Nat.add_assoc Y₁ Y₂ Y₃)) ≈zx
      (ZX.castHom (Nat.add_assoc X₁ X₂ X₃) ≫ (a ⊗ (b ⊗ c))) := by
  have hL := ZX.compose_castHom (Nat.add_assoc Y₁ Y₂ Y₃) ((a ⊗ b) ⊗ c)
  have hR := ZX.castHom_compose (Nat.add_assoc X₁ X₂ X₃) (a ⊗ (b ⊗ c))
  have hMid : ZX.cast rfl (Nat.add_assoc Y₁ Y₂ Y₃) ((a ⊗ b) ⊗ c) ≈zx
      ZX.cast (Nat.add_assoc X₁ X₂ X₃).symm rfl (a ⊗ (b ⊗ c)) := by
    rw [ZX.Equiv.cast_iff]
    simp only [ZX.cast_cast]
    have h2 := (ZX.Equiv.cast_iff (Nat.add_assoc X₁ X₂ X₃) (Nat.add_assoc Y₁ Y₂ Y₃)
      ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))).mp (stack_assoc a b c)
    simpa using h2
  exact hL.trans (hMid.trans hR.symm)

theorem ZX.empty_stack_naturality {X Y : ℕ} (a : ZX X Y) :
    ((ZX.empty ⊗ a) ≫ ZX.castHom (Nat.zero_add Y)) ≈zx (ZX.castHom (Nat.zero_add X) ≫ a) := by
  have hL := ZX.compose_castHom (Nat.zero_add Y) (ZX.empty ⊗ a)
  have hR := ZX.castHom_compose (Nat.zero_add X) a
  have hMid : ZX.cast rfl (Nat.zero_add Y) (ZX.empty ⊗ a) ≈zx
      ZX.cast (Nat.zero_add X).symm rfl a := by
    rw [ZX.Equiv.cast_iff]
    simp only [ZX.cast_cast]
    have h2 := (ZX.Equiv.cast_iff (Nat.zero_add X) (Nat.zero_add Y)
      (ZX.empty ⊗ a) a).mp (empty_stack a)
    simpa using h2
  exact hL.trans (hMid.trans hR.symm)

theorem ZX.stack_empty_naturality {X Y : ℕ} (a : ZX X Y) :
    ((a ⊗ ZX.empty) ≫ ZX.nWire Y) ≈zx (ZX.nWire X ≫ a) := by
  have hL := compose_nWire (a ⊗ ZX.empty)
  have hR := nWire_compose a
  exact hL.trans ((stack_empty a).trans hR.symm)

theorem ZX.pentagon_zx (W X Y Z : ℕ) :
    ((ZX.castHom (Nat.add_assoc W X Y) ⊗ ZX.nWire Z) ≫
        (ZX.castHom (Nat.add_assoc W (X + Y) Z) ≫
          (ZX.nWire W ⊗ ZX.castHom (Nat.add_assoc X Y Z)))) ≈zx
      (ZX.castHom (Nat.add_assoc (W + X) Y Z) ≫ ZX.castHom (Nat.add_assoc W X (Y + Z))) := by
  have hA : (ZX.castHom (Nat.add_assoc W X Y) ⊗ ZX.nWire Z) ≈zx
      ZX.castHom (congrArg (· + Z) (Nat.add_assoc W X Y)) :=
    ZX.castHom_stack_right (Nat.add_assoc W X Y)
  have hBC :
      (ZX.castHom (Nat.add_assoc W (X + Y) Z) ≫ (ZX.nWire W ⊗ ZX.castHom (Nat.add_assoc X Y Z))) ≈zx
        ZX.castHom ((Nat.add_assoc W (X + Y) Z).trans (congrArg (W + ·) (Nat.add_assoc X Y Z))) :=
    (ZX.Equiv.compose_congr (ZX.Equiv.refl _)
      (ZX.castHom_stack_left (Nat.add_assoc X Y Z))).trans (ZX.castHom_trans _ _)
  have hABC := (ZX.Equiv.compose_congr hA hBC).trans (ZX.castHom_trans _ _)
  have hRight := ZX.castHom_trans (Nat.add_assoc (W + X) Y Z) (Nat.add_assoc W X (Y + Z))
  have hEq : ZX.castHom
      ((congrArg (· + Z) (Nat.add_assoc W X Y)).trans
        ((Nat.add_assoc W (X + Y) Z).trans (congrArg (W + ·) (Nat.add_assoc X Y Z))))
      = ZX.castHom ((Nat.add_assoc (W + X) Y Z).trans (Nat.add_assoc W X (Y + Z))) :=
    ZX.castHom_proof_irrel _ _
  rw [hEq] at hABC
  exact hABC.trans hRight.symm

theorem ZX.triangle_zx (X Y : ℕ) :
    (ZX.castHom (Nat.add_assoc X 0 Y) ≫ (ZX.nWire X ⊗ ZX.castHom (Nat.zero_add Y))
      : ZX (X + 0 + Y) (X + Y)) ≈zx
      ((ZX.nWire X : ZX (X + 0) X) ⊗ ZX.nWire Y : ZX (X + 0 + Y) (X + Y)) := by
  have hL1 : (ZX.nWire X ⊗ ZX.castHom (Nat.zero_add Y)) ≈zx
      ZX.castHom (congrArg (X + ·) (Nat.zero_add Y)) :=
    ZX.castHom_stack_left (Nat.zero_add Y)
  have hL2 := ZX.Equiv.compose_congr (ZX.Equiv.refl (ZX.castHom (Nat.add_assoc X 0 Y))) hL1
  have hL3 := hL2.trans (ZX.castHom_trans (Nat.add_assoc X 0 Y) (congrArg (X + ·) (Nat.zero_add Y)))
  have hR : ((ZX.nWire X : ZX (X + 0) X) ⊗ ZX.nWire Y) ≈zx ZX.nWire (X + Y) :=
    ZX.nWire_stack X Y
  have hcast : ZX.castHom ((Nat.add_assoc X 0 Y).trans (congrArg (X + ·) (Nat.zero_add Y)))
      = ZX.nWire (X + Y) := rfl
  rw [hcast] at hL3
  exact hL3.trans hR.symm

instance : MonoidalCategory ZXCat :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ =>
      Quotient.sound (ZX.nWire_stack X₁ X₂))
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      Quotient.inductionOn₂ f₁ g₁ fun a c =>
        Quotient.inductionOn₂ f₂ g₂ fun b d =>
          Quotient.sound (ZX.compose_stack_interchange a c b d))
    (associator_naturality := fun f₁ f₂ f₃ =>
      Quotient.inductionOn₃ f₁ f₂ f₃ fun a b c =>
        Quotient.sound (ZX.stack_assoc_naturality a b c))
    (leftUnitor_naturality := fun f =>
      Quotient.inductionOn f fun a => Quotient.sound (ZX.empty_stack_naturality a))
    (rightUnitor_naturality := fun f =>
      Quotient.inductionOn f fun a => Quotient.sound (ZX.stack_empty_naturality a))
    (pentagon := fun W X Y Z => Quotient.sound (ZX.pentagon_zx W X Y Z))
    (triangle := fun X Y => Quotient.sound (ZX.triangle_zx X Y))

end SpLean.Algebraic
