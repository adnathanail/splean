import SpLean.Algebraic.Equiv

/-!
# Casting a diagram between equal arities

`a ⊗ .empty` has type `ZX (n + 0) (m + 0)`, which is reduced automatically to `ZX n m`
This reduction only takes place between variables and explicit values on the RHS so
  `.empty ⊗ a` has type `ZX (0 + n) (0 + m)`, and it can't be automatically reduced

So sometimes we need to be able to manually cast a ZX diagram, e.g. to even state
  the `empty_stack` lemma, as `(.empty ⊗ a) ≈zx a` gives
    Application type mismatch:
      The argument `a` has type `ZX n m`
      but is expected to have type `ZX (0 + n) (0 + m)`
      in the application `ZX.empty ⊗ a ≈zx a`

We then also give `zx_rw` a congruence lemma to allow it to work through casts
-/

namespace SpLean.Algebraic

/-- Cast a diagram along equalities of its input and output arities. -/
def ZX.cast {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m) : ZX n' m' :=
  hn ▸ hm ▸ a

/-- A cast with the same arities on both sides does nothing. -/
@[simp] theorem ZX.cast_self {n m : ℕ} (hn : n = n) (hm : m = m) (a : ZX n m) :
    ZX.cast hn hm a = a := rfl

/-- Two casts in a row are one cast. -/
@[simp] theorem ZX.cast_cast {n m n' m' n'' m'' : ℕ}
    (hn : n = n') (hm : m = m') (hn' : n' = n'') (hm' : m' = m'') (a : ZX n m) :
    ZX.cast hn' hm' (ZX.cast hn hm a) = ZX.cast (hn.trans hn') (hm.trans hm') a := by
  subst hn; subst hm; subst hn'; subst hm'; rfl

/-- Casting back with the symmetric proofs undoes a cast. -/
@[simp] theorem ZX.cast_symm_cast {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m) :
    ZX.cast hn.symm hm.symm (ZX.cast hn hm a) = a := by
  subst hn; subst hm; rfl

/-- Casting doesn't change denotation. -/
@[simp] theorem ZX.sem_cast {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m)
    (f : Wires n') (g : Wires m') :
    (ZX.cast hn hm a).sem f g = a.sem (fun i => f (Fin.cast hn i)) (fun j => g (Fin.cast hm j)) := by
  subst hn; subst hm; rfl

/-! ### Pushing casts through the constructors

When both arities are built the same way, a cast on the whole diagram
  splits into casts on its parts.
So a cast introduced at the top of a diagram can be moved down to where it cancels. -/

theorem ZX.cast_compose {n m k n' k' : ℕ} (hn : n = n') (hk : k = k')
    (a : ZX n m) (b : ZX m k) :
    ZX.cast hn hk (a ≫ b) = (ZX.cast hn rfl a ≫ ZX.cast rfl hk b) := by
  subst hn; subst hk; rfl

theorem ZX.cast_stack {n m p q n' m' p' q' : ℕ}
    (hn : n = n') (hm : m = m') (hp : p = p') (hq : q = q')
    (hnp : n + p = n' + p') (hmq : m + q = m' + q') (a : ZX n m) (b : ZX p q) :
    ZX.cast hnp hmq (a ⊗ b) = (ZX.cast hn hm a ⊗ ZX.cast hp hq b) := by
  subst hn; subst hm; subst hp; subst hq; rfl

/-! ### `≈zx` and casts -/

namespace ZX.Equiv

/-- `≈zx` is a congruence for `ZX.cast`
Tagged `@[gcongr]` in `Tactics.lean` so that `zx_rw` can see through a cast. -/
theorem cast_congr {n m n' m' : ℕ} (hn : n = n') (hm : m = m') {a b : ZX n m}
    (h : a ≈zx b) : ZX.cast hn hm a ≈zx ZX.cast hn hm b := by
  subst hn; subst hm; exact h

/-- Move a cast to the other side of an `≈zx`. -/
theorem cast_iff {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m) (b : ZX n' m') :
    (ZX.cast hn hm a ≈zx b) ↔ (a ≈zx ZX.cast hn.symm hm.symm b) := by
  subst hn; subst hm; exact Iff.rfl

end ZX.Equiv

end SpLean.Algebraic
