import SpLean.Algebraic.Semantics
import SpLean.Algebraic.Equiv

open SpLean.Algebraic

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
