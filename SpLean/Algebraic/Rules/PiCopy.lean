import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Rules.Structural

/-!
# π-commutation ("π-copy")

An X spider with phase π pushed through a Z spider negates the Z spider's phase
and comes out copied onto every one of its output legs.

`ZX.nStack m (ZX.spider .X 1 1 π)` is
  "a π spider on each of the `m` outputs".
-/

namespace SpLean.Algebraic

/-- A π-phase X spider commutes through a Z spider, negating its phase and
copying itself onto every output leg. -/
theorem pi_copy_Z (m : ℕ) (α : AlgPhase) :
    (ZX.spider .X 1 1 π ≫ ZX.spider .Z 1 m α)
      ≈zx (ZX.spider .Z 1 m (-α) ≫ ZX.nStack m (ZX.spider .X 1 1 π)) := by
  -- Introduce correct constant factor
  refine ⟨α.expI, AlgPhase.expI_ne_zero α, fun f g => ?_⟩
  -- Simplify a bit
  rw [ZX.sem, ZX.sem, sum_wires1]
  simp only [x_gate_sem, nStack_pi_sem]
  simp only [ZX.sem, zSpiderSem, Fin.forall_fin_one, AlgPhase.expI_neg, ite_mul]
  cases hf : f 0
  · -- f = |0⟩: only the all-true branch survives
    norm_num
    rw [sum_bool_all_false]
    split
    ·
      rename_i hg -- ∀ j, g j = true
      simp only [hg]
      rw [x_gate_xSpiderSem_entries]
      norm_num
    ·
      rename_i hg -- ¬(∀ j, g j) = true
      -- Flip not forall equals, to exists not equals
      push_neg at hg
      -- Get specific wire which isn't true
      obtain ⟨j, hj⟩ := hg
      -- Show that if that wire is false, then we are accessing the top left element
      --   of the X gate, which is 0
      have hjz :
        xSpiderSem π (fun j => false : Wires 1) (fun _ => g j : Wires 1) = 0 := by
        simp only [hj, x_gate_xSpiderSem_entries, ↓reduceIte]
      -- If anything in a product is 0, the whole thing is zero
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hjz, mul_zero]
  · -- f = |1⟩: only the all-false branch survives
    norm_num
    rw [sum_bool_all_true]
    norm_num
    split
    · rename_i hg
      simp only [hg]
      rw [x_gate_xSpiderSem_entries]
      norm_num
    · rename_i hg
      push_neg at hg
      obtain ⟨j, hj⟩ := hg
      have hjz :
        xSpiderSem π (fun x => true : Wires 1) (fun x_1 => g j : Wires 1) = 0 := by
        simp only [hj, x_gate_xSpiderSem_entries, ↓reduceIte]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hjz]


/-- π-commutation, colours swapped. -/
theorem pi_copy_X (m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z 1 1 π ≫ ZX.spider .X 1 m α)
      ≈zx (ZX.spider .X 1 m (-α) ≫ ZX.nStack m (ZX.spider .Z 1 1 π)) := by
  sorry

end SpLean.Algebraic
