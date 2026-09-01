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

-- Copied from SemanticsTesting.06Compose.lean
lemma x_gate_ampl (f g : Wires 1) :
    (ZX.spider .X 1 1 π).sem f g = if f 0 = g 0 then 0 else 1 := by
  rw [ZX.sem, xSpiderSem]
  simp only [sum_wires1, zSpiderSem, hadSem]
  cases hf : f 0 <;> cases hg : g 0 <;>
    norm_num [hf, hg, inv_root_two_mul_self_complex]

lemma xSpiderSem_pi_false_true :
    (xSpiderSem π (fun _ => false : Wires 1) (fun _ => true : Wires 1)) = 1 := by
  sorry

lemma xSpiderSem_pi_true_false :
    (xSpiderSem π (fun _ => true : Wires 1) (fun _ => false : Wires 1)) = 1 := by
  sorry

/-- A π-phase X spider commutes through a Z spider, negating its phase and
copying itself onto every output leg. -/
theorem pi_copy_Z (m : ℕ) (α : AlgPhase) :
    (ZX.spider .X 1 1 π ≫ ZX.spider .Z 1 m α)
      ≈zx (ZX.spider .Z 1 m (-α) ≫ ZX.nStack m (ZX.spider .X 1 1 π)) := by
  -- Introduce correct constant factor
  refine ⟨α.expI, AlgPhase.expI_ne_zero α, fun f g => ?_⟩
  -- Open some defs
  rw [ZX.sem, ZX.sem, sum_wires1]
  simp only [x_gate_ampl, nStack_pi_sem]
  simp only [ZX.sem, zSpiderSem, Fin.forall_fin_one, AlgPhase.expI_neg]
  simp
  cases hf : f 0
  · -- f = |0⟩: only the all-true branch survives
    norm_num
    rw [sum_bool_all_false]
    simp
    split
    ·
      rename_i hg
      simp only [hg]
      rw [xSpiderSem_pi_false_true]
      norm_num
    ·
      rename_i hg
      push_neg at hg
      obtain ⟨j, hj⟩ := hg
      have hjz :
        xSpiderSem π (fun j => false : Wires 1) (fun _ => g j : Wires 1) = 0 := by
        simp only [hj]
        sorry
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hjz, mul_zero]
      -- obtain ⟨j, hj⟩ := (red_eq_red_iff _ _).mp h1
  · -- f = |1⟩: only the all-false branch survives
    norm_num
    rw [sum_bool_all_true]
    norm_num
    split
    · rename_i hg
      simp only [hg]
      rw [xSpiderSem_pi_true_false]
      rw [Finset.prod_const_one]
    · rename_i hg
      push_neg at hg
      obtain ⟨j, hj⟩ := hg
      have hjz :
        xSpiderSem π (fun x => true : Wires 1) (fun x_1 => g j : Wires 1) = 0 := by
        sorry
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hjz]


/-- π-commutation, colours swapped. -/
theorem pi_copy_X (m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z 1 1 π ≫ ZX.spider .X 1 m α)
      ≈zx (ZX.spider .X 1 m (-α) ≫ ZX.nStack m (ZX.spider .Z 1 1 π)) := by
  sorry

end SpLean.Algebraic
