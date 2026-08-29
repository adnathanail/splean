import SemanticsTesting.Utils

open SpLean.Algebraic

abbrev twoQubitidentityMatrix : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
abbrev twoWiresStacked : ZX 2 2 := .wire ⊗ .wire
#zx twoWiresStacked
theorem two_wire_stack_sem : twoWiresStacked.sem = twoQubitidentityMatrix := by
  -- Unfold definitions
  unfold wiresMat4 twoQubitidentityMatrix
  -- Introduce variables for indexes of matrices
  apply funext; intro f
  apply funext; intro g
  -- Split the boundary between the two wires: `f 0`/`g 0` go to the left copy
  --   (via `Fin.castAdd`), `f 1`/`g 1` to the right (via `Fin.natAdd`)
  rw [ZX.sem]
  -- Show the wires are identity
  rw [show ZX.wire.sem = fun x y => if x 0 = y 0 then 1 else 0 from rfl]
  -- Split on the sixteen entries of the 4x4 matrix
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hg0 : g 0 <;> cases hg1 : g 1 <;>
    simp [hf0, hf1, hg0, hg1]

def gateCnotZFirst : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) ≫ (.wire ⊗ .spider .X 2 1)
#zx gateCnotZFirst

def gateCnotXFirst : ZX 2 2 := (.wire ⊗ .spider .X 1 2) ≫ (.spider .Z 2 1 ⊗ .wire)
#zx gateCnotXFirst

theorem cnot_sem_agnostic :
    gateCnotZFirst.sem = gateCnotXFirst.sem := by
  unfold gateCnotZFirst gateCnotXFirst
  apply funext; intro f
  apply funext; intro g
  simp only [ZX.sem]
  rw [sum_wires3, sum_wires3]
  simp only [zSpiderSem, xSpiderSem, hadSem, sum_wires1, sum_wires2, Fin.prod_univ_two, AlgPhase.expI_zero]
  simp only [Fintype.univ_bool, Fin.forall_fin_one, Fin.isValue, Fin.reduceCastAdd,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_ite, mul_one, mul_zero,
    Fin.natAdd_eq_addNat, Fin.addNat_one, Fin.succ_zero_eq_one, Fin.reduceNatAdd, Matrix.cons_val,
    Bool.and_eq_true, Matrix.cons_val_fin_one, mul_neg, ite_mul, neg_mul, implies_true, and_true,
    Bool.false_eq_true, forall_const, and_false, ↓reduceIte, add_zero, Finset.univ_unique,
    Fin.default_eq_zero, Bool.false_and, Finset.prod_inv_distrib, Finset.prod_const,
    Finset.card_singleton, pow_one, zero_mul, Bool.true_eq_false, zero_add, Bool.true_and,
    Finset.prod_singleton, Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, neg_zero, ite_self, one_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_insert, Bool.eq_true_or_eq_false_self, Finset.sum_const_zero, neg_neg,
    Finset.sum_ite_eq', Bool.and_false, true_and, false_and, Bool.and_true, Finset.sum_neg_distrib]
  ring_nf
  cases f 0 <;> cases f 1 <;> cases g 0 <;> cases g 1 <;>
    norm_num
