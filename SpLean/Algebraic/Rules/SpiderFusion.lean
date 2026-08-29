import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas

namespace SpLean.Algebraic

theorem zSpider_fusion (n m : ℕ) (α β : AlgPhase) :
    (ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  simp only [sum_wires1, zSpiderSem]
  norm_num
  simp only [ite_and]
  split_ifs <;> ring

theorem xSpider_fusion (n m : ℕ) (α β : AlgPhase) :
    (ZX.spider .X n 1 α ≫ ZX.spider .X 1 m β) ≈zx ZX.spider .X n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  simp only [sum_wires1, xSpiderSem, zSpiderSem, hadSem]
  norm_num
  -- Collapse the LHS sums: the negated branch needs splitting off with
  -- `sum_neg_distrib` before the endpoint lemmas can see it.
  simp only [sum_bool_endpoints, sum_bool_all_false, sum_bool_all_true]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [sum_bool_all_false, sum_bool_all_true]
  -- Collapse the RHS double sum: distribute so each `ite` is the whole summand.
  conv_rhs => simp only [mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  ring_nf
  simp only [sum_bool_endpoints₂]
  -- Both sides now mention the same four Hadamard products, so they never need
  -- expanding: (A+B)(C+D) + (A-B)(C-D) = 2(AC+BD), and the two ½s cancel it.
  rw [inv_root_two_sq_complex]
  ring

end SpLean.Algebraic

-- TODO n version
