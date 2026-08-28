import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas

-- TODO different namespace?
namespace SpLean.Algebraic

theorem zSpider_fusion (n m : ℕ) (α β : AlgPhase) :
    (ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires1]
  simp only [zSpiderSem]
  norm_num
  simp only [ite_and, add_mul, Complex.exp_add]
  split_ifs <;> ring
