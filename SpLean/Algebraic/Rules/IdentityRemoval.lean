import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Rules.SpiderFusion
import SpLean.Algebraic.Tactics

namespace SpLean.Algebraic

theorem identity_removal_Z_zero :
    .spider .Z 1 1 ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem]
  simp only [Fin.forall_fin_one]
  cases f 0 <;> cases h 0 <;> norm_num

theorem identity_removal_Z {φ : AlgPhase} (h : AlgPhase.equiv φ 0) :
    ZX.spider .Z 1 1 φ ≈zx ZX.wire :=
  (ZX.Equiv.spider_congr _ _ _ h).trans identity_removal_Z_zero

theorem identity_removal_Z_two_pi :
    ZX.spider .Z 1 1 (2π) ≈zx ZX.wire := by
  zx_rw [identity_removal_Z]
  simp [AlgPhase.equiv]

theorem identity_removal_X_zero :
    .spider .X 1 1 ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem, zSpiderSem, hadSem]
  simp only [sum_wires1, Finset.univ_unique, Finset.prod_singleton]
  cases f 0 <;> cases h 0 <;> norm_num [inv_root_two_mul_self_complex]

theorem identity_removal_X {φ : AlgPhase} (h : AlgPhase.equiv φ 0) :
    ZX.spider .X 1 1 φ ≈zx ZX.wire :=
  (ZX.Equiv.spider_congr _ _ _ h).trans identity_removal_X_zero

theorem identity_removal_X_two_pi :
    ZX.spider .X 1 1 (2π) ≈zx ZX.wire := by
  zx_rw [identity_removal_X]
  simp [AlgPhase.equiv]

/-- Two π-phase Z spiders on a wire cancel. -/
theorem pi_pi_Z :
    (ZX.spider .Z 1 1 π ≫ ZX.spider .Z 1 1 π) ≈zx ZX.wire := by
  zx_rw [spider_fusion_Z]
  zx_normalize
  zx_rw [identity_removal_Z_two_pi]

/-- Two π-phase X spiders on a wire cancel. -/
theorem pi_pi_X :
    (ZX.spider .X 1 1 π ≫ ZX.spider .X 1 1 π) ≈zx ZX.wire := by
  zx_rw [spider_fusion_X]
  zx_normalize
  zx_rw [identity_removal_X_two_pi]

-- TODO id_simp tactic
