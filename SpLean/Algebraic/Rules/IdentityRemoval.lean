import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Panel

show_panel_widgets [local SpLean.ZXPanel]


namespace SpLean.Algebraic

theorem identity_removal_Z :
    .spider .Z 1 1 ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem]
  simp only [Fin.forall_fin_one]
  cases f 0 <;> cases h 0 <;> norm_num

theorem identity_removal_Z_mod_two_pi {φ : AlgPhase} (h : AlgPhase.equiv φ 0) :
    ZX.spider .Z 1 1 φ ≈zx ZX.wire :=
  (ZX.Equiv.spider_congr _ _ _ h).trans identity_removal_Z
