import SpLean.Algebraic.ZX
import SpLean.Panel
import SpLean.Algebraic.Visualize
-- import SpLean.Algebraic.Semantics

open SpLean.Algebraic

def GateCNOT : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) × (.wire ⊗ .spider .X 2 1)
#zx GateCNOT

-- TODO
-- def GateCNOT2 : ZX 2 2 := (.wire ⊗ .spider .X 1 2) × (.spider .Z 2 1 ⊗ .wire)
-- #zx GateCNOT2

-- -- WIP: needs real `stack`/`X-spider` semantics first; see Algebraic/CLAUDE.md.
-- theorem x : GateCNOT ≃ZX GateCNOT2 := by
--   show _ = _
--   unfold ZX.sem
--   sorry


def GateNOTC : ZX 2 2 := (.spider .X 1 2 ⊗ .wire) × (.wire ⊗ .spider .Z 2 1)
#zx GateNOTC

def GateCX : ZX 2 2 :=
  (
    (.spider .Z 1 2 ⊗ .wire) ×
    (.wire ⊗ .hadamard ⊗ .wire)
  ) ×
  (.wire ⊗ .spider .Z 2 1)
#zx GateCX
