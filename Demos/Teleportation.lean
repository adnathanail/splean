import LeanSpider.All

open LeanSpider

show_panel_widgets [local ZXPanel]

-- Quantum teleportation demo:
--   The correction depends on two classical measurement bits, so the proof has to
--   hold for all four combinations of phases a, b ∈ {0, π}
abbrev teleportationStart (a b : Int) : ZXDiagram :=
  ZXDiagram.ofList
    [
      .input 0, .spider .Z ⟨0, 1⟩, .hadamard, .spider .X ⟨a, 1⟩,
      .spider .X ⟨0, 1⟩, .spider .X ⟨b, 1⟩,
      .spider .X ⟨b, 1⟩, .spider .Z ⟨a, 1⟩, .output 0
    ]
    [
      ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩,
      ⟨1, 4⟩, ⟨4, 5⟩,
      ⟨4, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩,
    ]
def teleportationEnd : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .output 0]
    [⟨0, 1⟩]
-- Example of one of the 4 graphs (change the a and b values to see each possible graph)
#zx (teleportationStart 1 1)
#zx teleportationEnd

-- Proof that the diagram reduces to a bare wire for either measurement outcome
--   `cond a 1 0` turns each bit into a phase of π or 0
--   All four cases are discharged by the same sequence of rewrites
theorem doTeleportationSimp : ∀ a b : Bool,
    teleportationStart (cond a 1 0) (cond b 1 0) ≈z teleportationEnd := by
  intro a b
  cases a <;> cases b <;> (
    simp only [teleportationStart, ZXDiagram.ofList, cond]
    zx_cc 3; zx_hh 2 9; zx_sp 1 3
    zx_sp 4 5; zx_sp 4 6; zx_id 4; zx_sp 1 7; zx_id 1
    zx_rfl)
-- Still only depends on the base axioms
#print axioms doTeleportationSimp
