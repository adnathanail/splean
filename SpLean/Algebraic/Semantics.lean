import SpLean.Algebraic.ZX
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Denotational semantics for algebraic ZX terms

A `ZX n m` term denotes a tensor: a complex amplitude for every assignment of
Booleans to its `n` input wires and `m` output wires,
`⟦d⟧ : (Fin n → Bool) → (Fin m → Bool) → ℂ`.

This "matrix as a function of boundary bit-vectors" presentation is chosen over
`Matrix (Fin (2^m)) (Fin (2^n)) ℂ` deliberately: `stack` splits a boundary
assignment with `Fin.castAdd`/`Fin.natAdd` instead of reindexing along
`2^(n+p) = 2^n * 2^p`, so no power-of-two casts ever appear. It is also the
tensor-network view of a diagram, which is the right vocabulary for the planned
hypergraph-isomorphism work: permuting wires is reindexing a sum, i.e. an
`Equiv`, not a matrix conjugation.
-/

noncomputable section

/-- The angle in radians denoted by a `Phase`, i.e. `num/den · π`. -/
def Phase.angle (p : Phase) : ℝ :=
  (p.num : ℝ) / ((p.den : ℕ) : ℝ) * Real.pi

namespace SpLean.Algebraic

open Complex (I)

/-- A boundary assignment: one Boolean per open wire. -/
abbrev Wires (n : ℕ) := Fin n → Bool

/-- Tensor of a Z spider: `1` on the all-`false` boundary, `e^{iα}` on the
all-`true` boundary, `0` elsewhere. When `n = m = 0` both indicators fire and
the scalar is `1 + e^{iα}`, as it should be. -/
def zSpiderSem (α : ℝ) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  (if (∀ i, f i = false) ∧ (∀ j, g j = false) then 1 else 0)
    + Complex.exp (α * I) *
        (if (∀ i, f i = true) ∧ (∀ j, g j = true) then 1 else 0)

/-- One matrix entry of the Hadamard gate. -/
def hadSem (a b : Bool) : ℂ :=
  if a && b then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Tensor of an X spider: a Z spider conjugated by Hadamards on every wire. -/
def xSpiderSem (α : ℝ) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  ∑ f' : Wires n, ∑ g' : Wires m,
    (∏ i, hadSem (f i) (f' i)) * zSpiderSem α f' g' * (∏ j, hadSem (g' j) (g j))

/-- Denotation of an algebraic ZX term as a boundary tensor. -/
def ZX.sem : {n m : ℕ} → ZX n m → Wires n → Wires m → ℂ
  | _, _, .empty, _, _ => 1
  | _, _, .wire, f, g => 0
  | _, _, .hadamard, f, g => hadSem (f 0) (g 0)
  | _, _, .spider .Z _ _ φ, f, g => zSpiderSem φ.angle f g
  | _, _, .spider .X _ _ φ, f, g => xSpiderSem φ.angle f g
  | _, _, .stack a b, f, g => 0
  | _, _, .compose a b, f, h => 0

end SpLean.Algebraic
