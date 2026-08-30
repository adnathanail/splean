import SpLean.Algebraic.ZX
import SpLean.Algebraic.Semantics

/-!
# Derived diagram constructions

`n`-ary forms of rules need to be able to represent:
- *`k` copies of
  - 1 to 1 diagrams
  - parallel wires
  - a Hadamard on every wire
  - 0 to 1 diagrams (states)
- cups
- caps

Recursions arranged so their arity index reduces *definitionally*:
`ZX.nStack (k+1) a` is `nStack k a ⊗ a`, of type `ZX (k+1) (k+1)`,
  because `Nat.add` recurses on its second argument.
-/

namespace SpLean.Algebraic

/-- `k` parallel copies of a one-in-one-out diagram, stacked. -/
def ZX.nStack : (k : ℕ) → ZX 1 1 → ZX k k
  | 0, _ => .empty
  | k + 1, a => nStack k a ⊗ a

/-- `k` parallel wires — the identity diagram on `k` wires. -/
abbrev ZX.nWire (k : ℕ) : ZX k k := ZX.nStack k .wire

/-- A Hadamard on each of `k` wires. -/
abbrev ZX.nHadamard (k : ℕ) : ZX k k := ZX.nStack k .hadamard

theorem n_hadamard_sem (k : ℕ) (u v : Wires k) :
    (ZX.nHadamard k).sem u v = ∏ i, hadSem (u i) (v i) := by
  induction k with
  | zero =>
    simp only [ZX.nHadamard, ZX.nStack, ZX.sem]
    norm_num
  | succ k ih =>
    simp only [ZX.nHadamard, ZX.nStack, ZX.sem]
    rw [ih]
    exact Eq.symm (Fin.prod_univ_castSucc fun i => hadSem (u i) (v i))

/-- `k` parallel copies of a state, stacked. The state version of `nStack`:
`ZX 0 1` rather than `ZX 1 1`, so the result is a `ZX 0 k`. -/
def ZX.nStackState : (k : ℕ) → ZX 0 1 → ZX 0 k
  | 0, _ => .empty
  | k + 1, a => nStackState k a ⊗ a

/-- The cup: a phase-free Z spider with no inputs and two outputs. -/
abbrev ZX.cup : ZX 0 2 := .spider .Z 0 2

/-- The cap: a phase-free Z spider with two inputs and no outputs. -/
abbrev ZX.cap : ZX 2 0 := .spider .Z 2 0

end SpLean.Algebraic
