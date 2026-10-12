import SemanticsTesting.Utils

open SpLean.Algebraic

/-! ### Generators -/

/--
info: Hyp 0 0 with 0 wires
  edges:   []
  ids:     []
  inputs:  []
  outputs: []
-/
#guard_msgs in
#eval (ZX.empty).toHyp

/--
info: Hyp 1 1 with 1 wires
  edges:   []
  ids:     []
  inputs:  [0]
  outputs: [0]
-/
#guard_msgs in
#eval (ZX.wire).toHyp

/--
info: Hyp 1 1 with 2 wires
  edges:   [H [0, 1]]
  ids:     []
  inputs:  [0]
  outputs: [1]
-/
#guard_msgs in
#eval (ZX.hadamard).toHyp

/--
info: Hyp 1 2 with 3 wires
  edges:   [Z(π/2) [0, 1, 2]]
  ids:     []
  inputs:  [0]
  outputs: [1, 2]
-/
#guard_msgs in
#eval (ZX.spider .Z 1 2 (π/2)).toHyp

/--
info: Hyp 0 3 with 3 wires
  edges:   [X(π) [0, 1, 2]]
  ids:     []
  inputs:  []
  outputs: [0, 1, 2]
-/
#guard_msgs in
#eval (ZX.spider .X 0 3 π).toHyp

/--
info: Hyp 2 2 with 2 wires
  edges:   []
  ids:     []
  inputs:  [0, 1]
  outputs: [1, 0]
-/
#guard_msgs in
#eval (ZX.swap).toHyp

/-! ### Stacking

Disjoint union
Second diagram's wires are numbered after the first's -/

/--
info: Hyp 2 2 with 4 wires
  edges:   [Z(0) [0, 1], H [2, 3]]
  ids:     []
  inputs:  [0, 2]
  outputs: [1, 3]
-/
#guard_msgs in
#eval (ZX.spider .Z 1 1 ⊗ ZX.hadamard).toHyp

/--
info: Hyp 3 3 with 3 wires
  edges:   []
  ids:     []
  inputs:  [0, 1, 2]
  outputs: [0, 1, 2]
-/
#guard_msgs in
#eval (ZX.wire ⊗ ZX.wire ⊗ ZX.wire).toHyp

/-! ### Composition

Disjoint union
Each output wire of the first diagram is recorded as identified with the
  matching input wire of the second -/

/--
info: Hyp 2 2 with 8 wires
  edges:   [Z(0) [0, 1, 2], X(0) [5, 6, 7]]
  ids:     [(1, 4), (2, 5), (3, 6)]
  inputs:  [0, 3]
  outputs: [4, 7]
-/
#guard_msgs in
#eval Gate.CNOT.toHyp

/--
info: Hyp 2 2 with 12 wires
  edges:   [Z(0) [0, 1, 2], H [5, 6], Z(0) [9, 10, 11]]
  ids:     [(1, 4), (2, 5), (3, 7), (4, 8), (6, 9), (7, 10)]
  inputs:  [0, 3]
  outputs: [8, 11]
-/
#guard_msgs in
#eval Gate.CZ.toHyp
