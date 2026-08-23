import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  # X-basis states (pqs eq 3.3)
-/

-- TODO track scalar factors
-- ## Plus state
-- (Z0)- = √2|+⟩ = |0⟩ + |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ and |1⟩ both have amplitude 1
abbrev plusState : ZX 0 1 := .spider .Z 0 1 ⟨0, 1⟩
#zx plusState
theorem z_sem_plus_state (f : Wires 0) : plusState.sem f = (![1, 1] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, ZX.sem, zSpiderSem, Phase.angle]
  match h : g 0 with
  | false => norm_num [h]
  | true => norm_num [h]

-- ## Minus state
-- (Zπ)- = √2|-⟩ = |0⟩ - |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ has amplitude 1, |1⟩ has amplitude -1
abbrev minusState : ZX 0 1 := .spider .Z 0 1 ⟨1, 1⟩
#zx minusState
theorem z_sem_minus_state (f : Wires 0) : minusState.sem f = (![1, -1] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, ZX.sem, zSpiderSem, Phase.angle]
  match h : g 0 with
  | false => norm_num [h]
  | true => norm_num [h]

/-! ## Bell state -/

abbrev bellState : ZX 0 2 := .spider .Z 0 2 ⟨0, 1⟩
#zx bellState

theorem z_sem_bell_state (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  ext g
  rw [wiresVec2, ZX.sem, zSpiderSem, Phase.angle]
  match h0 : g 0 with
  | false =>
      match h1 : g 1 with
      | false => simp [h0, h1]
      | true => simp [h0, h1]
  | true =>
      match h1 : g 1 with
      | false => simp [h0, h1]
      | true => simp [h0, h1]
