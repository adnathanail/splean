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
abbrev plusState : ZX 0 1 := .spider .Z 0 1
#zx plusState
theorem z_sem_plus_state (f : Wires 0) : plusState.sem f = (![1, 1] : Fin 2 → ℂ) := by
  unfold wiresVec1
  ext g
  rw [ZX.sem, zSpiderSem]
  cases h : g 0 <;> norm_num [h]

-- ## Minus state
-- (Zπ)- = √2|-⟩ = |0⟩ - |1⟩
--   no input wires so `f : Wires 0`
--   one output `g : Wires 1`
--     |0⟩ has amplitude 1, |1⟩ has amplitude -1
abbrev minusState : ZX 0 1 := .spider .Z 0 1 π
#zx minusState
theorem z_sem_minus_state (f : Wires 0) : minusState.sem f = (![1, -1] : Fin 2 → ℂ) := by
  unfold wiresVec1
  ext g
  rw [ZX.sem, zSpiderSem]
  push_cast
  cases h : g 0 <;> norm_num [h]

/--
  # GHZ states (pqs p83)
-/

-- ## Bell state
abbrev bellState : ZX 0 2 := .spider .Z 0 2
#zx bellState
theorem z_sem_bell_state (f : Wires 0) : bellState.sem f = (![1, 0, 0, 1] : Fin 4 → ℂ) := by
  unfold wiresVec2
  ext g
  rw [ZX.sem, zSpiderSem]
  push_cast
  simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one]
  cases g 0 <;> cases g 1 <;> norm_num

-- ## GHZ state
abbrev ghzState : ZX 0 3 := .spider .Z 0 3
#zx ghzState
theorem z_sem_ghz_state (f : Wires 0) : ghzState.sem f = (![1, 0, 0, 0, 0, 0, 0, 1] : Fin 8 → ℂ) := by
  unfold wiresVec3
  ext g
  rw [ZX.sem, zSpiderSem]
  push_cast
  simp only [Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  cases g 0 <;> cases g 1 <;> cases g 2 <;> norm_num

-- ## Arity-n GHZ state (Leanstral)
abbrev nGhzState (n : ℕ) : ZX 0 n := .spider .Z 0 n
#zx nGhzState 7
theorem z_sem_nGhz_state (f : Wires 0) (n : ℕ) (hn : n ≥ 1) : (nGhzState n).sem f =
    (λ g => if (∀ j : Fin n, g j = false) ∨ (∀ j : Fin n, g j = true) then (1 : ℂ) else 0) := by
  unfold nGhzState
  ext x
  rw [ZX.sem, zSpiderSem]
  simp only [IsEmpty.forall_iff, true_and]
  have hpos : 0 < n := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  by_cases hA : ∀ j : Fin n, x j = false
  · by_cases hB : ∀ j : Fin n, x j = true
    · exfalso
      have h0 : Fin n := ⟨0, hpos⟩
      have h_eq0 := hA h0
      have h_eq1 := hB h0
      rw [h_eq0] at h_eq1
      exact Bool.false_ne_true h_eq1
    · rw [if_pos hA, if_neg hB, if_pos (Or.inl hA)]
      norm_num
  · by_cases hB : ∀ j : Fin n, x j = true
    · rw [if_neg hA, if_pos hB, if_pos (Or.inr hB)]
      norm_num
    · rw [if_neg hA, if_neg hB, if_neg (fun h => h.elim hA hB)]
      norm_num

/--
  # Z-spiders (pqs eq 3.2)
-/
abbrev zIdentity : ZX 1 1 := .spider .Z 1 1
#zx zIdentity
theorem z_sem_z_identity : zIdentity.sem = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, zSpiderSem]
  simp only [Fin.forall_fin_one]
  cases f 0 <;> cases g 0 <;> norm_num

abbrev zGate : ZX 1 1 := .spider .Z 1 1 π
#zx zGate
theorem z_sem_z_gate : zGate.sem = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, zSpiderSem]
  push_cast
  simp only [Fin.forall_fin_one]
  cases f 0 <;> cases g 0 <;> norm_num

abbrev zRotation (α : AlgPhase) : ZX 1 1 := .spider .Z 1 1 α
#zx zRotation (π/4)
theorem z_sem_z_rotation (α : AlgPhase) : (zRotation α).sem = (!![1, 0; 0, Complex.exp (α.angle * Complex.I)] : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold wiresMat2
  apply funext; intro f
  apply funext; intro g
  rw [ZX.sem, zSpiderSem]
  simp only [Fin.forall_fin_one]
  cases f 0 <;> cases g 0 <;> norm_num
