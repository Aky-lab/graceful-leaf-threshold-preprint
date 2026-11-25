import Mathlib.Tactic

namespace FixedCore.ModularForest

/-- Absolute finite-exclusion budget from the three-seed packet lemma. -/
def exclusionBudget (s : ℕ) : ℕ := 2000*(s+3)

/-- The manuscript's explicit width for steering ℓ actual marked vertices. -/
def steeringWidth (s ℓ : ℕ) : ℕ := 16*(ℓ+1)^3*(exclusionBudget s+2)

theorem exclusionBudget_pos (s : ℕ) : 0<exclusionBudget s := by unfold exclusionBudget; positivity
theorem steeringWidth_pos (s ℓ : ℕ) : 0<steeringWidth s ℓ := by unfold steeringWidth; positivity

theorem steeringWidth_mono {s ℓ ℓ' : ℕ} (h : ℓ≤ℓ') : steeringWidth s ℓ≤steeringWidth s ℓ' := by
  unfold steeringWidth
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3))

theorem steering_trial_capacity (s ℓ a E : ℕ) (ha : a≤s)
    (hE : 2^E≤4*ℓ^3) : 2^E*(2000*(a+3)+2)≤steeringWidth s ℓ := by
  have hp : ℓ^3≤(ℓ+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hb : 2000*(a+3)+2≤exclusionBudget s+2 := by unfold exclusionBudget; omega
  calc
    2^E*(2000*(a+3)+2)≤(4*ℓ^3)*(exclusionBudget s+2) := Nat.mul_le_mul hE hb
    _ ≤ 16*(ℓ+1)^3*(exclusionBudget s+2) := Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left 4 hp).trans (Nat.mul_le_mul_right _ (by decide : 4≤16)))
    _ = steeringWidth s ℓ := rfl

theorem modulus_budget {q s ℓ : ℕ}
    (hq : 8*steeringWidth s ℓ+2*exclusionBudget s<q) : exclusionBudget s≤q := by omega

theorem width_lt_modulus {q s ℓ : ℕ}
    (hq : 8*steeringWidth s ℓ+2*exclusionBudget s<q) : steeringWidth s ℓ<q := by omega

theorem centered_of_width {q s ℓ : ℕ}
    (hq : 8*steeringWidth s ℓ+2*exclusionBudget s<q) {z : ℤ}
    (hz : |z|≤2*(steeringWidth s ℓ:ℤ)) :
    z.natAbs≤2*steeringWidth s ℓ ∧ 2*z.natAbs<q := by
  have hn : z.natAbs≤2*steeringWidth s ℓ := by
    exact_mod_cast (show (z.natAbs:ℤ)≤2*(steeringWidth s ℓ:ℤ) by simpa using hz)
  exact ⟨hn,by omega⟩

#print axioms steering_trial_capacity
end FixedCore.ModularForest
