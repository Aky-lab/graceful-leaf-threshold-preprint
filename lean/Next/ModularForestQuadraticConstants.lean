import Next.ModularForestConstants

namespace FixedCore.ModularForest

/-- Quadratic width for steering ℓ actual marked vertices with packet-aware requests. -/
def quadratic_steeringWidth (s ℓ : ℕ) : ℕ := 16*(ℓ+1)^2*(exclusionBudget s+2)

theorem quadratic_steeringWidth_pos (s ℓ : ℕ) : 0<quadratic_steeringWidth s ℓ := by unfold quadratic_steeringWidth; positivity

theorem quadratic_steeringWidth_mono {s ℓ ℓ' : ℕ} (h : ℓ≤ℓ') : quadratic_steeringWidth s ℓ≤quadratic_steeringWidth s ℓ' := by
  unfold quadratic_steeringWidth
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2))

theorem quadratic_steering_trial_capacity (s ℓ a E : ℕ) (ha : a≤s)
    (hE : 2^E≤4*ℓ^2) : 2^E*(2000*(a+3)+2)≤quadratic_steeringWidth s ℓ := by
  have hp : ℓ^2≤(ℓ+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hb : 2000*(a+3)+2≤exclusionBudget s+2 := by unfold exclusionBudget; omega
  calc
    2^E*(2000*(a+3)+2)≤(4*ℓ^2)*(exclusionBudget s+2) := Nat.mul_le_mul hE hb
    _ ≤ 16*(ℓ+1)^2*(exclusionBudget s+2) := Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left 4 hp).trans (Nat.mul_le_mul_right _ (by decide : 4≤16)))
    _ = quadratic_steeringWidth s ℓ := rfl

theorem quadratic_modulus_budget {q s ℓ : ℕ}
    (hq : 8*quadratic_steeringWidth s ℓ+2*exclusionBudget s<q) : exclusionBudget s≤q := by omega

theorem quadratic_width_lt_modulus {q s ℓ : ℕ}
    (hq : 8*quadratic_steeringWidth s ℓ+2*exclusionBudget s<q) : quadratic_steeringWidth s ℓ<q := by omega

theorem quadratic_centered_of_width {q s ℓ : ℕ}
    (hq : 8*quadratic_steeringWidth s ℓ+2*exclusionBudget s<q) {z : ℤ}
    (hz : |z|≤2*(quadratic_steeringWidth s ℓ:ℤ)) :
    z.natAbs≤2*quadratic_steeringWidth s ℓ ∧ 2*z.natAbs<q := by
  have hn : z.natAbs≤2*quadratic_steeringWidth s ℓ := by
    exact_mod_cast (show (z.natAbs:ℤ)≤2*(quadratic_steeringWidth s ℓ:ℤ) by simpa using hz)
  exact ⟨hn,by omega⟩

#print axioms quadratic_steering_trial_capacity
end FixedCore.ModularForest
