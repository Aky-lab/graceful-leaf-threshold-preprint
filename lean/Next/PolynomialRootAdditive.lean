import Next.PolynomialRoot

/-! The exact division remainder pays for a single grid block, not a
factor-two loss of the entire packing capacity. -/
namespace FixedCore.PolynomialRoot
open scoped BigOperators

/-- The largest grid-compatible dilation spends at most the edge budget
and retains the requested product capacity after division. -/
theorem floor_additive_scale_bounds {N M b R A : ℕ} (hM : 0<M) (hb : 0<b)
    (hN : b*M+R*A≤N) :
    0 < b*(N/(b*M)) ∧ b*(N/(b*M))*M≤N ∧ R*A≤b*(N/(b*M))*M := by
  have hm : 0<b*M := Nat.mul_pos hb hM
  have hq : 1≤N/(b*M) := (Nat.le_div_iff_mul_le hm).mpr (by omega)
  have hr := Nat.mod_lt N hm
  have hsum : N % (b*M) + (b*(N/(b*M)))*M = N := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mod_add_div N (b*M)
  exact ⟨Nat.mul_pos hb (by omega),by omega,by omega⟩

/-- For a fixed seed and packing quantity, the additive threshold is
never larger than the old maximum of the two doubled thresholds. -/
theorem floor_additive_budget_le_old (b M R A : ℕ) :
    b*M+R*A≤max (2*b*M) (2*R*A) := by
  rw [Nat.mul_assoc 2 b M,Nat.mul_assoc 2 R A]
  omega

/-- One additive edge budget supplies the original greedy capacity at
every positive rank whose ratio to the maximum is bounded by `R`. -/
theorem floor_additive_scaled_capacity {N M b R k L a t : ℕ}
    (hM : 0<M) (hb : 0<b) (hR : 0<R)
    (hrank : M≤R*a) (hbudget : b*M+R*(2*k+3*L+3)≤N) (ht : 2*t≤L) :
    t+k+L≤(b*(N/(b*M))*a-1)/2 := by
  have hl := (floor_additive_scale_bounds hM hb hbudget).2.2
  have hmul := Nat.mul_le_mul_left (b*(N/(b*M))) hrank
  have hlarge : 2*k+3*L+3≤b*(N/(b*M))*a := by
    have hc : R*(2*k+3*L+3) ≤ R*(b*(N/(b*M))*a) := by
      calc
        _ ≤ b*(N/(b*M))*M := hl
        _ ≤ b*(N/(b*M))*(R*a) := hmul
        _ = _ := by ring
    exact (Nat.le_of_mul_le_mul_left hc hR)
  omega

#print axioms floor_additive_scale_bounds
#print axioms floor_additive_scaled_capacity
end FixedCore.PolynomialRoot
