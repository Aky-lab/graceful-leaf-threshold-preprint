import Next.BoundedDepthAvoidance

namespace FixedCore.Next

/-- An explicit exponent window for a depth-`t` seed with initial height `M`. -/
def boundedDepthExponent (t M : ℕ) : ℕ := M * 3^t + 1

/-- The integral choice threshold, uniform over at most `K` assigned ranks. -/
def boundedDepthTrialBudget (K t M : ℕ) : ℕ :=
  24 * ((2*K+1)*(2*boundedDepthExponent t M+1)+2)

/-- The root scale compensates for a factor of three at every depth. -/
def boundedDepthBase (K t M : ℕ) : ℕ := 3^t * boundedDepthTrialBudget K t M

/-- A computable coefficient depending only on depth and initial height. -/
def boundedDepthCoefficient (t M : ℕ) : ℕ :=
  72 * 2^t * 3^t * M * (2*boundedDepthExponent t M+3)

/-- The common rank lower bound at depth `d`. -/
def boundedDepthScale (K t M d : ℕ) : ℚ :=
  (boundedDepthBase K t M : ℚ) / (3 : ℚ)^d

theorem boundedDepthExponent_bound (t M : ℕ) :
    M*3^t ≤ 2^(boundedDepthExponent t M) := by
  exact (Nat.le_succ (M*3^t)).trans (Nat.lt_two_pow_self.le)

theorem boundedDepthExponent_bound_rat (t M : ℕ) :
    (M : ℚ)*(3 : ℚ)^t ≤ (2 : ℚ)^(boundedDepthExponent t M) := by
  exact_mod_cast boundedDepthExponent_bound t M

theorem boundedDepthTrialBudget_pos (K t M : ℕ) :
    0 < boundedDepthTrialBudget K t M := by
  unfold boundedDepthTrialBudget
  positivity

theorem boundedDepthBase_pos (K t M : ℕ) : 0 < boundedDepthBase K t M := by
  unfold boundedDepthBase
  exact Nat.mul_pos (by positivity) (boundedDepthTrialBudget_pos K t M)

theorem boundedDepthScale_pos (K t M d : ℕ) : 0 < boundedDepthScale K t M d := by
  unfold boundedDepthScale
  exact div_pos (by exact_mod_cast boundedDepthBase_pos K t M) (by positivity)

@[simp] theorem boundedDepthScale_zero (K t M : ℕ) :
    boundedDepthScale K t M 0 = boundedDepthBase K t M := by
  simp [boundedDepthScale]

@[simp] theorem boundedDepthScale_total (K t M : ℕ) :
    boundedDepthScale K t M t = boundedDepthTrialBudget K t M := by
  simp [boundedDepthScale, boundedDepthBase, Nat.cast_mul, Nat.cast_pow]

/-- Every shallower level retains at least the final trial scale. -/
theorem boundedDepthScale_antitone (K t M : ℕ) {d e : ℕ} (hde : d ≤ e) :
    boundedDepthScale K t M e ≤ boundedDepthScale K t M d := by
  unfold boundedDepthScale
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 3) hde)

theorem boundedDepthScale_total_le (K t M : ℕ) {d : ℕ} (hdt : d ≤ t) :
    (boundedDepthTrialBudget K t M : ℚ) ≤ boundedDepthScale K t M d := by
  simpa using boundedDepthScale_antitone K t M hdt

/-- One graph level spends exactly a factor of three in the lower scale. -/
theorem boundedDepthScale_step (K t M d : ℕ) :
    boundedDepthScale K t M d / 3 = boundedDepthScale K t M (d+1) := by
  simp only [boundedDepthScale, pow_succ, div_div]

/-- At a nonzero final depth, the common lower bound fits below one third of
the root scale. -/
theorem boundedDepthScale_root_third (K t M : ℕ) (ht : 1 ≤ t) :
    boundedDepthScale K t M t ≤ (boundedDepthBase K t M : ℚ)/3 := by
  simpa [boundedDepthScale] using boundedDepthScale_antitone K t M ht

/-- The top seed rank and the final lower scale lie within the chosen dyadic
exponent window. -/
theorem boundedDepth_range_width (K t M : ℕ) :
    (boundedDepthBase K t M : ℚ)*M ≤
      (2 : ℚ)^(boundedDepthExponent t M) * boundedDepthScale K t M t := by
  unfold boundedDepthScale
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 3^t)).mpr
  have h := mul_le_mul_of_nonneg_left (boundedDepthExponent_bound_rat t M)
    (show (0 : ℚ) ≤ boundedDepthBase K t M by positivity)
  nlinarith

/-- The choice threshold is linear in the size budget. -/
theorem boundedDepthTrialBudget_linear (K t M : ℕ) :
    boundedDepthTrialBudget K t M ≤
      72 * (K+1) * (2*boundedDepthExponent t M+3) := by
  unfold boundedDepthTrialBudget
  nlinarith

/-- Clearing at most `t` forced halvings leaves a natural rank bound linear
in the graph-size budget, with a fully explicit computable coefficient. -/
theorem boundedDepth_final_bound (K t M : ℕ) :
    2^t * boundedDepthBase K t M * M ≤ boundedDepthCoefficient t M * (K+1) := by
  calc
    _ = (2^t*3^t*M)*boundedDepthTrialBudget K t M := by
      unfold boundedDepthBase
      ring
    _ ≤ (2^t*3^t*M)*(72*(K+1)*(2*boundedDepthExponent t M+3)) :=
      Nat.mul_le_mul_left _ (boundedDepthTrialBudget_linear K t M)
    _ = _ := by
      unfold boundedDepthCoefficient
      ring

#print axioms boundedDepthExponent_bound
#print axioms boundedDepthScale_total
#print axioms boundedDepth_range_width
#print axioms boundedDepth_final_bound

end FixedCore.Next
