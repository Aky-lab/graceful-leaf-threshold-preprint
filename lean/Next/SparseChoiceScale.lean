import Next.PolynomialDyadicChoices
import Mathlib.Data.Nat.Log

namespace FixedCore.Next

/-- Global multiplier window sized to the rational rank ratio (200s^3). -/
def sparseWindow (s : ℕ) : ℕ := 8+3*Nat.clog 2 s

/-- Integral choice scale for logarithmically many dyadic exponents. -/
def sparseChoiceScale (s : ℕ) : ℕ := 512*s*(sparseWindow s+1)

theorem sparseChoiceScale_pos {s : ℕ} (hs : 0 < s) :
    0 < sparseChoiceScale s := by
  unfold sparseChoiceScale
  positivity

theorem sparse_dyadic_width (s : ℕ) :
    200*s^3 ≤ 2^(sparseWindow s) := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (b := 2) (by decide) s) 3
  calc
    _ ≤ 256*(2^Nat.clog 2 s)^3 :=
      (Nat.mul_le_mul_left 200 h).trans (Nat.mul_le_mul_right _ (by decide))
    _ = _ := by rw [sparseWindow,pow_add,Nat.mul_comm 3,pow_mul]; rfl

theorem sparseChoiceScale_width {s : ℕ} :
    2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3 ≤
      (2 : ℚ)^(sparseWindow s)*((sparseChoiceScale s : ℚ)/100) := by
  have hw : 200*(s : ℚ)^3 ≤ (2 : ℚ)^(sparseWindow s) := by
    exact_mod_cast sparse_dyadic_width s
  have hD : (0 : ℚ) ≤ sparseChoiceScale s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hw hD]

theorem sparse_pair_threshold (s : ℕ) (hs : 0 < s) :
    ((60*((2*s+1)*(2*sparseWindow s+1)+2) : ℕ) : ℚ) ≤ sparseChoiceScale s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  have hj : (0 : ℚ) ≤ sparseWindow s := by positivity
  unfold sparseChoiceScale
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (s : ℚ)-1 by linarith) hj]

theorem sparse_root_threshold (s : ℕ) :
    s*(2*sparseWindow s+1) ≤ sparseChoiceScale s := by
  unfold sparseChoiceScale
  nlinarith

#print axioms sparseChoiceScale_width
#print axioms sparse_pair_threshold
#print axioms sparse_root_threshold
end FixedCore.Next
