import Next.BoundedDepthInteger

namespace FixedCore.Next.CubicHeavyBounds
open BoundedDepth

/-- The cubic drop is exactly seven units at the limiting half-size charge. -/
theorem cubic_gap {S C J D : ℚ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hJ : 0 ≤ J) (hhalf : 2*J ≤ S) (hsum : C+J ≤ S) :
    7*D*J^3 ≤ D*(S^3-C^3) := by
  let U := S-J
  have hJU : J ≤ U := by dsimp [U]; linarith
  have hCU : C ≤ U := by dsimp [U]; linarith
  have hc3 := pow_le_pow_left₀ hC hCU 3
  have ha := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hJ hJU 2) hJ
  have hb := mul_le_mul_of_nonneg_right hJU (show 0 ≤ J^2 by positivity)
  have hfac : S^3-U^3 = 3*U^2*J+3*U*J^2+J^3 := by
    dsimp [U]
    ring
  have hgap : 7*J^3 ≤ S^3-C^3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hgap hD]

/-- A heavy triple is an unchanged labeling operation, now paid for using
a fourth-power reserve. -/
theorem triple_budget {S C J D p t : ℚ} (hD : 0 < D) (hC : 0 ≤ C)
    (hJ : 0 < J) (hhalf : 2*J ≤ S) (hsum : C+J ≤ S)
    (hp : D*S^3 ≤ p) (ht : t ≤ (21/8)*D*J^3) :
    D*C^3 ≤ p-2*t ∧ 3*t < p ∧ D*S^3/2 ≤ p-t := by
  have hg := cubic_gap hD.le hC hJ.le hhalf hsum
  have hs : (2*J)^3 ≤ S^3 := pow_le_pow_left₀ (by positivity) hhalf 3
  have hs' := mul_le_mul_of_nonneg_left hs hD.le
  have hpos : 0 < D*J^3 := mul_pos hD (pow_pos hJ 3)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A scale-independent ratio estimate, in division-free form. -/
theorem rank_ratio {D s M r : ℚ} (_hs : 0 ≤ s)
    (hM : M ≤ 2*D*s^3) (hr : D/100 ≤ r) :
    M ≤ 200*s^3*r := by
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 200*s^3 by positivity)
  nlinarith

/-- Equivalent quotient form when the size is positive. -/
theorem rank_ratio_div {D s M r : ℚ} (hs : 0 < s)
    (hM : M ≤ 2*D*s^3) (hr : D/100 ≤ r) :
    M/(200*s^3) ≤ r := by
  apply (div_le_iff₀ (by positivity : 0 < 200*s^3)).2
  simpa [mul_comm] using rank_ratio hs.le hM hr

#print axioms cubic_gap
end FixedCore.Next.CubicHeavyBounds
