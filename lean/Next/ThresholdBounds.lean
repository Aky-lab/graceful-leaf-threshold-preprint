import Mathlib.Tactic

namespace FixedCore.ThresholdBounds

/-- Floor dilation loses fewer than one certificate maximum. -/
theorem floor_dilation {N m : ℕ} (hm : 0 < m) :
    N / m * m ≤ N ∧ N - (N / m) * m < m := by
  constructor
  · exact Nat.div_mul_le_self N m
  · have h := Nat.mod_lt N hm
    simpa [Nat.mod_def, Nat.mul_comm] using h

/-- The scale factor times the clearing denominator stays below final size. -/
theorem scaled_denominator {N m Q : ℕ} (hQ : Q ≤ m) :
    (N / m) * Q ≤ N :=
  (Nat.mul_le_mul_left _ hQ).trans (Nat.div_mul_le_self N m)

/-- An anchor within delta of one, with a maximum within delta above one,
becomes an integer bank rank within M + 2 delta N of the final endpoint. -/
theorem bank_deficit {N m Q P M : ℕ} {δ : ℚ}
    (hm : 0 < m) (hδ : 0 ≤ δ) (hQ : Q ≤ m) (hmM : m ≤ M)
    (hP : P ≤ m) (hmax : (m : ℚ) ≤ (1 + δ) * Q)
    (hanchor : (1 - δ) * Q ≤ P) :
    ((N - (N / m) * P : ℕ) : ℚ) ≤ M + 2 * δ * N := by
  let K := N / m
  have hd := floor_dilation (N := N) hm
  have hKQ := scaled_denominator (N := N) hQ
  have hKP : K * P ≤ N :=
    (Nat.mul_le_mul_left K hP).trans hd.1
  have hKm : (K : ℚ) * m ≤ N := by exact_mod_cast hd.1
  have hKQq : (K : ℚ) * Q ≤ N := by exact_mod_cast hKQ
  have hKPq : (K : ℚ) * P ≤ N := by exact_mod_cast hKP
  have hgap : (N : ℚ) - K * m < m := by
    have hgap' : ((N - K * m : ℕ) : ℚ) < m := by exact_mod_cast hd.2
    rw [Nat.cast_sub hd.1, Nat.cast_mul] at hgap'
    exact hgap'
  rw [Nat.cast_sub hKP, Nat.cast_mul]
  have hmMq : (m : ℚ) ≤ M := by exact_mod_cast hmM
  have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
  have hdiff : (m : ℚ) - P ≤ 2 * δ * Q := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hK
  have hmulN := mul_le_mul_of_nonneg_left hKQq (by positivity : (0:ℚ) ≤ 2*δ)
  change (N : ℚ) - K * P ≤ _
  nlinarith

/-- Scaling preserves a rational near-end separation bound. -/
theorem high_deviation {N m Q h P : ℕ} {δ : ℚ}
    (hδ : 0 ≤ δ) (hQ : Q ≤ m)
    (hnear : |(h : ℚ) - P| ≤ 2 * δ * Q) :
    |((N / m) * h : ℕ) - (((N / m) * P : ℕ) : ℚ)| ≤ 2 * δ * N := by
  have hKQ : ((N / m : ℕ) : ℚ) * Q ≤ N := by
    exact_mod_cast scaled_denominator (N := N) hQ
  simp only [Nat.cast_mul]
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hmul := mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg (N / m) : (0:ℚ)≤_)
  have hmulN := mul_le_mul_of_nonneg_left hKQ (by positivity : (0:ℚ) ≤ 2*δ)
  nlinarith

theorem low_rank {N m Q h : ℕ} {δ : ℚ}
    (hδ : 0 ≤ δ) (hQ : Q ≤ m) (hnear : (h : ℚ) ≤ δ * Q) :
    (((N / m) * h : ℕ) : ℚ) ≤ δ * N := by
  have hKQ : ((N / m : ℕ) : ℚ) * Q ≤ N := by
    exact_mod_cast scaled_denominator (N := N) hQ
  rw [Nat.cast_mul]
  have hmul := mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg (N / m) : (0:ℚ)≤_)
  have hmulN := mul_le_mul_of_nonneg_left hKQ hδ
  nlinarith

/-- A single estimate controls both root and bank slack required by packing. -/
theorem packing_slack {N δ M s d E deficit : ℚ}
    (hN : 0 ≤ N) (hd : 0 ≤ d) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (hE : E ≤ 2 * δ * N + 4 * s + 5)
    (hdeficit : deficit ≤ M + 2 * δ * N) :
    2 * d * E ≤ (4*d+2)*δ*N + (M+2*d*(4*s+5)+2*s+4) ∧
    deficit + 2*d*E + 2*s + 4 ≤
      (4*d+2)*δ*N + (M+2*d*(4*s+5)+2*s+4) := by
  have hm := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2*d)
  constructor <;> nlinarith

/-- Constants chosen by the manuscript make the common packing bound no more
than half the large-site demand. -/
theorem packing_below_half {N η δ d C : ℚ}
    (hN : 0 ≤ N) (hη : 0 < η)
    (hδ : (4*d+2)*δ ≤ η/4) (hthreshold : 4*C/η ≤ N) :
    (4*d+2)*δ*N + C ≤ η*N/2 := by
  have hC : 4*C ≤ N*η := (div_le_iff₀ hη).mp hthreshold
  have hmul := mul_le_mul_of_nonneg_right hδ hN
  nlinarith

/-- Removing a fixed reserve still leaves half a large demand. -/
theorem reserve_below_half {N η A c : ℚ}
    (hη : 0 < η) (hthreshold : 2*A/η ≤ N) (hc : η*N ≤ c) :
    η*N/2 ≤ c-A := by
  have := (div_le_iff₀ hη).mp hthreshold
  nlinarith

/-- The manuscript's delta choice meets the coefficient inequality. -/
theorem delta_budget {k d : ℕ} {η : ℚ} (hη : 0 ≤ η) (hd : d ≤ k) :
    (4*(d:ℚ)+2)*(η/(100*((k:ℚ)+1))) ≤ η/4 := by
  have hk : (0:ℚ) ≤ k := Nat.cast_nonneg k
  have hdk : (d:ℚ) ≤ k := by exact_mod_cast hd
  apply (le_div_iff₀ (by norm_num : (0:ℚ)<4)).mpr
  calc
    _ = ((4*(d:ℚ)+2)*η*4)/(100*((k:ℚ)+1)) := by ring
    _ ≤ η := (div_le_iff₀ (by positivity : (0:ℚ)<100*((k:ℚ)+1))).mpr (by nlinarith)

end FixedCore.ThresholdBounds
