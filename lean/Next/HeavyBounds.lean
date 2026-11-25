import Next.BoundedDepthInteger
namespace FixedCore.Next
open BoundedDepth
namespace HeavyBounds

/-- The sixth-power budget pays for a triple while retaining the heavy child. -/
theorem sixth_gap {S C J D : ℚ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hJ : 0 ≤ J) (hhalf : 2*J ≤ S) (hsum : C+J ≤ S) :
    32*D*J^6 ≤ D*(S^6-C^6) := by
  have hCS : C ≤ S := by linarith
  have hS : 0 ≤ S := le_trans hC hCS
  have hpow : C^5 ≤ S^5 := pow_le_pow_left₀ hC hCS 5
  have hpow' : (2*J)^5 ≤ S^5 := pow_le_pow_left₀ (by positivity) hhalf 5
  have h₁ := mul_le_mul_of_nonneg_left hpow hC
  have h₂ := mul_le_mul_of_nonneg_left hpow' hJ
  have h₃ := mul_nonneg (show 0 ≤ S-C-J by linarith)
    (show 0 ≤ S^5 by positivity)
  have hg : 32*J^6 ≤ S^6-C^6 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

/-- Local triple bounds with a half-budget still available above the triple. -/
theorem triple_budget {S C J D p t : ℚ} (hD : 0 < D) (hC : 0 ≤ C)
    (hJ : 0 < J) (hhalf : 2*J ≤ S) (hsum : C+J ≤ S)
    (hp : D*S^6 ≤ p) (ht : t ≤ 5*D*J^6) :
    D*C^6 ≤ p-2*t ∧ 3*t < p ∧ D*S^6/2 ≤ p-t := by
  have hg := sixth_gap hD.le hC hJ.le hhalf hsum
  have hs : (2*J)^6 ≤ S^6 := pow_le_pow_left₀ (by positivity) hhalf 6
  have hs' := mul_le_mul_of_nonneg_left hs hD.le
  have hpos : 0 < D*J^6 := mul_pos hD (pow_pos hJ 6)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A light child uses at most one sixty-fourth of the sixth-power budget. -/
theorem light_reserve {S L D q : ℚ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hhalf : 2*L ≤ S) (hq : D*S^6/27 ≤ q) : D*L^6 ≤ q := by
  have hp : (2*L)^6 ≤ S^6 := pow_le_pow_left₀ (by positivity) hhalf 6
  have hm := mul_le_mul_of_nonneg_left hp hD
  have hz : 0 ≤ D*L^6 := by positivity
  nlinarith

/-- Three denominator bits per light level clear within a cubic factor. -/
theorem clearing_factor {h s : ℕ} (hh : 2^h ≤ s) :
    2^(3*(h+1)) ≤ 8*s^3 := by
  calc
    2^(3*(h+1)) = 8*(2^h)^3 := by
      rw [Nat.mul_add, pow_add, Nat.mul_comm 3 h, pow_mul]
      norm_num
      omega
    _ ≤ 8*s^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 3)

/-- The explicit root scale and clearing factor yield degree eleven. -/
theorem cleared_root_bound {h s : ℕ} (hh : 2^h ≤ s) :
    2^(3*(h+1)) * (2*(10000*s^2)*s^6) ≤ 160000*s^11 := by
  calc
    _ ≤ (8*s^3) * (2*(10000*s^2)*s^6) :=
      Nat.mul_le_mul_right _ (clearing_factor hh)
    _ = _ := by ring

/-- A scale-independent ratio estimate, in division-free form. -/
theorem rank_ratio {D s M r : ℚ} (hs : 0 ≤ s)
    (hM : M ≤ 2*D*s^6) (hr : D/100 ≤ r) :
    M ≤ 200*s^6*r := by
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 200*s^6 by positivity)
  nlinarith

/-- Equivalent quotient form when the size is positive. -/
theorem rank_ratio_div {D s M r : ℚ} (hs : 0 < s)
    (hM : M ≤ 2*D*s^6) (hr : D/100 ≤ r) :
    M/(200*s^6) ≤ r := by
  apply (div_le_iff₀ (by positivity : 0 < 200*s^6)).2
  simpa [mul_comm] using rank_ratio hs.le hM hr

/-- Quantitative assembly only: consumes an already constructed rational seed,
rank bounds and denominator certificate; it is not a seed existence theorem. -/
theorem assemble {k : ℕ} {H : Core k} (R : RationalSeed H) (s h : ℕ)
    (hh : 2^h ≤ s)
    (hint : ∀ v, IntegralAt (3*(h+1)) (R.rank v))
    (hupper : ∀ v, R.rank v ≤ (2*(10000*s^2)*s^6 : ℕ))
    (hlower : ∀ v, v ≠ 0 → (10000*(s : ℚ)^2)/100 ≤ R.rank v) :
    ∃ T : ConsistentSeed H,
      (∀ v, (T.rank v : ℚ) = (2 : ℚ)^(3*(h+1))*R.rank v) ∧
      Finset.univ.sup T.rank ≤ 160000*s^11 ∧
      (∀ v, v ≠ 0 → Finset.univ.sup T.rank ≤ 200*s^6*T.rank v) := by
  obtain ⟨T, hscale⟩ := R.exists_dyadic_consistentSeed (3*(h+1)) hint
  refine ⟨T, hscale, (dyadic_consistentSeed_max_le hscale hupper).trans
    (cleared_root_bound hh), ?_⟩
  intro v hv
  apply Finset.sup_le
  intro w _
  have hu : R.rank w ≤ 2*(10000*(s : ℚ)^2)*(s : ℚ)^6 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hupper w
  have hr := rank_ratio (s := (s : ℚ)) (by positivity) hu (hlower v hv)
  have hscaled := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (2 : ℚ)^(3*(h+1)) by positivity)
  have hq : (T.rank w : ℚ) ≤ 200*(s : ℚ)^6*(T.rank v : ℚ) := by
    rw [hscale w, hscale v]
    nlinarith
  exact_mod_cast hq

#print axioms sixth_gap
#print axioms triple_budget
#print axioms light_reserve
#print axioms clearing_factor
#print axioms assemble
end HeavyBounds
end FixedCore.Next
