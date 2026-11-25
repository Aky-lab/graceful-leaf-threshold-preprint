import Next.HeavyBounds

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

/-- The explicit root scale and clearing factor yield degree eight. -/
theorem cleared_root_bound {h s : ℕ} (hh : 2^h ≤ s) :
    2^(3*(h+1)) * (2*(10000*s^2)*s^3) ≤ 160000*s^8 := by
  calc
    _ ≤ (8*s^3) * (2*(10000*s^2)*s^3) :=
      Nat.mul_le_mul_right _ (HeavyBounds.clearing_factor hh)
    _ = _ := by ring

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

/-- Quantitative assembly only: consumes an already constructed rational seed,
rank bounds and denominator certificate; it is not a seed existence theorem. -/
theorem assemble {k : ℕ} {H : Core k} (R : RationalSeed H) (s h : ℕ)
    (hh : 2^h ≤ s)
    (hint : ∀ v, IntegralAt (3*(h+1)) (R.rank v))
    (hupper : ∀ v, R.rank v ≤ (2*(10000*s^2)*s^3 : ℕ))
    (hlower : ∀ v, v ≠ 0 → (10000*(s : ℚ)^2)/100 ≤ R.rank v) :
    ∃ T : ConsistentSeed H,
      (∀ v, (T.rank v : ℚ) = (2 : ℚ)^(3*(h+1))*R.rank v) ∧
      Finset.univ.sup T.rank ≤ 160000*s^8 ∧
      (∀ v, v ≠ 0 → Finset.univ.sup T.rank ≤ 200*s^3*T.rank v) := by
  obtain ⟨T, hscale⟩ := R.exists_dyadic_consistentSeed (3*(h+1)) hint
  refine ⟨T, hscale, (dyadic_consistentSeed_max_le hscale hupper).trans
    (cleared_root_bound hh), ?_⟩
  intro v hv
  apply Finset.sup_le
  intro w _
  have hu : R.rank w ≤ 2*(10000*(s : ℚ)^2)*(s : ℚ)^3 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hupper w
  have hr := rank_ratio (s := (s : ℚ)) (by positivity) hu (hlower v hv)
  have hscaled := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (2 : ℚ)^(3*(h+1)) by positivity)
  have hq : (T.rank w : ℚ) ≤ 200*(s : ℚ)^3*(T.rank v : ℚ) := by
    rw [hscale w, hscale v]
    nlinarith
  exact_mod_cast hq


#print axioms cubic_gap
#print axioms triple_budget
#print axioms assemble
end FixedCore.Next.CubicHeavyBounds
