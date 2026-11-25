import Next.CubicTwoBitBounds
import Next.SparseChoiceScale

/-! The two-bit quadratic clearing factor combined with the new
logarithmic-window rational scale. -/
namespace FixedCore.Next.SparseHeavyBounds
open BoundedDepth

/-- The seed keeps the cubic ratio while its absolute span scales with
the actual logarithmic exclusion window. -/
theorem cleared_root_bound {h s : ℕ} (hh : 2^h ≤ s) :
    2^(2*(h+1)) * (2*sparseChoiceScale s*s^3) ≤ 4096*s^6*(sparseWindow s+1) := by
  calc
    _ ≤ (4*s^2) * (2*sparseChoiceScale s*s^3) :=
      Nat.mul_le_mul_right _ (CubicTwoBitBounds.clearing_factor hh)
    _ = _ := by unfold sparseChoiceScale; ring

/-- Quantitative assembly only: consumes an already constructed rational seed,
rank bounds and denominator certificate; it is not a seed existence theorem. -/
theorem assemble {k : ℕ} {H : Core k} (R : RationalSeed H) (s h : ℕ)
    (hh : 2^h ≤ s)
    (hint : ∀ v, IntegralAt (2*(h+1)) (R.rank v))
    (hupper : ∀ v, R.rank v ≤ (2*sparseChoiceScale s*s^3 : ℕ))
    (hlower : ∀ v, v ≠ 0 → (sparseChoiceScale s : ℚ)/100 ≤ R.rank v) :
    ∃ T : ConsistentSeed H,
      (∀ v, (T.rank v : ℚ) = (2 : ℚ)^(2*(h+1))*R.rank v) ∧
      Finset.univ.sup T.rank ≤ 4096*s^6*(sparseWindow s+1) ∧
      (∀ v, v ≠ 0 → Finset.univ.sup T.rank ≤ 200*s^3*T.rank v) := by
  obtain ⟨T, hscale⟩ := R.exists_dyadic_consistentSeed (2*(h+1)) hint
  refine ⟨T, hscale, (dyadic_consistentSeed_max_le hscale hupper).trans
    (cleared_root_bound hh), ?_⟩
  intro v hv
  apply Finset.sup_le
  intro w _
  have hu : R.rank w ≤ 2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hupper w
  have hr := CubicHeavyBounds.rank_ratio (s := (s : ℚ)) (by positivity) hu (hlower v hv)
  have hscaled := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (2 : ℚ)^(2*(h+1)) by positivity)
  have hq : (T.rank w : ℚ) ≤ 200*(s : ℚ)^3*(T.rank v : ℚ) := by
    rw [hscale w, hscale v]
    nlinarith
  exact_mod_cast hq


#print axioms cleared_root_bound
#print axioms assemble
end FixedCore.Next.SparseHeavyBounds
