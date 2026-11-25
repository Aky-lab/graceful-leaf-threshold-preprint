import Next.CubicHeavyBounds

/-! Two-bit denominator clearing for the cubic rational seed. Its scale and
division-free rank ratio are unchanged; only the clearing exponent changes. -/
namespace FixedCore.Next.CubicTwoBitBounds
open BoundedDepth

/-- Since 2^h≤s, two bits per light level cost at most 4s². -/
theorem clearing_factor {h s : ℕ} (hh : 2^h ≤ s) :
    2^(2*(h+1)) ≤ 4*s^2 := by
  calc
    _ = 4*(2^h)^2 := by
      rw [Nat.mul_comm 2 (h+1),pow_mul,pow_succ]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 2)

/-- The unchanged cubic rational ceiling now gives degree seven. -/
theorem cleared_root_bound {h s : ℕ} (hh : 2^h ≤ s) :
    2^(2*(h+1)) * (2*(10000*s^2)*s^3) ≤ 80000*s^7 := by
  calc
    _ ≤ (4*s^2) * (2*(10000*s^2)*s^3) :=
      Nat.mul_le_mul_right _ (clearing_factor hh)
    _ = _ := by ring

/-- Quantitative assembly only: consumes an already constructed rational seed,
rank bounds and denominator certificate; it is not a seed existence theorem. -/
theorem assemble {k : ℕ} {H : Core k} (R : RationalSeed H) (s h : ℕ)
    (hh : 2^h ≤ s)
    (hint : ∀ v, IntegralAt (2*(h+1)) (R.rank v))
    (hupper : ∀ v, R.rank v ≤ (2*(10000*s^2)*s^3 : ℕ))
    (hlower : ∀ v, v ≠ 0 → (10000*(s : ℚ)^2)/100 ≤ R.rank v) :
    ∃ T : ConsistentSeed H,
      (∀ v, (T.rank v : ℚ) = (2 : ℚ)^(2*(h+1))*R.rank v) ∧
      Finset.univ.sup T.rank ≤ 80000*s^7 ∧
      (∀ v, v ≠ 0 → Finset.univ.sup T.rank ≤ 200*s^3*T.rank v) := by
  obtain ⟨T, hscale⟩ := R.exists_dyadic_consistentSeed (2*(h+1)) hint
  refine ⟨T, hscale, (dyadic_consistentSeed_max_le hscale hupper).trans
    (cleared_root_bound hh), ?_⟩
  intro v hv
  apply Finset.sup_le
  intro w _
  have hu : R.rank w ≤ 2*(10000*(s : ℚ)^2)*(s : ℚ)^3 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hupper w
  have hr := CubicHeavyBounds.rank_ratio (s := (s : ℚ)) (by positivity) hu (hlower v hv)
  have hscaled := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (2 : ℚ)^(2*(h+1)) by positivity)
  have hq : (T.rank w : ℚ) ≤ 200*(s : ℚ)^3*(T.rank v : ℚ) := by
    rw [hscale w, hscale v]
    nlinarith
  exact_mod_cast hq


#print axioms clearing_factor
#print axioms assemble
end FixedCore.Next.CubicTwoBitBounds
