import Next.BoundedDepthBatches
import Next.SeedExistence

namespace FixedCore.Next
open BoundedDepth

/-- Dyadic integral ranks need only the prescribed power of two, rather than
an uncontrolled product of all denominators. -/
theorem clear_dyadic_denominators {ι : Type*} (t : ℕ) (r : ι → ℚ)
    (hr : ∀ i, 0 ≤ r i) (hint : ∀ i, IntegralAt t (r i)) :
    ∃ n : ι → ℕ, ∀ i, (n i : ℚ) = (2 : ℚ)^t * r i := by
  classical
  choose z hz using hint
  have hz₀ (i : ι) : (0 : ℤ) ≤ z i := by
    have hq : (0 : ℚ) ≤ z i := by
      rw [hz i]
      exact mul_nonneg (by positivity) (hr i)
    exact_mod_cast hq
  refine ⟨fun i => (z i).toNat, fun i => ?_⟩
  have he : ((z i).toNat : ℚ) = (z i : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (hz₀ i)
  exact he.trans (hz i)

/-- Clearing the known dyadic denominator preserves the actual core and its
edge permutation, with exactly the requested scaling factor. -/
theorem RationalSeed.exists_dyadic_consistentSeed {k : ℕ} {H : Core k}
    (R : RationalSeed H) (t : ℕ) (hint : ∀ v, IntegralAt t (R.rank v)) :
    ∃ T : ConsistentSeed H, ∀ v, (T.rank v : ℚ) = (2 : ℚ)^t * R.rank v := by
  obtain ⟨n, hn⟩ := clear_dyadic_denominators t R.rank R.nonneg hint
  have ht : (0 : ℚ) < 2^t := by positivity
  have hzero : n 0 = 0 := by
    apply Nat.cast_injective (R := ℚ)
    simp [hn, R.root_zero]
  have hinj : Function.Injective n := by
    intro i j hij
    apply R.injective
    apply mul_left_cancel₀ ht.ne'
    rw [← hn, ← hn, hij]
  have hedge (i : Fin k) : diff (n (H.parent i)) (n i.succ) =
      n (R.edgePermutation i).succ := by
    apply Nat.cast_injective (R := ℚ)
    rw [Consistency.cast_diff, hn, hn, ← mul_sub, abs_mul, abs_of_pos ht,
      R.edge_difference, hn]
  exact ⟨⟨n, hzero, hinj, R.edgePermutation, hedge⟩, hn⟩

/-- A rational upper bound becomes an explicit natural upper bound after the
known power-of-two clearing. -/
theorem dyadic_consistentSeed_rank_le {k : ℕ} {H : Core k}
    {R : RationalSeed H} {T : ConsistentSeed H} {t M : ℕ}
    (hscale : ∀ v, (T.rank v : ℚ) = (2 : ℚ)^t * R.rank v)
    (hbound : ∀ v, R.rank v ≤ (M : ℚ)) :
    ∀ v, T.rank v ≤ 2^t*M := by
  intro v
  have hq : (T.rank v : ℚ) ≤ (2 : ℚ)^t * M := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hbound v) (by positivity)
  exact_mod_cast hq

/-- The maximum over the actual core vertices obeys the same bound. -/
theorem dyadic_consistentSeed_max_le {k : ℕ} {H : Core k}
    {R : RationalSeed H} {T : ConsistentSeed H} {t M : ℕ}
    (hscale : ∀ v, (T.rank v : ℚ) = (2 : ℚ)^t * R.rank v)
    (hbound : ∀ v, R.rank v ≤ (M : ℚ)) :
    Finset.univ.sup T.rank ≤ 2^t*M := by
  apply Finset.sup_le
  intro v _
  exact dyadic_consistentSeed_rank_le hscale hbound v

/-- Combined exact clearing and maximum bound for quantitative seed assembly. -/
theorem RationalSeed.exists_dyadic_consistentSeed_bounded {k : ℕ} {H : Core k}
    (R : RationalSeed H) (t M : ℕ) (hint : ∀ v, IntegralAt t (R.rank v))
    (hbound : ∀ v, R.rank v ≤ (M : ℚ)) :
    ∃ T : ConsistentSeed H,
      (∀ v, (T.rank v : ℚ) = (2 : ℚ)^t * R.rank v) ∧
      (∀ v, T.rank v ≤ 2^t*M) ∧ Finset.univ.sup T.rank ≤ 2^t*M := by
  obtain ⟨T, hT⟩ := R.exists_dyadic_consistentSeed t hint
  exact ⟨T, hT, dyadic_consistentSeed_rank_le hT hbound,
    dyadic_consistentSeed_max_le hT hbound⟩

/-- Any prescribed natural ranks retained in the rational construction retain
exactly their prescribed common scale in the final natural seed. -/
theorem dyadic_consistentSeed_preserves {k : ℕ} {H : Core k}
    {R : RationalSeed H} {T : ConsistentSeed H} {t a : ℕ}
    (hscale : ∀ v, (T.rank v : ℚ) = (2 : ℚ)^t * R.rank v)
    {ι : Type*} (f : ι → Fin (k+1)) (r : ι → ℕ)
    (hpres : ∀ v, R.rank (f v) = (a : ℚ) * r v) :
    ∀ v, T.rank (f v) = 2^t*a*r v := by
  intro v
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [hscale, hpres]
  ring

#print axioms clear_dyadic_denominators
#print axioms RationalSeed.exists_dyadic_consistentSeed
#print axioms RationalSeed.exists_dyadic_consistentSeed_bounded
#print axioms dyadic_consistentSeed_preserves

end FixedCore.Next
