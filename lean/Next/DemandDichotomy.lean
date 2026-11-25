import Mathlib.Tactic

namespace FixedCore.DemandDichotomy

/-- Either every site but one has small demand, or two distinct sites each
carry a large demand. No choice of an ordering or tie-breaking rule is assumed. -/
theorem one_or_two {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (hne : S.Nonempty) (c : ι → ℚ) (cutoff : ℚ) :
    (∃ u ∈ S, ∀ v ∈ S, v ≠ u → c v < cutoff) ∨
    (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ cutoff ≤ c u ∧ cutoff ≤ c v) := by
  classical
  by_cases hlarge : ∃ u ∈ S, cutoff ≤ c u
  · obtain ⟨u, hu, hcu⟩ := hlarge
    by_cases hother : ∃ v ∈ S, v ≠ u ∧ cutoff ≤ c v
    · obtain ⟨v, hv, hne, hcv⟩ := hother
      exact Or.inr ⟨u, hu, v, hv, Ne.symm hne, hcu, hcv⟩
    · refine Or.inl ⟨u, hu, ?_⟩
      intro v hv hne
      exact lt_of_not_ge (fun h => hother ⟨v, hv, hne, h⟩)
  · obtain ⟨u, hu⟩ := hne
    refine Or.inl ⟨u, hu, ?_⟩
    intro v hv _
    exact lt_of_not_ge (fun h => hlarge ⟨v, hv, h⟩)

/-- The small-site alternative gives the exact sum estimate used by the
first-table construction. Charging |S| sites is deliberately conservative. -/
theorem small_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℚ)
    (u : ι) (cutoff : ℚ) (hcutoff : 0 ≤ cutoff)
    (hsmall : ∀ v ∈ S, v ≠ u → c v < cutoff) :
    (∑ v ∈ S.erase u, c v) ≤ S.card * cutoff := by
  calc
    _ ≤ ∑ _v ∈ S.erase u, cutoff := by
      apply Finset.sum_le_sum
      intro v hv
      exact le_of_lt (hsmall v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1)
    _ = ((S.erase u).card : ℚ) * cutoff := by simp
    _ ≤ S.card * cutoff := by
      apply mul_le_mul_of_nonneg_right _ hcutoff
      exact_mod_cast Finset.card_le_card (Finset.erase_subset u S)

/-- A rational eta budget turns the small-site sum into the integer-scaled
capacity bound required by the dominant-root theorem. -/
theorem dominant_bound {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℚ)
    (u : ι) {η N M : ℚ} (hη : 0 ≤ η) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hbudget : 16 * M * S.card * η ≤ 1)
    (hsmall : ∀ v ∈ S, v ≠ u → c v < η*N) :
    16*M*(∑ v ∈ S.erase u, c v) ≤ N := by
  have hs := small_sum S c u (η*N) (mul_nonneg hη hN) hsmall
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16*M)
  have hb := mul_le_mul_of_nonneg_right hbudget hN
  nlinarith

/-- The eta chosen from a nonempty site set and a positive table maximum
meets the preceding budget exactly. -/
theorem eta_budget {n M : ℕ} (hn : 0 < n) (hM : 0 < M) :
    16*(M:ℚ)*n*(1/(16*(n:ℚ)*M)) = 1 := by
  have hnq : (n:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  field_simp

end FixedCore.DemandDichotomy
