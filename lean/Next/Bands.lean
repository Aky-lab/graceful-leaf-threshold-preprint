import FixedCore.MirrorPairs

namespace FixedCore.PackingBands

def prefixSum (length : ℕ → ℕ) (i : ℕ) : ℕ := (Finset.range i).sum length

def band (length : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  Finset.Icc (prefixSum length i + 1) (prefixSum length (i + 1))

@[simp] theorem prefix_zero (length : ℕ → ℕ) : prefixSum length 0 = 0 := by
  simp [prefixSum]

theorem prefix_succ (length : ℕ → ℕ) (i : ℕ) :
    prefixSum length (i + 1) = prefixSum length i + length i := by
  exact Finset.sum_range_succ _ _

theorem prefix_mono (length : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    prefixSum length i ≤ prefixSum length j := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

@[simp] theorem band_card (length : ℕ → ℕ) (i : ℕ) :
    (band length i).card = length i := by
  simp [band, prefix_succ]

theorem band_subset (length : ℕ → ℕ) {i d L : ℕ}
    (hi : i < d) (capacity : prefixSum length d ≤ L) :
    band length i ⊆ Finset.Icc 1 L := by
  intro x hx
  obtain ⟨lo, up⟩ := Finset.mem_Icc.mp hx
  have hprefix := prefix_mono length (show i + 1 ≤ d by omega)
  exact Finset.mem_Icc.mpr (by omega)

theorem bands_disjoint (length : ℕ → ℕ) {i j : ℕ} (hne : i ≠ j) :
    Disjoint (band length i) (band length j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨xlo, xup⟩ := Finset.mem_Icc.mp hx
  obtain ⟨ylo, yup⟩ := Finset.mem_Icc.mp hy
  rcases lt_or_gt_of_ne hne with h | h
  · have hm := prefix_mono length (show i + 1 ≤ j by omega)
    omega
  · have hm := prefix_mono length (show j + 1 ≤ i by omega)
    omega

/-- The band construction uses exactly the requested number of low mirror
indices, and all indices remain in the legal mirror palette. -/
theorem mirror_bands (length : ℕ → ℕ) {d P : ℕ}
    (capacity : prefixSum length d ≤ (P - 1) / 2) :
    (∀ i < d, (band length i).card = length i ∧
      band length i ⊆ MirrorPairs.indices P) ∧
    ∀ i j, i ≠ j → Disjoint (band length i) (band length j) := by
  refine ⟨?_, fun _ _ h => bands_disjoint length h⟩
  intro i hi
  exact ⟨band_card length i, band_subset length hi capacity⟩

/-- The root-demand inequality in Lemma 2 pays for all bands, all old-rank
exclusions, and the outstanding bank demand at once. `twiceBands` is the
identity obtained from even site demands and the reserve slack E. -/
theorem packing_capacity {s a b D N P d E bands : ℕ}
    (totalEdges : s + a + b + D = N) (rankBound : P ≤ N)
    (twiceBands : 2 * bands = D + 2 * d * E)
    (rootSlack : N - P + 2 * d * E + 2 * s + 4 ≤ a) :
    2 * bands + 2 * s + b ≤ 2 * ((P - 1) / 2) := by
  omega

theorem bands_fit {s a b D N P d E bands : ℕ}
    (totalEdges : s + a + b + D = N) (rankBound : P ≤ N)
    (twiceBands : 2 * bands = D + 2 * d * E)
    (rootSlack : N - P + 2 * d * E + 2 * s + 4 ≤ a) :
    bands ≤ (P - 1) / 2 := by
  have h := packing_capacity totalEdges rankBound twiceBands rootSlack
  omega

/-- Removing the allocated bands and every spoiled mirror index still leaves
at least the required number of bank pairs. -/
theorem outside_capacity {L bands spoiled q : ℕ}
    (capacity : bands + spoiled + q ≤ L)
    (used : Finset ℕ) (usedCard : used.card ≤ bands + spoiled) :
    q ≤ (Finset.Icc 1 L \ used).card := by
  have h := Finset.le_card_sdiff used (Finset.Icc 1 L)
  have hc : (Finset.Icc 1 L).card = L := by simp
  omega

end FixedCore.PackingBands
