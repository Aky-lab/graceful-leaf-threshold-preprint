import Next.Bands
import Next.LowBands

namespace FixedCore.DisjointBands

theorem pairLabels_disjoint {P : ℕ} {I J : Finset ℕ}
    (hI : I ⊆ MirrorPairs.indices P) (hJ : J ⊆ MirrorPairs.indices P)
    (hd : Disjoint I J) :
    Disjoint (LowBands.pairLabels P I) (LowBands.pairLabels P J) := by
  apply Finset.disjoint_left.mpr
  intro x hx hjx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hjx with hy | hy
    · exact Finset.disjoint_left.mp hd hx hy
    · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hy
      have hxb := MirrorPairs.index_bounds (hI hx)
      have hyb := MirrorPairs.index_bounds (hJ hy)
      omega
  · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hjx with hz | hz
    · have hxb := MirrorPairs.index_bounds (hJ hz)
      have hyb := MirrorPairs.index_bounds (hI hy)
      omega
    · obtain ⟨z, hz, hzEq⟩ := Finset.mem_image.mp hz
      have hyb := MirrorPairs.index_bounds (hI hy)
      have hzb := MirrorPairs.index_bounds (hJ hz)
      have heq : y = z := by omega
      subst z
      exact Finset.disjoint_left.mp hd hy hz

def allBands (length : ℕ → ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).biUnion (PackingBands.band length)

theorem allBands_card (length : ℕ → ℕ) (d : ℕ) :
    (allBands length d).card = PackingBands.prefixSum length d := by
  rw [allBands, Finset.card_biUnion]
  · simp [PackingBands.band_card, PackingBands.prefixSum]
  · intro i _ j _ hne
    exact PackingBands.bands_disjoint length hne

theorem allBands_subset {length : ℕ → ℕ} {d P : ℕ}
    (capacity : PackingBands.prefixSum length d ≤ (P - 1) / 2) :
    allBands length d ⊆ MirrorPairs.indices P := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
  exact PackingBands.band_subset length (Finset.mem_range.mp hi) capacity hx

def outside (length : ℕ → ℕ) (d P : ℕ) (used : Finset ℕ) : Finset ℕ :=
  MirrorPairs.indices P \ (allBands length d ∪ MirrorPairs.spoiled P used)

/-- Whole unused mirror pairs outside every allocated band can be chosen in
exactly the required quantity, after charging each used rank only once. -/
theorem choose_outside {length : ℕ → ℕ} {d P q : ℕ} (used : Finset ℕ)
    (capacity : PackingBands.prefixSum length d + used.card + q ≤ (P - 1) / 2) :
    ∃ chosen : Finset ℕ, chosen.card = q ∧ chosen ⊆ outside length d P used := by
  have hbad := MirrorPairs.spoiled_card_le P used
  have hu := Finset.card_union_le (allBands length d) (MirrorPairs.spoiled P used)
  have ha := allBands_card length d
  have hi : (MirrorPairs.indices P).card = (P - 1) / 2 := by
    simp [MirrorPairs.indices]
  have hdiff := Finset.le_card_sdiff
    (allBands length d ∪ MirrorPairs.spoiled P used) (MirrorPairs.indices P)
  have hq : q ≤ (outside length d P used).card := by
    unfold outside
    omega
  obtain ⟨chosen, hs, hc⟩ := Finset.exists_subset_card_eq hq
  exact ⟨chosen, hc, hs⟩

theorem outside_available {length : ℕ → ℕ} {d P x : ℕ} {used : Finset ℕ}
    (hx : x ∈ outside length d P used) :
    x ∈ MirrorPairs.available P used ∧ x ∉ allBands length d := by
  obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hx
  have hband : x ∉ allBands length d := fun h => hn (Finset.mem_union_left _ h)
  have hspoiled : x ∉ MirrorPairs.spoiled P used := fun h => hn (Finset.mem_union_right _ h)
  exact ⟨Finset.mem_sdiff.mpr ⟨hi, hspoiled⟩, hband⟩

theorem outside_labels_disjoint {length : ℕ → ℕ} {d P : ℕ} {used chosen : Finset ℕ}
    (capacity : PackingBands.prefixSum length d ≤ (P - 1) / 2)
    (chosen_ok : chosen ⊆ outside length d P used) :
    Disjoint (LowBands.pairLabels P chosen) (LowBands.pairLabels P (allBands length d)) := by
  have hi : chosen ⊆ MirrorPairs.indices P := by
    intro x hx
    exact (Finset.mem_sdiff.mp (chosen_ok hx)).1
  apply pairLabels_disjoint hi (allBands_subset capacity)
  apply Finset.disjoint_left.mpr
  intro x hx hband
  exact (outside_available (chosen_ok hx)).2 hband

end FixedCore.DisjointBands
