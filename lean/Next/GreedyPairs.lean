import Next.BandGeometry

namespace FixedCore.GreedyPairs

/-- Disjoint mirror pairs for any finite collection of sites. The uniform
capacity charges every site against the total number of leaves selected. -/
theorem choose_family {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q rank : ι → ℕ) (used : Finset ℕ)
    (capacity : ∀ i ∈ I, q i + used.card + 2 * (∑ j ∈ I, q j) ≤ (rank i - 1) / 2) :
    ∃ T : ι → Finset ℕ,
      (∀ i ∈ I, (T i).card = 2 * q i) ∧
      (∀ i ∈ I, Disjoint (T i) used) ∧
      (∀ i ∈ I, ∀ z ∈ T i, 0 < z ∧ z < rank i) ∧
      (∀ i ∈ I, ∀ z ∈ T i, z ≤ rank i ∧ rank i - z ∈ T i) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j)) := by
  classical
  induction I using Finset.induction_on generalizing used with
  | empty => exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp, by simp⟩
  | @insert i I hi ih =>
    have hsum : (∑ j ∈ insert i I, q j) = q i + ∑ j ∈ I, q j := Finset.sum_insert hi
    have hcapI : ∀ j ∈ I, q j + used.card + 2 * (∑ x ∈ I, q x) ≤ (rank j - 1)/2 := by
      intro j hj
      have h := capacity j (by simp [hj])
      rw [hsum] at h
      omega
    obtain ⟨T, hcard, hfresh, hpos, hclosed, hdis⟩ := ih used hcapI
    let U := I.biUnion T
    have hUcard : U.card = 2 * ∑ j ∈ I, q j := by
      rw [Finset.card_biUnion hdis]
      calc
        _ = ∑ j ∈ I, 2 * q j := Finset.sum_congr rfl (fun j hj => hcard j hj)
        _ = _ := (Finset.mul_sum ..).symm
    have hused := Finset.card_union_le used U
    have hc : q i + (used ∪ U).card ≤ (rank i - 1)/2 := by
      have h := capacity i (by simp)
      rw [hsum] at h
      omega
    obtain ⟨J, hJ, hJcard⟩ := MirrorPairs.exists_pairs (rank i) (used ∪ U) (q i) hc
    let A := LowBands.pairLabels (rank i) J
    have hind : J ⊆ MirrorPairs.indices (rank i) :=
      fun x hx => (MirrorPairs.available_spec.mp (hJ hx)).1
    have hAcard : A.card = 2 * q i := by
      rw [LowBands.pairLabels_card hind, hJcard]
    have hAfresh : Disjoint A (used ∪ U) := BandGeometry.intact_fresh hJ
    have hAi : Disjoint A used := hAfresh.mono_right Finset.subset_union_left
    have hAj (j : ι) (hj : j ∈ I) : Disjoint A (T j) := by
      apply hAfresh.mono_right
      intro z hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hz⟩)
    let T' := Function.update T i A
    refine ⟨T', ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [T'] using hAcard
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa [T', hji] using hcard j hj
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [T'] using hAi
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa [T', hji] using hfresh j hj
    · intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have hz' : z ∈ A := by simpa [T'] using hz
        exact BandGeometry.pairLabels_positive hind hz'
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        exact hpos j hj z (by simpa [T', hji] using hz)
    · intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have hz' : z ∈ A := by simpa [T'] using hz
        have hh := Packing.pairLabels_complement hind hz'
        exact ⟨Nat.le_of_lt hh.1, by simpa [T'] using hh.2⟩
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        have hh := hclosed j hj z (by simpa [T', hji] using hz)
        simpa [T', hji] using hh
    · intro j hj l hl hjl
      by_cases hji : j = i
      · subst j
        have hli : l ≠ i := Ne.symm hjl
        have hlI := (Finset.mem_insert.mp hl).resolve_left hli
        simpa [T', hli] using hAj l hlI
      · have hjI := (Finset.mem_insert.mp hj).resolve_left hji
        by_cases hli : l = i
        · subst l
          simpa [T', hji] using (hAj j hjI).symm
        · have hlI := (Finset.mem_insert.mp hl).resolve_left hli
          simpa [T', hji, hli] using hdis j hjI l hlI hjl

end FixedCore.GreedyPairs
