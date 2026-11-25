import Next.BankUnion
import Next.HighBandNat

namespace FixedCore.BandGeometry
open scoped BigOperators

theorem pairLabels_mono {P : ℕ} {I J : Finset ℕ} (h : I ⊆ J) :
    LowBands.pairLabels P I ⊆ LowBands.pairLabels P J := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ (h hz)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, h hx, rfl⟩)

theorem intact_fresh {P : ℕ} {I used : Finset ℕ}
    (hI : I ⊆ MirrorPairs.available P used) :
    Disjoint (LowBands.pairLabels P I) used := by
  apply Finset.disjoint_left.mpr
  intro z hz hu
  rcases Finset.mem_union.mp hz with hz | hz
  · exact (MirrorPairs.available_spec.mp (hI hz)).2.1 hu
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (MirrorPairs.available_spec.mp (hI hx)).2.2 hu

theorem pairLabels_positive {P : ℕ} {I : Finset ℕ}
    (hI : I ⊆ MirrorPairs.indices P) {z : ℕ}
    (hz : z ∈ LowBands.pairLabels P I) : 0 < z ∧ z < P := by
  rcases Finset.mem_union.mp hz with hz | hz
  · have hb := MirrorPairs.index_bounds (hI hz)
    omega
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hb := MirrorPairs.index_bounds (hI hx)
    omega

def installed (P a q E : ℕ) (used : Finset ℕ) : Finset ℕ :=
  LowBands.pairLabels P
    (Finset.Icc a (a + (q + E) - 1) \ MirrorPairs.spoiled P used)

/-- An actual transfer set for a single band, with all interfaces needed by
the global union and graph constructors. -/
theorem choose_transfer {P a q E h : ℕ} (used : Finset ℕ) (low : Bool)
    (ha : 0 < a) (half : 2 * (a + (q + E) - 1) < P)
    (slack : if low then h + 2 * used.card ≤ E
      else ((P : ℤ) - h).natAbs + 2 * used.card ≤ E) :
    ∃ T : Finset ℕ,
      T.card = 2 * q ∧ Disjoint T used ∧
      T ⊆ LowBands.pairLabels P (Finset.Icc a (a + (q + E) - 1)) ∧
      (∀ z ∈ T, 0 < z) ∧
      (∀ z ∈ T, z ≤ (if low then P else 0) + h ∧
        (if low then P else 0) + h - z ∈ T) ∧
      (if low then T ⊆ installed P a q E used ∧
        Even ((installed P a q E used \ T).card) ∧
        (installed P a q E used \ T).card ≤ 2 * E else True) := by
  have hband := LowBands.band_in_mirror ha half
  have havail : Finset.Icc a (a + (q + E) - 1) \ MirrorPairs.spoiled P used ⊆
      MirrorPairs.available P used := by
    intro x hx
    obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hband hi, hn⟩
  cases hl : low
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at slack ⊢
    obtain ⟨J, hc, hj⟩ := HighBandNat.choose_high_indices used ha (by omega :
      q + ((P : ℤ) - h).natAbs + 2 * used.card ≤ q + E)
    refine ⟨LowBands.pairLabels h J, ?_, HighBandNat.pairLabels_fresh ha half hj,
      HighBandNat.pairLabels_subset ha half hj, ?_, ?_, trivial⟩
    · rw [HighBandNat.pairLabels_card ha half hj, hc]
    · intro z hz
      exact (pairLabels_positive (HighBandNat.chosen_in_mirror ha half hj) hz).1
    · intro z hz
      have hh := Packing.pairLabels_complement (HighBandNat.chosen_in_mirror ha half hj) hz
      simpa only [zero_add] using And.intro (Nat.le_of_lt hh.1) hh.2
  · simp only [hl, ↓reduceIte] at slack ⊢
    have hs := MirrorPairs.spoiled_card_le P used
    obtain ⟨J, hj, hc⟩ := PackingIntervals.choose_low_with_slack a q E h
      (MirrorPairs.spoiled P used) ha (by omega)
    have ht := LowBands.transfer_labels_subset (P := P) ha hj
    have hr := LowBands.bank_remainder (P := P) ha half hj hc
    refine ⟨LowBands.pairLabels (P + h) J, hr.1, ?_,
      ht.trans (pairLabels_mono Finset.sdiff_subset), ?_, ?_, ht, hr.2⟩
    · exact (intact_fresh havail).mono_left ht
    · intro z hz
      exact (pairLabels_positive (LowBands.chosen_in_mirror ha half hj) hz).1
    · intro z hz
      have hh := Packing.pairLabels_complement (LowBands.chosen_in_mirror ha half hj) hz
      exact ⟨Nat.le_of_lt hh.1, hh.2⟩

theorem installed_properties {P a q E : ℕ} (used : Finset ℕ)
    (ha : 0 < a) (half : 2 * (a + (q + E) - 1) < P) :
    installed P a q E used ⊆ LowBands.pairLabels P (Finset.Icc a (a + (q + E) - 1)) ∧
    Disjoint (installed P a q E used) used ∧
    (∀ z ∈ installed P a q E used, 0 < z ∧ z < P) ∧
    (∀ z ∈ installed P a q E used, z ≤ P ∧ P - z ∈ installed P a q E used) := by
  have hband := LowBands.band_in_mirror ha half
  have hind : Finset.Icc a (a + (q + E) - 1) \ MirrorPairs.spoiled P used ⊆
      MirrorPairs.indices P := Finset.sdiff_subset.trans hband
  have havail : Finset.Icc a (a + (q + E) - 1) \ MirrorPairs.spoiled P used ⊆
      MirrorPairs.available P used := by
    intro x hx
    obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hband hi, hn⟩
  refine ⟨pairLabels_mono Finset.sdiff_subset, intact_fresh havail,
    fun z hz => pairLabels_positive hind hz, ?_⟩
  intro z hz
  have hh := Packing.pairLabels_complement hind hz
  exact ⟨Nat.le_of_lt hh.1, hh.2⟩

#print axioms choose_transfer
end FixedCore.BandGeometry
