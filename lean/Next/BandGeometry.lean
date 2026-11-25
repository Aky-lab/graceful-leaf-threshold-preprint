import Next.BatchPacking
import Next.DisjointBands
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

end FixedCore.BandGeometry
