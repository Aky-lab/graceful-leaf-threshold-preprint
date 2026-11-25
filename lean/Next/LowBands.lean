import FixedCore.MirrorPairs

namespace FixedCore.LowBands

def pairLabels (P : ℕ) (indices : Finset ℕ) : Finset ℕ :=
  indices ∪ indices.image (fun x => P - x)

theorem pairLabels_card {P : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ MirrorPairs.indices P) : (pairLabels P J).card = 2 * J.card := by
  have hinj : Set.InjOn (fun x => P - x) (J : Set ℕ) := by
    intro x hx y hy h
    have hxb := MirrorPairs.index_bounds (hJ hx)
    have hyb := MirrorPairs.index_bounds (hJ hy)
    change P - x = P - y at h
    omega
  have hdis : Disjoint J (J.image (fun x => P - x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    have hxb := MirrorPairs.index_bounds (hJ hx)
    have hyb := MirrorPairs.index_bounds (hJ hy)
    omega
  rw [pairLabels, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hinj]
  omega

theorem band_in_mirror {a n P : ℕ} (ha : 0 < a)
    (half : 2 * (a + n - 1) < P) :
    Finset.Icc a (a + n - 1) ⊆ MirrorPairs.indices P := by
  intro x hx
  have hb := Finset.mem_Icc.mp hx
  apply Finset.mem_Icc.mpr
  omega

end FixedCore.LowBands
