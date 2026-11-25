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

end FixedCore.DisjointBands
