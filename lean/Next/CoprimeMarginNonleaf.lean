import Next.CoprimeMarginAssembly
import Next.TreeEncodingNonleafCore

namespace FixedCore.TreeEncoding

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem coprimeMargin_graphGraceful_small_order (hG : G.IsTree) (hs : Fintype.card V ≤ 2) :
    GraphGraceful G := by
  obtain ⟨k, H, ⟨e⟩⟩ := exists_core G hG
  have hc : k+1 = Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  have hw : Works H 0 := by
    simpa only [gracefulThreshold_small H (by omega)] using (gracefulThreshold_spec H).1
  exact graphGraceful_of_representation ((zeroIso H).trans e) (hw _ (Nat.zero_le _))

/-- The improved uniform cutoff applies with the final tree's intrinsic
number of vertices of degree at least two. -/
theorem poly_coprime_margin_final_nonleaf (hG : G.IsTree)
    (h : CoprimeMargin.supportCutoff (Nat.card (InternalCore.internal G))
      (Nat.card (InternalCore.internal G)) ≤ Nat.card G.edgeSet) :
    GraphGraceful G := by
  by_cases hcard : 3 ≤ Fintype.card V
  · obtain ⟨k, H, c, e, -, -, hn, -, he⟩ :=
      InternalCore.exists_representation G hG hcard
    rw [hn, he] at h
    exact graphGraceful_of_representation e (CoprimeMargin.graceful_of_uniform_cutoff H c h)
  · exact coprimeMargin_graphGraceful_small_order hG (by omega)

/-- The improved degree-seven coefficient applies directly to the final
nonleaf count, not to the size of an arbitrary original presentation. -/
theorem poly_coprime_margin_final_nonleaf_degree_seven (hG : G.IsTree)
    (h : 33395200 * (Nat.card (InternalCore.internal G) + 1)^7 ≤
      Nat.card G.edgeSet) : GraphGraceful G := by
  by_cases hcard : 3 ≤ Fintype.card V
  · apply poly_coprime_margin_final_nonleaf hG
    obtain ⟨k, H, c, e, -, -, hn, -, _⟩ :=
      InternalCore.exists_representation G hG hcard
    rw [hn] at h ⊢
    exact (CoprimeMargin.supportCutoff_le_polynomial (Nat.succ_pos _) le_rfl).trans h
  · exact coprimeMargin_graphGraceful_small_order hG (by omega)

omit [DecidableRel G.Adj] in
/-- The same intrinsic bound for the named final extension graph. -/
theorem poly_coprime_margin_leaf_extension_final_nonleaf (hG : G.IsTree) (c : V → ℕ)
    [DecidableRel (leafExtension G c).Adj]
    (h : 33395200 * (Nat.card (InternalCore.internal (leafExtension G c)) + 1)^7 ≤
      Nat.card (leafExtension G c).edgeSet) : GraphGraceful (leafExtension G c) :=
  poly_coprime_margin_final_nonleaf_degree_seven (leafExtension_isTree hG c) h

end FixedCore.TreeEncoding
