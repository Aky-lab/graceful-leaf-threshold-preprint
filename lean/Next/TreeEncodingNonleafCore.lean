import Next.SparseSupportAssembly

/-! The support-sensitive construction applies to an arbitrary tree using
its canonical internal core. The bound depends on the number of nonleaf
vertices in the final graph, not on a supplied core representation. -/
namespace FixedCore.TreeEncoding

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem graphGraceful_small_order (hG : G.IsTree) (hs : Fintype.card V ≤ 2) :
    GraphGraceful G := by
  obtain ⟨k, H, ⟨e⟩⟩ := exists_core G hG
  have hc : k+1 = Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  have hw : Works H 0 := by
    simpa only [gracefulThreshold_small H (by omega)] using (gracefulThreshold_spec H).1
  exact graphGraceful_of_representation ((zeroIso H).trans e) (hw _ (Nat.zero_le _))

/-- The exact uniform cutoff in terms of the actual number of internal
vertices of the final tree. The one- and two-vertex trees are graceful
without a cutoff hypothesis. -/
theorem poly_final_nonleaf (hG : G.IsTree)
    (h : SparseSupport.cutoff (Nat.card (InternalCore.internal G))
      (Nat.card (InternalCore.internal G)) ≤ Nat.card G.edgeSet) :
    GraphGraceful G := by
  by_cases hcard : 3 ≤ Fintype.card V
  · obtain ⟨k, H, c, e, -, -, hn, -, he⟩ :=
      InternalCore.exists_representation G hG hcard
    rw [hn, he] at h
    exact graphGraceful_of_representation e (SparseSupport.graceful_of_uniform_cutoff H c h)
  · exact graphGraceful_small_order hG (by omega)

/-- A simple degree-seven sufficient bound in the actual number of
nonleaf vertices. The edge count is that of the final tree itself. -/
theorem poly_final_nonleaf_degree_seven (hG : G.IsTree)
    (h : 4800010240000 * (Nat.card (InternalCore.internal G) + 1)^7 ≤
      Nat.card G.edgeSet) : GraphGraceful G := by
  by_cases hcard : 3 ≤ Fintype.card V
  · apply poly_final_nonleaf hG
    obtain ⟨k, H, c, e, -, -, hn, -, he⟩ :=
      InternalCore.exists_representation G hG hcard
    rw [hn, he] at h ⊢
    exact (SparseSupport.cutoff_le_polynomial (Nat.succ_pos _) le_rfl).trans h
  · exact graphGraceful_small_order hG (by omega)

omit [DecidableRel G.Adj] in
/-- Attaching any finite family of pendant leaves to a finite tree gives a tree. -/
theorem leafExtension_isTree (hG : G.IsTree) (c : V → ℕ) :
    (leafExtension G c).IsTree := by
  let incl : G →g leafExtension G c :=
    { toFun := Sum.inl
      map_rel' := fun h => h }
  have oldReach (u v : V) : (leafExtension G c).Reachable (.inl u) (.inl v) :=
    (hG.preconnected u v).map incl
  have parentReach (l : (v : V) × Fin (c v)) :
      (leafExtension G c).Reachable (.inl l.1) (.inr l) :=
    (show (leafExtension G c).Adj (.inl l.1) (.inr l) from rfl).reachable
  have hconn : (leafExtension G c).Connected := by
    letI : Nonempty V := hG.connected.nonempty
    constructor
    intro a b
    cases a with
    | inl a =>
      cases b with
      | inl b => exact oldReach a b
      | inr b => exact (oldReach a b.1).trans (parentReach b)
    | inr a =>
      cases b with
      | inl b => exact (parentReach a).symm.trans (oldReach a.1 b)
      | inr b => exact ((parentReach a).symm.trans (oldReach a.1 b.1)).trans (parentReach b)
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  have he := representation_edge_count (leafExtensionIso e c)
  have hv := representation_vertex_count (leafExtensionIso e c)
  rw [he, Nat.card_eq_fintype_card, hv]

omit [DecidableRel G.Adj] in
/-- The nonleaf degree-seven criterion for a prescribed leaf extension of
a named finite tree, counting only nonleaf vertices in the final graph. -/
theorem poly_leaf_extension_final_nonleaf (hG : G.IsTree) (c : V → ℕ)
    [DecidableRel (leafExtension G c).Adj]
    (h : 4800010240000 * (Nat.card (InternalCore.internal (leafExtension G c)) + 1)^7 ≤
      Nat.card (leafExtension G c).edgeSet) : GraphGraceful (leafExtension G c) :=
  poly_final_nonleaf_degree_seven (leafExtension_isTree hG c) h

end FixedCore.TreeEncoding
