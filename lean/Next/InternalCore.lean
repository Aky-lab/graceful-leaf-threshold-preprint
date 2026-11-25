import Next.TreeEncoding

/-! The internal vertices of an arbitrary finite tree of order at least three
induce a nonempty tree. Every omitted vertex is an actual degree-one leaf,
attached to exactly one internal vertex. -/
namespace FixedCore.InternalCore
open CoreDiameter

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Internal means degree at least two in the original graph. -/
def internal : Set V := {v | 2 ≤ G.degree v}

theorem outside_degree_one (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V)
    {v : V} (hv : v ∉ internal G) : G.degree v = 1 := by
  letI : Nontrivial V := ⟨Fintype.one_lt_card_iff.mp (by omega)⟩
  have hp := hG.preconnected.degree_pos_of_nontrivial v
  change ¬ 2 ≤ G.degree v at hv
  omega

theorem internal_nonempty (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    (internal G).Nonempty := by
  classical
  by_contra hn
  have hd (v : V) : G.degree v ≤ 1 := by
    have hn' : ¬ 2 ≤ G.degree v := fun h => hn ⟨v,h⟩
    omega
  have hs : ∑ v : V, G.degree v ≤ Fintype.card V := by
    calc
      _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  have ht := hG.card_edgeFinset
  omega

theorem outside_subsingleton {v : V} (hv : v ∉ internal G) :
    (G.neighborSet v).Subsingleton := by
  have hc : Fintype.card (G.neighborSet v) ≤ 1 := by
    rw [G.card_neighborSet_eq_degree]
    change ¬ 2 ≤ G.degree v at hv
    omega
  letI : Subsingleton (G.neighborSet v) := Fintype.card_le_one_iff_subsingleton.mp hc
  intro a ha b hb
  exact congrArg Subtype.val (Subsingleton.elim (⟨a,ha⟩ : G.neighborSet v) ⟨b,hb⟩)

theorem induced_isTree (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    (G.induce (internal G)).IsTree := by
  have hn := internal_nonempty G hG hcard
  letI : Nonempty (internal G) := ⟨⟨hn.choose, hn.choose_spec⟩⟩
  refine ⟨⟨hG.preconnected.induce_of_degree_eq_one (fun v hv => outside_subsingleton G hv)⟩,
    hG.isAcyclic.induce _⟩

/-- Two adjacent degree-one vertices exhaust their connected component. -/
theorem reachable_of_adj_leaves {u v : V} (hu : G.degree u = 1)
    (hv : G.degree v = 1) (huv : G.Adj u v) {z : V} (hz : G.Reachable u z) :
    z = u ∨ z = v := by
  obtain ⟨p⟩ := hz
  obtain ⟨_,_,huniqU⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
  obtain ⟨_,_,huniqV⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  have hstep : ∀ a b, a = u ∨ a = v → G.Adj a b → b = u ∨ b = v := by
    intro a b ha hab
    rcases ha with rfl | rfl
    · exact Or.inr ((huniqU b hab).trans (huniqU v huv).symm)
    · exact Or.inl ((huniqV b hab).trans (huniqV u huv.symm).symm)
  have hwalk : ∀ {a b}, G.Walk a b → a = u ∨ a = v → b = u ∨ b = v := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h q ih => exact fun ha => ih (hstep _ _ ha h)
  exact hwalk p (Or.inl rfl)

/-- Every omitted vertex is attached to a unique internal vertex. -/
theorem outside_unique_internal_neighbor (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V)
    {v : V} (hv : v ∉ internal G) :
    ∃! u : internal G, G.Adj v u.val := by
  have hdv := outside_degree_one G hG hcard hv
  obtain ⟨u,hu,huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdv
  have hui : u ∈ internal G := by
    by_contra hnu
    have hdu := outside_degree_one G hG hcard hnu
    obtain ⟨w,hw⟩ := internal_nonempty G hG hcard
    rcases reachable_of_adj_leaves G hdv hdu hu (hG.connected v w) with he | he
    · exact hv (he ▸ hw)
    · exact hnu (he ▸ hw)
  refine ⟨⟨u,hui⟩,hu,?_⟩
  intro w hw
  exact Subtype.ext (huniq w.val hw)

/-- The induced internal graph has a genuine earlier-parent encoding. -/
theorem exists_internal_core (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    ∃ k, ∃ H : Core k, Nonempty (graph H ≃g G.induce (internal G)) := by
  classical
  exact TreeEncoding.exists_core _ (induced_isTree G hG hcard)

#print axioms induced_isTree
#print axioms outside_unique_internal_neighbor
#print axioms exists_internal_core
end FixedCore.InternalCore
