import Next.InternalCore
import Next.TreeEncodingLeafExtensions

/-! The actual internal-core decomposition of every finite tree of order at least
three, including the vertex bijection, unordered-edge bijection, and degrees. -/
namespace FixedCore.InternalCore
open CoreDiameter TreeEncoding
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {k : ℕ} {H : Core k} (e : graph H ≃g G.induce (internal G))

/-- Actual leaves attached to a specified internal vertex. -/
abbrev Fiber (i : Fin (k+1)) := {v : V // v ∉ internal G ∧ G.Adj (e i).val v}

noncomputable def demand (i : Fin (k+1)) : ℕ := by
  classical
  exact Fintype.card (Fiber G e i)

noncomputable def fiberEquiv (i : Fin (k+1)) : Fiber G e i ≃ Fin (demand G e i) := by
  classical
  exact Fintype.equivFin _

noncomputable def leafVertex (l : Leaf (demand G e)) : V :=
  ((fiberEquiv G e l.1).symm l.2).val

theorem leafVertex_outside (l : Leaf (demand G e)) : leafVertex G e l ∉ internal G :=
  ((fiberEquiv G e l.1).symm l.2).property.1

theorem leafVertex_adj (l : Leaf (demand G e)) : G.Adj (e l.1).val (leafVertex G e l) :=
  ((fiberEquiv G e l.1).symm l.2).property.2

noncomputable def vertex : Vertex (demand G e) → V
  | .inl i => (e i).val
  | .inr l => leafVertex G e l

theorem vertex_injective : Function.Injective (vertex G e) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (e.injective (Subtype.ext hab))
    | inr l =>
      change (e i).val = leafVertex G e l at hab
      exact False.elim (leafVertex_outside G e l (hab ▸ (e i).property))
  | inr l =>
    cases b with
    | inl j =>
      change leafVertex G e l = (e j).val at hab
      exact False.elim (leafVertex_outside G e l (hab.symm ▸ (e j).property))
    | inr m =>
      have hp : l.1 = m.1 := by
        apply e.injective
        apply Subtype.ext
        apply outside_subsingleton G (leafVertex_outside G e l)
        · exact (leafVertex_adj G e l).symm
        · change G.Adj (leafVertex G e l) (e m.1).val
          rw [show leafVertex G e l = leafVertex G e m from hab]
          exact (leafVertex_adj G e m).symm
      obtain ⟨i,l⟩ := l
      obtain ⟨j,m⟩ := m
      dsimp at hp
      subst j
      have hlm : l = m := (fiberEquiv G e i).symm.injective (Subtype.ext hab)
      subst m
      rfl

theorem vertex_surjective (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    Function.Surjective (vertex G e) := by
  classical
  intro v
  by_cases hv : v ∈ internal G
  · refine ⟨.inl (e.symm ⟨v,hv⟩),?_⟩
    simp [vertex]
  · obtain ⟨u,hu,-⟩ := outside_unique_internal_neighbor G hG hcard hv
    let i := e.symm u
    let f : Fiber G e i := ⟨v,hv,by simpa [i] using hu.symm⟩
    refine ⟨.inr ⟨i,fiberEquiv G e i f⟩,?_⟩
    simp [vertex, leafVertex, f]

noncomputable def vertexEquiv (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    Vertex (demand G e) ≃ V :=
  Equiv.ofBijective (vertex G e) ⟨vertex_injective G e, vertex_surjective G e hG hcard⟩

theorem internal_leaf_adj_iff (i : Fin (k+1)) (l : Leaf (demand G e)) :
    G.Adj (e i).val (leafVertex G e l) ↔ i = l.1 := by
  constructor
  · intro h
    exact e.injective (Subtype.ext
      (outside_subsingleton G (leafVertex_outside G e l) h.symm (leafVertex_adj G e l).symm))
  · rintro rfl
    exact leafVertex_adj G e l

/-- A constructed graph isomorphism from the internal core plus the actual leaves. -/
noncomputable def representation (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    Representation G H (demand G e) where
  toEquiv := vertexEquiv G e hG hcard
  map_rel_iff' := by
    intro a b
    change G.Adj (vertex G e a) (vertex G e b) ↔ (extensionGraph H (demand G e)).Adj a b
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        rw [extensionGraph_old_old]
        exact e.map_rel_iff
      | inr l =>
        rw [extensionGraph_old_leaf]
        exact internal_leaf_adj_iff G e i l
    | inr l =>
      cases b with
      | inl i =>
        rw [extensionGraph_leaf_old, G.adj_comm]
        exact internal_leaf_adj_iff G e i l
      | inr m =>
        simp only [extensionGraph_leaf_leaf, iff_false]
        intro hlm
        have he : leafVertex G e m = (e l.1).val :=
          outside_subsingleton G (leafVertex_outside G e l)
            hlm (leafVertex_adj G e l).symm
        exact leafVertex_outside G e m (he.symm ▸ (e l.1).property)

 theorem representation_old_degree (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V)
    (i : Fin (k+1)) : 2 ≤ G.degree (representation G e hG hcard (.inl i)) := (e i).property

 theorem representation_leaf_degree (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V)
    (l : Leaf (demand G e)) : G.degree (representation G e hG hcard (.inr l)) = 1 :=
  outside_degree_one G hG hcard (leafVertex_outside G e l)

include e in
 theorem internal_count : Nat.card (internal G) = k+1 := by
  rw [← Nat.card_congr e.toEquiv, Nat.card_fin]

/-- Every finite tree of order at least three has the exact paper representation,
with the core vertices precisely its degree-at-least-two vertices. -/
theorem exists_representation (hG : G.IsTree) (hcard : 3 ≤ Fintype.card V) :
    ∃ k, ∃ H : Core k, ∃ c : Demand k, ∃ e : Representation G H c,
      (∀ i, 2 ≤ G.degree (e (.inl i))) ∧
      (∀ l, G.degree (e (.inr l)) = 1) ∧
      Nat.card (internal G) = k+1 ∧
      Fintype.card V = k+total c+1 ∧ Nat.card G.edgeSet = k+total c := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_internal_core G hG hcard
  exact ⟨k,H,demand G e,representation G e hG hcard,
    representation_old_degree G e hG hcard, representation_leaf_degree G e hG hcard,
    internal_count G e,
    representation_vertex_count (representation G e hG hcard),
    representation_edge_count (representation G e hG hcard)⟩

#print axioms representation
#print axioms exists_representation
end FixedCore.InternalCore
