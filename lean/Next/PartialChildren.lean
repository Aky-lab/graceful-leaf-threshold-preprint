import Next.PartialSeed

namespace FixedCore.Next
open Set

variable {k : ℕ} (H : Core k)

/-- Turn a child-rank batch into an actual graph block at any already assigned
vertex. Only the selected fresh child edges are filled. -/
noncomputable def PartialSeed.childBlock (P : PartialSeed H) (v : Fin (k+1))
    (Q : Finset (Fin k)) (hQ : Disjoint P.edges Q)
    (hparent : ∀ i ∈ Q, H.parent i=v)
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ Q} P.S P.A (P.rank v)) : P.Block H := by
  classical
  let e := Classical.choose B.exists_matching
  have he := Classical.choose_spec B.exists_matching
  have hp : P.updatedRank H Q B.rank v=P.rank v := by
    rcases hv with rfl | ⟨j,hj,hjv⟩
    · simp [P.root_zero]
    · subst v
      exact P.updatedRank_old H Q B.rank hQ hj
  exact {
    edges := Q
    disjoint := hQ
    rank := B.rank
    positive := B.positive
    injective := B.injective
    fresh := B.fresh
    closed := by
      intro i hi
      rw [hparent i hi]
      rcases hv with h | ⟨j,hj,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,Finset.mem_union_left _ hj,h⟩
    permutation := e
    edge_difference := by
      intro i
      rw [hparent i.val i.property,hp]
      exact he i
    A := (P.A \ {P.rank v}) ∪ range B.rank
    frontier := B.frontier
  }

/-- The actual unassigned child edges at a selected core vertex. -/
def PartialSeed.remainingChildren (P : PartialSeed H) (v : Fin (k+1)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => H.parent i=v ∧ i ∉ P.edges)

@[simp] theorem PartialSeed.mem_remainingChildren (P : PartialSeed H) (v : Fin (k+1)) (i : Fin k) :
    i ∈ P.remainingChildren H v ↔ H.parent i=v ∧ i ∉ P.edges := by
  simp [PartialSeed.remainingChildren]

theorem PartialSeed.remainingChildren_disjoint (P : PartialSeed H) (v : Fin (k+1)) :
    Disjoint P.edges (P.remainingChildren H v) := by
  apply Finset.disjoint_left.mpr
  intro i hi hq
  exact ((P.mem_remainingChildren H v i).mp hq).2 hi

/-- After processing the residual child block, every child of the vertex is
assigned, including children supplied earlier by an initial path gadget. -/
theorem PartialSeed.childBlock_covers (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    ∀ i : Fin k, H.parent i=v →
      i ∈ (P.extend H (P.childBlock H v (P.remainingChildren H v)
        (P.remainingChildren_disjoint H v)
        (fun i hi => ((P.mem_remainingChildren H v i).mp hi).1) hv B)).edges := by
  intro i hi
  change i ∈ P.edges ∪ P.remainingChildren H v
  by_cases h : i ∈ P.edges
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ ((P.mem_remainingChildren H v i).mpr ⟨hi,h⟩)

#print axioms PartialSeed.childBlock
end FixedCore.Next
