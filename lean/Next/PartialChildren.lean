import Next.PartialSeed

namespace FixedCore.Next
open Set

/-- Pair-only expansion remains available when a positive parent is deliberately
excluded from singleton eligibility, as in the quartet. -/
theorem exists_indexedEvenChildBatch (ι : Type*) [Fintype ι] {S A : Set ℚ}
    (F : SeedFrontier S A) {p : ℚ} (hp : 0 < p) (heven : Even (Fintype.card ι)) :
    Nonempty (IndexedChildBatch ι S A p) := by
  obtain ⟨n,hn⟩ := heven
  obtain ⟨B⟩ := exists_even_childBatch n F hp
  have hcard : 2*n=Fintype.card ι := by omega
  have B' : ChildBatch S A p (Fintype.card ι) := hcard ▸ B
  exact ⟨B'.index⟩

/-- Additional root leaves can be chosen below any ceiling and fresh against
an already partially assigned tree, without disturbing its active frontier. -/
theorem exists_fresh_rootBatch (ι : Type*) [Fintype ι] {S A : Set ℚ}
    (F : SeedFrontier S A) {ε : ℚ} (hε : 0 < ε) :
    ∃ B : IndexedChildBatch ι S A 0, ∀ i, B.rank i < ε := by
  classical
  obtain ⟨t,ht,hte,_,hf,_,_⟩ := exists_small_dyadic_split F.finite F.positive
    (p := 1) (ε := ε) (by norm_num) hε
  have htf : ∀ y ∈ S, ¬ Dyadic t y := by
    rintro y hy ⟨z,hz⟩
    exact hf y hy z hz
  have htS : t ∉ S := fun h => htf t h (Dyadic.refl t)
  have htA : t ∉ A := fun h => htS (F.subset h)
  obtain ⟨B⟩ := exists_indexedChildBatch ι (F.adjoin ht htf) (mem_insert t A)
  have hsub : S ∪ range B.rank ⊆ insert t S ∪ range B.rank := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (mem_insert_of_mem _ hx)
    · exact Or.inr hx
  have hactive : A ∪ range B.rank ⊆ (insert t A \ {t}) ∪ range B.rank := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨mem_insert_of_mem _ hx, fun he => htA (he ▸ hx)⟩
    · exact Or.inr hx
  refine ⟨⟨B.rank,B.injective,?_,B.positive,?_,?_⟩,fun i => (B.rank_lt_parent ht i).trans hte⟩
  · intro i hi
    exact B.fresh i (mem_insert_of_mem _ hi)
  · apply Multiset.map_congr rfl
    intro i _
    simpa using abs_of_pos (B.positive i)
  · have hz : A \ ({0}:Set ℚ) = A := by
      ext x
      simp only [mem_diff,mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hx
        exact ⟨hx,ne_of_gt (F.positive x (F.subset hx))⟩
    rw [hz]
    refine ⟨B.frontier.finite.subset hsub,?_,?_,?_⟩
    · intro x hx; exact B.frontier.positive x (hsub hx)
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl (F.subset hx)
      · exact Or.inr hx
    · intro x hx y hy hd
      exact B.frontier.minimal x (hactive hx) y (hsub hy) hd

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

#print axioms exists_indexedEvenChildBatch
#print axioms exists_fresh_rootBatch
#print axioms PartialSeed.childBlock
end FixedCore.Next
