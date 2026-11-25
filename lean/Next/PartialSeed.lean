import Next.SeedExistence
import Next.SeedIndexed
import Next.PreparationGadgets

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- A consistent assignment on a downward-closed portion of the actual core.
The edge permutation is identity on unassigned edges. No sibling-block
restriction is imposed, so initial path gadgets can be represented. -/
structure PartialSeed where
  edges : Finset (Fin k)
  rank : Fin (k+1) → ℚ
  root_zero : rank 0 = 0
  positive : ∀ i ∈ edges, 0 < rank i.succ
  injective : ∀ i ∈ edges, ∀ j ∈ edges, rank i.succ = rank j.succ → i=j
  closed : ∀ i ∈ edges, H.parent i = 0 ∨ ∃ j ∈ edges, j.succ = H.parent i
  permutation : Equiv.Perm (Fin k)
  fixes : ∀ i ∉ edges, permutation i=i
  maps : ∀ i ∈ edges, permutation i ∈ edges
  edge_difference : ∀ i ∈ edges,
    |rank (H.parent i)-rank i.succ| = rank (permutation i).succ
  S : Set ℚ
  A : Set ℚ
  frontier : SeedFrontier S A
  assigned : ∀ i ∈ edges, rank i.succ ∈ S

noncomputable def PartialSeed.empty : PartialSeed H where
  edges := ∅
  rank _ := 0
  root_zero := rfl
  positive := by simp
  injective := by simp
  closed := by simp
  permutation := Equiv.refl _
  fixes := by simp
  maps := by simp
  edge_difference := by simp
  S := ∅
  A := ∅
  frontier := ⟨finite_empty, by simp, by simp, by simp⟩
  assigned := by simp

noncomputable def PartialSeed.updatedRank (P : PartialSeed H) (Q : Finset (Fin k))
    (r : {i // i ∈ Q} → ℚ) : Fin (k+1) → ℚ :=
  Fin.cases 0 (fun i => if h : i ∈ Q then r ⟨i,h⟩ else P.rank i.succ)

@[simp] theorem PartialSeed.updatedRank_zero (P : PartialSeed H) (Q : Finset (Fin k))
    (r : {i // i ∈ Q} → ℚ) : P.updatedRank H Q r 0 = 0 := rfl

@[simp] theorem PartialSeed.updatedRank_new (P : PartialSeed H) (Q : Finset (Fin k))
    (r : {i // i ∈ Q} → ℚ) (i : {i // i ∈ Q}) :
    P.updatedRank H Q r i.val.succ = r i := by simp [PartialSeed.updatedRank, i.property]

theorem PartialSeed.updatedRank_old (P : PartialSeed H) (Q : Finset (Fin k))
    (r : {i // i ∈ Q} → ℚ) (hQ : Disjoint P.edges Q) {i : Fin k} (hi : i ∈ P.edges) :
    P.updatedRank H Q r i.succ = P.rank i.succ := by
  have hn : i ∉ Q := fun h => Finset.disjoint_left.mp hQ hi h
  simp [PartialSeed.updatedRank,hn]

theorem PartialSeed.updatedRank_parent (P : PartialSeed H) (Q : Finset (Fin k))
    (r : {i // i ∈ Q} → ℚ) (hQ : Disjoint P.edges Q) {i : Fin k} (hi : i ∈ P.edges) :
    P.updatedRank H Q r (H.parent i) = P.rank (H.parent i) := by
  rcases P.closed i hi with h | ⟨j,hj,h⟩
  · rw [h, PartialSeed.updatedRank_zero, P.root_zero]
  · rw [← h]
    exact P.updatedRank_old H Q r hQ hj

/-- Data for one finite actual-graph extension. New vertices may have new
parents within the same block, allowing paths rather than only sibling fans. -/
structure PartialSeed.Block (P : PartialSeed H) where
  edges : Finset (Fin k)
  disjoint : Disjoint P.edges edges
  rank : {i // i ∈ edges} → ℚ
  positive : ∀ i, 0 < rank i
  injective : Function.Injective rank
  fresh : ∀ i, rank i ∉ P.S
  closed : ∀ i ∈ edges, H.parent i = 0 ∨ ∃ j ∈ P.edges ∪ edges, j.succ = H.parent i
  permutation : Equiv.Perm {i // i ∈ edges}
  edge_difference : ∀ i,
    |P.updatedRank H edges rank (H.parent i.val)-rank i| = rank (permutation i)
  A : Set ℚ
  frontier : SeedFrontier (P.S ∪ range rank) A

noncomputable def PartialSeed.Block.extendPermutation {P : PartialSeed H} (B : P.Block H) :
    Equiv.Perm (Fin k) := B.permutation.subtypeCongr (Equiv.refl _)

@[simp] theorem PartialSeed.Block.extendPermutation_inside {P : PartialSeed H}
    (B : P.Block H) {i : Fin k} (hi : i ∈ B.edges) :
    B.extendPermutation H i = (B.permutation ⟨i,hi⟩).val := by
  simp [PartialSeed.Block.extendPermutation,hi]

@[simp] theorem PartialSeed.Block.extendPermutation_outside {P : PartialSeed H}
    (B : P.Block H) {i : Fin k} (hi : i ∉ B.edges) :
    B.extendPermutation H i = i := by
  simp [PartialSeed.Block.extendPermutation,hi]

/-- Extending by an actual graph block preserves the full partial-seed
contract, including root, global rank injectivity and edge permutation. -/
noncomputable def PartialSeed.extend (P : PartialSeed H) (B : P.Block H) : PartialSeed H := by
  classical
  let r := P.updatedRank H B.edges B.rank
  let e := P.permutation.trans (B.extendPermutation H)
  have hold (i : Fin k) (hi : i ∈ P.edges) : r i.succ = P.rank i.succ :=
    P.updatedRank_old H B.edges B.rank B.disjoint hi
  have hnew (i : Fin k) (hi : i ∈ B.edges) : r i.succ = B.rank ⟨i,hi⟩ :=
    P.updatedRank_new H B.edges B.rank ⟨i,hi⟩
  have eold (i : Fin k) (hi : i ∈ P.edges) : e i=P.permutation i := by
    apply B.extendPermutation_outside H
    exact fun h => Finset.disjoint_left.mp B.disjoint (P.maps i hi) h
  have enew (i : Fin k) (hi : i ∈ B.edges) : e i=(B.permutation ⟨i,hi⟩).val := by
    have hn : i ∉ P.edges := fun h => Finset.disjoint_left.mp B.disjoint h hi
    change B.extendPermutation H (P.permutation i) = _
    rw [P.fixes i hn, B.extendPermutation_inside H hi]
  refine ⟨P.edges ∪ B.edges, r, rfl, ?_, ?_, ?_, e, ?_, ?_, ?_,
    P.S ∪ range B.rank, B.A, B.frontier, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hold i hi]; exact P.positive i hi
    · rw [hnew i hi]; exact B.positive _
  · intro i hi j hj he
    rcases Finset.mem_union.mp hi with hi | hi <;>
      rcases Finset.mem_union.mp hj with hj | hj
    · rw [hold i hi,hold j hj] at he
      exact P.injective i hi j hj he
    · rw [hold i hi,hnew j hj] at he
      exact False.elim (B.fresh ⟨j,hj⟩ (he ▸ P.assigned i hi))
    · rw [hnew i hi,hold j hj] at he
      exact False.elim (B.fresh ⟨i,hi⟩ (he.symm ▸ P.assigned j hj))
    · rw [hnew i hi,hnew j hj] at he
      exact congrArg Subtype.val (B.injective he)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases P.closed i hi with h | ⟨j,hj,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,Finset.mem_union_left _ hj,h⟩
    · exact B.closed i hi
  · intro i hi
    have hni : i ∉ P.edges := fun h => hi (Finset.mem_union_left _ h)
    have hnq : i ∉ B.edges := fun h => hi (Finset.mem_union_right _ h)
    change B.extendPermutation H (P.permutation i)=i
    rw [P.fixes i hni, B.extendPermutation_outside H hnq]
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [eold i hi]; exact Finset.mem_union_left _ (P.maps i hi)
    · rw [enew i hi]; exact Finset.mem_union_right _ (B.permutation ⟨i,hi⟩).property
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hold i hi,eold i hi,hold _ (P.maps i hi)]
      change |P.updatedRank H B.edges B.rank (H.parent i)-P.rank i.succ| = _
      rw [P.updatedRank_parent H B.edges B.rank B.disjoint hi]
      exact P.edge_difference i hi
    · rw [hnew i hi,enew i hi,hnew _ (B.permutation ⟨i,hi⟩).property]
      exact B.edge_difference ⟨i,hi⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hold i hi]; exact Or.inl (P.assigned i hi)
    · rw [hnew i hi]; exact Or.inr ⟨⟨i,hi⟩,rfl⟩

@[simp] theorem PartialSeed.extend_edges (P : PartialSeed H) (B : P.Block H) :
    (P.extend H B).edges = P.edges ∪ B.edges := rfl

@[simp] theorem PartialSeed.extend_rank (P : PartialSeed H) (B : P.Block H) :
    (P.extend H B).rank = P.updatedRank H B.edges B.rank := rfl

/-- A complete partial assignment is already a rational seed on the core. -/
noncomputable def PartialSeed.finish (P : PartialSeed H) (hfull : P.edges = Finset.univ) :
    RationalSeed H := by
  have hm (i : Fin k) : i ∈ P.edges := hfull ▸ Finset.mem_univ i
  refine ⟨P.rank,P.root_zero,?_,?_,P.permutation,fun i => P.edge_difference i (hm i)⟩
  · intro v
    refine Fin.cases ?_ (fun i => (P.positive i (hm i)).le) v
    simp [P.root_zero]
  · intro x y he
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => rfl
      | succ j => have := P.positive j (hm j); rw [P.root_zero] at he; linarith
    | succ i =>
      induction y using Fin.cases with
      | zero => have := P.positive i (hm i); rw [P.root_zero] at he; linarith
      | succ j => exact congrArg Fin.succ (P.injective i (hm i) j (hm j) he)

#print axioms PartialSeed.extend
#print axioms PartialSeed.finish
end FixedCore.Next
