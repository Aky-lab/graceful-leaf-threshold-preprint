import Next.ReserveComposition
import Next.OrdinaryCompletion

namespace FixedCore.Next
open Set
variable {a b : ℕ} {H : Core a} {K : Core b}

/-- Transport an actual partial seed through an oriented core isomorphism.
Ranks, active frontier and matching are unchanged except for vertex indexing. -/
noncomputable def PartialSeed.transport (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) : PartialSeed K := by
  classical
  let E := P.edges.image e.edge
  let r := fun v => P.rank (e.vertex.symm v)
  let σ := e.edge.symm.trans (P.permutation.trans e.edge)
  have hmem (i : Fin a) : e.edge i ∈ E ↔ i ∈ P.edges := by simp [E]
  have hr (v : Fin (a+1)) : r (e.vertex v)=P.rank v := by simp [r]
  have hc (i : Fin a) : r (e.edge i).succ=P.rank i.succ := by rw [← e.child_eq,hr]
  have hp (i : Fin a) : r (K.parent (e.edge i))=P.rank (H.parent i) := by rw [← e.parent_eq,hr]
  have hs (i : Fin a) : σ (e.edge i)=e.edge (P.permutation i) := by simp [σ]
  refine ⟨E,r,?_,?_,?_,?_,σ,?_,?_,?_,P.S,P.A,P.frontier,?_⟩
  · rw [← hroot,hr,P.root_zero]
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [hc]
    exact P.positive i ((hmem i).mp hi)
  · intro i hi j hj he
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    obtain ⟨j,rfl⟩ := e.edge.surjective j
    rw [hc,hc] at he
    exact congrArg e.edge (P.injective i ((hmem i).mp hi) j ((hmem j).mp hj) he)
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [← e.parent_eq]
    rcases P.closed i ((hmem i).mp hi) with h | ⟨j,hj,hjv⟩
    · exact Or.inl (by rw [h,hroot])
    · exact Or.inr ⟨e.edge j,(hmem j).mpr hj,by rw [← e.child_eq,hjv]⟩
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [hs,P.fixes i (fun h => hi ((hmem i).mpr h))]
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [hs]
    exact (hmem _).mpr (P.maps i ((hmem i).mp hi))
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [hp,hc,hs,hc]
    exact P.edge_difference i ((hmem i).mp hi)
  · intro i hi
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    rw [hc]
    exact P.assigned i ((hmem i).mp hi)

@[simp] theorem PartialSeed.transport_edges (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) :
    (P.transport e hroot).edges=P.edges.image e.edge := rfl

@[simp] theorem PartialSeed.transport_rank (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (v : Fin (a+1)) :
    (P.transport e hroot).rank (e.vertex v)=P.rank v := by
  change P.rank (e.vertex.symm (e.vertex v))=P.rank v
  rw [e.vertex.symm_apply_apply]

@[simp] theorem PartialSeed.transport_rank_child (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (i : Fin a) :
    (P.transport e hroot).rank (e.edge i).succ=P.rank i.succ := by
  rw [← e.child_eq,P.transport_rank]

@[simp] theorem PartialSeed.transport_S (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) :
    (P.transport e hroot).S=P.S := rfl

@[simp] theorem PartialSeed.transport_A (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) :
    (P.transport e hroot).A=P.A := rfl

@[simp] theorem PartialSeed.transport_assigned (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (i : Fin a) :
    e.edge i ∈ (P.transport e hroot).edges ↔ i ∈ P.edges := by
  classical
  simp

/-- Residual child fibers are transported exactly, not merely bounded. -/
theorem PartialSeed.transport_remainingChildren (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (v : Fin (a+1)) :
    (P.transport e hroot).remainingChildren K (e.vertex v)=
      (P.remainingChildren H v).image e.edge := by
  classical
  ext i
  obtain ⟨i,rfl⟩ := e.edge.surjective i
  simp only [PartialSeed.mem_remainingChildren,PartialSeed.transport_assigned]
  rw [← e.parent_eq]
  simp

@[simp] theorem PartialSeed.transport_remaining_card (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (v : Fin (a+1)) :
    ((P.transport e hroot).remainingChildren K (e.vertex v)).card=
      (P.remainingChildren H v).card := by
  rw [P.transport_remainingChildren e hroot v]
  exact Finset.card_image_of_injective _ e.edge.injective

theorem PartialSeed.transport_ready (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0)
    (hready : P.OrdinaryReady H) : (P.transport e hroot).OrdinaryReady K := by
  intro i hi
  obtain ⟨i,rfl⟩ := e.edge.surjective i
  have hi' := (P.transport_assigned e hroot i).mp hi
  rcases hready i hi' with ha | he
  · left
    simpa using ha
  · right
    rw [← e.child_eq,P.transport_remaining_card]
    exact he

theorem PartialSeed.transport_inactiveLow (P : PartialSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0)
    {δ : ℚ} (hlow : P.InactiveLow H δ) : (P.transport e hroot).InactiveLow K δ := by
  intro i hi hn
  obtain ⟨i,rfl⟩ := e.edge.surjective i
  have hi' := (P.transport_assigned e hroot i).mp hi
  have hn' : P.rank i.succ ∉ P.A := by simpa using hn
  rcases hlow i hi' hn' with h | h
  · left
    simpa using h
  · right
    rw [← e.child_eq,P.transport_remainingChildren,h]
    simp

/-- Full rational seeds transport along the same rooted graph equivalence. -/
noncomputable def RationalSeed.transport (P : RationalSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) : RationalSeed K where
  rank v := P.rank (e.vertex.symm v)
  root_zero := by rw [← hroot,e.vertex.symm_apply_apply,P.root_zero]
  nonneg v := P.nonneg _
  injective := P.injective.comp e.vertex.symm.injective
  edgePermutation := e.edge.symm.trans (P.edgePermutation.trans e.edge)
  edge_difference i := by
    obtain ⟨i,rfl⟩ := e.edge.surjective i
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    rw [← e.parent_eq,← e.child_eq,← e.child_eq]
    simp only [Equiv.symm_apply_apply]
    exact P.edge_difference i

@[simp] theorem RationalSeed.transport_rank (P : RationalSeed H)
    (e : ReserveComposition.OrientedIso H K) (hroot : e.vertex 0=0) (v : Fin (a+1)) :
    (P.transport e hroot).rank (e.vertex v)=P.rank v := by
  change P.rank (e.vertex.symm (e.vertex v))=P.rank v
  rw [e.vertex.symm_apply_apply]

#print axioms RationalSeed.transport
#print axioms PartialSeed.transport
#print axioms PartialSeed.transport_ready
#print axioms PartialSeed.transport_inactiveLow
end FixedCore.Next
