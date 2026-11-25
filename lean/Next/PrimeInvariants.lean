import Next.PartialPrime
import Next.OrdinaryCompletion
import Next.ReserveModel

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k) {P : PartialSeed H} {c : Fin k} {ε : ℚ}

namespace PartialSeed.PrimeExtension
variable (E : P.PrimeExtension H c ε)

private theorem old_vertex_injective (r : Demand k) : Function.Injective (Reserves.old r) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) h)

private theorem old_edge_injective (r : Demand k) : Function.Injective (Reserves.oldEdge r) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (k+total r) => x.val) h)

private theorem old_vertex_ne_added (r : Demand k) (v : Fin (k+1)) (l : Leaf r) :
    Reserves.old r v ≠ Reserves.added r l := by
  intro h
  have he := congrArg Fin.val h
  change v.val=k+1+(Reserves.enumerate r l).val at he
  have := v.isLt
  omega

private theorem leaf_parent (l : Leaf (FixedCore.Next.PrimeExtension.reserves c E.n)) :
    l.1=c.succ := by
  by_contra h
  have hz := FixedCore.Next.PrimeExtension.reserves_away c E.n h
  have hl := l.2.isLt
  omega

/-- Added fan vertices are actual leaves, so inactive fan ranks have no
remaining children and cannot create a later singleton obligation. -/
theorem added_remaining_empty (l : Leaf (FixedCore.Next.PrimeExtension.reserves c E.n)) :
    E.seed.remainingChildren (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n))
      (Reserves.added (FixedCore.Next.PrimeExtension.reserves c E.n) l)=∅ := by
  let r := FixedCore.Next.PrimeExtension.reserves c E.n
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hp := ((E.seed.mem_remainingChildren (Reserves.core H r) (Reserves.added r l) a).mp ha).1
  obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
  cases e with
  | inl i =>
    simp only [ReserveModel.edgeEquiv_old,Reserves.oldEdge_parent] at hp
    exact old_vertex_ne_added r (H.parent i) l hp
  | inr m =>
    simp only [ReserveModel.edgeEquiv_added,Reserves.addedEdge_parent] at hp
    exact old_vertex_ne_added r m.1 l hp

/-- Apart from the marked child and its parent, every old residual child
fiber is exactly carried along by the old-edge embedding. -/
theorem remaining_other (v : Fin (k+1)) (hvc : v ≠ c.succ) (hvp : v ≠ H.parent c) :
    E.seed.remainingChildren (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n))
      (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n) v) =
    (P.remainingChildren H v).image (Reserves.oldEdge (FixedCore.Next.PrimeExtension.reserves c E.n)) := by
  classical
  let r := FixedCore.Next.PrimeExtension.reserves c E.n
  ext a
  obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
  cases e with
  | inl i =>
    simp only [r,ReserveModel.edgeEquiv_old,PartialSeed.mem_remainingChildren,
      Reserves.oldEdge_parent,E.old_assigned]
    rw [(old_vertex_injective r).eq_iff]
    have himage : Reserves.oldEdge r i ∈ (P.remainingChildren H v).image (Reserves.oldEdge r) ↔
        i ∈ P.remainingChildren H v := by
      constructor
      · intro h
        obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp h
        exact (old_edge_injective r hji) ▸ hj
      · intro h
        exact Finset.mem_image.mpr ⟨i,h,rfl⟩
    rw [himage,P.mem_remainingChildren]
    constructor
    · rintro ⟨hp,hn⟩; exact ⟨hp,fun h => hn (Or.inl h)⟩
    · rintro ⟨hp,hn⟩
      refine ⟨hp,?_⟩
      rintro (h | rfl)
      · exact hn h
      · exact hvp hp.symm
  | inr l =>
    simp only [r,ReserveModel.edgeEquiv_added,PartialSeed.mem_remainingChildren,Reserves.addedEdge_parent]
    have hparent : Reserves.old r l.1 ≠ Reserves.old r v := by
      intro h
      have he := old_vertex_injective r h
      exact hvc (he.symm.trans (E.leaf_parent H l))
    have hnot : Reserves.addedEdge r l ∉ (P.remainingChildren H v).image (Reserves.oldEdge r) := by
      intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      exact FixedCore.Next.PrimeExtension.old_ne_added r i l hi
    simp only [r] at hparent hnot
    simp only [hparent,hnot,false_and]

/-- Prime expansion preserves legal ordinary residual parity whenever the
parent losing the marked edge remains singleton-active. -/
theorem ordinaryReady (hready : P.OrdinaryReady H)
    (hparent : P.rank (H.parent c) ∈ P.A) :
    E.seed.OrdinaryReady (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n)) := by
  classical
  let r := FixedCore.Next.PrimeExtension.reserves c E.n
  intro a ha
  obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
  cases e with
  | inl i =>
    simp only [ReserveModel.edgeEquiv_old] at ha ⊢
    rw [Reserves.oldEdge_child]
    rcases (E.old_assigned i).mp ha with hi | rfl
    · by_cases hactive : P.rank i.succ ∈ P.A
      · left
        rw [E.assigned_rank i hi,E.A_eq]
        exact Or.inl hactive
      · right
        have hvc : i.succ ≠ c.succ := by
          intro h
          exact E.original_unassigned ((Fin.succ_injective _ h) ▸ hi)
        have hvp : i.succ ≠ H.parent c := by
          intro h
          exact hactive (h ▸ hparent)
        rw [E.remaining_other H i.succ hvc hvp,
          Finset.card_image_of_injective _ (old_edge_injective r)]
        exact (hready i hi).resolve_left hactive
    · left
      rw [E.child_rank,E.A_eq]
      exact Or.inr rfl
  | inr l =>
    simp only [ReserveModel.edgeEquiv_added,Reserves.addedEdge_child]
    right
    rw [E.added_remaining_empty H l]
    simp

/-- Prime expansion does not introduce any inactive nonleaf: the new marked
child is active, the other fan vertices are leaves, and old inactive vertices
retain their residual child fibers. -/
theorem inactiveLow {δ : ℚ} (hLow : P.InactiveLow H δ)
    (hparent : P.rank (H.parent c) ∈ P.A) :
    E.seed.InactiveLow (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n)) δ := by
  classical
  let r := FixedCore.Next.PrimeExtension.reserves c E.n
  intro a ha hInactive
  obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
  cases e with
  | inl i =>
    simp only [ReserveModel.edgeEquiv_old] at ha hInactive ⊢
    rw [Reserves.oldEdge_child] at hInactive ⊢
    rcases (E.old_assigned i).mp ha with hi | rfl
    · have hactive : P.rank i.succ ∉ P.A := by
        intro h
        apply hInactive
        rw [E.assigned_rank i hi,E.A_eq]
        exact Or.inl h
      have hvc : i.succ ≠ c.succ := by
        intro h
        exact E.original_unassigned ((Fin.succ_injective _ h) ▸ hi)
      have hvp : i.succ ≠ H.parent c := by
        intro h
        exact hactive (h ▸ hparent)
      rcases hLow i hi hactive with hl | he
      · left; rw [E.assigned_rank i hi]; exact hl
      · right; rw [E.remaining_other H i.succ hvc hvp,he]; simp
    · exfalso
      apply hInactive
      rw [E.child_rank,E.A_eq]
      exact Or.inr rfl
  | inr l =>
    simp only [ReserveModel.edgeEquiv_added,Reserves.addedEdge_child] at ha hInactive ⊢
    exact Or.inr (E.added_remaining_empty H l)

end PartialSeed.PrimeExtension

/-- A non-low parent with an unassigned child cannot be a protected inactive
vertex under the inactive-low invariant. -/
theorem PartialSeed.parent_active_of_nonlow (P : PartialSeed H) {δ : ℚ}
    (hδ : 0 ≤ δ) (hLow : P.InactiveLow H δ) (c : Fin k) (hc : c ∉ P.edges)
    (hparent : H.parent c=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent c)
    (hp : δ < P.rank (H.parent c)) : P.rank (H.parent c) ∈ P.A := by
  rcases hparent with h | ⟨j,hj,hjv⟩
  · rw [h,P.root_zero] at hp
    linarith
  · by_contra hInactive
    have hjI : P.rank j.succ ∉ P.A := by simpa [hjv] using hInactive
    rcases hLow j hj hjI with hl | he
    · have : P.rank (H.parent c) ≤ δ := by simpa [hjv] using hl
      linarith
    · have hm : c ∈ P.remainingChildren H j.succ :=
        (P.mem_remainingChildren H j.succ c).mpr ⟨hjv.symm,hc⟩
      rw [he] at hm
      exact Finset.notMem_empty c hm

#print axioms PartialSeed.PrimeExtension.ordinaryReady
#print axioms PartialSeed.PrimeExtension.inactiveLow
#print axioms PartialSeed.parent_active_of_nonlow
end FixedCore.Next
