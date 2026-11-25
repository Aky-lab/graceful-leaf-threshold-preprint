import Next.PartialSeed

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Canonical finite image equivalence for an injective actual-edge indexing. -/
noncomputable def blockImageEquiv {ι : Type*} [Fintype ι] (f : ι ↪ Fin k) :
    ι ≃ {i // i ∈ Finset.univ.map f} := by
  classical
  exact (Equiv.ofInjective f f.injective).trans
    (Equiv.subtypeEquivRight (fun i => by simp))

@[simp] theorem blockImageEquiv_val {ι : Type*} [Fintype ι] (f : ι ↪ Fin k) (i : ι) :
    (blockImageEquiv f i).val=f i := rfl

noncomputable def PartialSeed.indexedUpdatedRank {ι : Type*} [Fintype ι]
    (P : PartialSeed H) (f : ι ↪ Fin k) (r : ι → ℚ) : Fin (k+1) → ℚ :=
  P.updatedRank H (Finset.univ.map f) (fun i => r ((blockImageEquiv f).symm i))

@[simp] theorem PartialSeed.indexedUpdatedRank_new {ι : Type*} [Fintype ι]
    (P : PartialSeed H) (f : ι ↪ Fin k) (r : ι → ℚ) (i : ι) :
    P.indexedUpdatedRank H f r (f i).succ=r i := by
  change P.updatedRank H (Finset.univ.map f) (fun j => r ((blockImageEquiv f).symm j))
    (blockImageEquiv f i).val.succ = r i
  rw [P.updatedRank_new H _ _ (blockImageEquiv f i)]
  simp

/-- Reindex any finite local gadget onto distinct fresh actual core edges.
Parent incidence is checked against the updated actual rank function. -/
noncomputable def PartialSeed.indexedBlock {ι : Type*} [Fintype ι]
    (P : PartialSeed H) (f : ι ↪ Fin k) (r : ι → ℚ)
    (hnew : ∀ i, f i ∉ P.edges)
    (hpos : ∀ i, 0 < r i) (hinj : Function.Injective r)
    (hfresh : ∀ i, r i ∉ P.S)
    (hclosed : ∀ i, H.parent (f i)=0 ∨
      ∃ j ∈ P.edges ∪ Finset.univ.map f, j.succ=H.parent (f i))
    (e : Equiv.Perm ι)
    (he : ∀ i, |P.indexedUpdatedRank H f r (H.parent (f i))-r i|=r (e i))
    (A : Set ℚ) (hfront : SeedFrontier (P.S ∪ range r) A) : P.Block H := by
  classical
  let E := blockImageEquiv f
  let q : {i // i ∈ Finset.univ.map f} → ℚ := fun i => r (E.symm i)
  have hval (i : {i // i ∈ Finset.univ.map f}) : f (E.symm i)=i.val :=
    congrArg Subtype.val (E.apply_symm_apply i)
  have hrange : range q = range r := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨E.symm i,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨E i,by simp [q]⟩
  exact {
    edges := Finset.univ.map f
    disjoint := by
      apply Finset.disjoint_left.mpr
      intro i hi hq
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hq
      exact hnew j hi
    rank := q
    positive := fun i => hpos (E.symm i)
    injective := fun i j h => E.symm.injective (hinj h)
    fresh := fun i => hfresh (E.symm i)
    closed := by
      intro i hi
      simpa only [hval ⟨i,hi⟩] using hclosed (E.symm ⟨i,hi⟩)
    permutation := E.symm.trans (e.trans E)
    edge_difference := by
      intro i
      have hh := he (E.symm i)
      rw [hval] at hh
      simpa [q, E, PartialSeed.indexedUpdatedRank] using hh
    A := A
    frontier := by simpa [hrange] using hfront
  }

#print axioms PartialSeed.indexedBlock
end FixedCore.Next
