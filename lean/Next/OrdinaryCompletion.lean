import Next.PartialChildren

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Every assigned vertex can finish ordinarily: either singleton-eligible,
or its entire residual child fiber has even cardinality. -/
def PartialSeed.OrdinaryReady (P : PartialSeed H) : Prop :=
  ∀ i ∈ P.edges, P.rank i.succ ∈ P.A ∨ Even (P.remainingChildren H i.succ).card

noncomputable def PartialSeed.fillChildren (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    PartialSeed H := P.extend H (P.childBlock H v (P.remainingChildren H v)
      (P.remainingChildren_disjoint H v)
      (fun i hi => ((P.mem_remainingChildren H v i).mp hi).1) hv B)

@[simp] theorem PartialSeed.fillChildren_edges (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).edges=P.edges ∪ P.remainingChildren H v := rfl

@[simp] theorem PartialSeed.fillChildren_A (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).A=(P.A \ {P.rank v}) ∪ range B.rank := rfl

@[simp] theorem PartialSeed.fillChildren_S (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).S=P.S ∪ range B.rank := rfl

theorem PartialSeed.fillChildren_old (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    {i : Fin k} (hi : i ∈ P.edges) :
    (P.fillChildren H v hv B).rank i.succ=P.rank i.succ :=
  P.updatedRank_old H _ B.rank (P.remainingChildren_disjoint H v) hi

@[simp] theorem PartialSeed.fillChildren_remaining_self (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).remainingChildren H v=∅ := by
  ext i
  simp [PartialSeed.remainingChildren,PartialSeed.fillChildren_edges]
  tauto

theorem PartialSeed.fillChildren_remaining_other (P : PartialSeed H) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    (w : Fin (k+1)) (hw : w ≠ v) :
    (P.fillChildren H v hv B).remainingChildren H w=P.remainingChildren H w := by
  ext i
  simp only [PartialSeed.mem_remainingChildren,PartialSeed.fillChildren_edges,Finset.mem_union]
  constructor
  · intro h; exact ⟨h.1,fun hi => h.2 (Or.inl hi)⟩
  · rintro ⟨hp,hn⟩
    refine ⟨hp,?_⟩
    rintro (hi | hi)
    · exact hn hi
    · exact hw (hp.symm.trans hi.1)

/-- Residual parity for inactive vertices is stable under processing another
parent; processing that vertex itself leaves an empty residual fiber. -/
theorem PartialSeed.fillChildren_ready (P : PartialSeed H) (hready : P.OrdinaryReady H)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).OrdinaryReady H := by
  intro i hi
  rw [PartialSeed.fillChildren_edges] at hi
  rcases Finset.mem_union.mp hi with hi | hi
  · by_cases hiv : i.succ=v
    · right
      rw [hiv,PartialSeed.fillChildren_remaining_self]
      simp
    · rcases hready i hi with hactive | heven
      · left
        rw [PartialSeed.fillChildren_old H P v hv B hi,PartialSeed.fillChildren_A]
        left
        refine ⟨hactive,?_⟩
        change P.rank i.succ ≠ P.rank v
        intro heq
        rcases hv with hv0 | ⟨j,hj,hjv⟩
        · have := P.positive i hi
          rw [hv0,P.root_zero] at heq
          linarith
        · have hr : P.rank i.succ=P.rank j.succ := by simpa [hjv] using heq
          exact hiv ((congrArg Fin.succ (P.injective i hi j hj hr)).trans hjv)
      · right
        rw [P.fillChildren_remaining_other H v hv B i.succ hiv]
        exact heven
  · left
    change P.updatedRank H (P.remainingChildren H v) B.rank i.succ ∈
      (P.A \ {P.rank v}) ∪ range B.rank
    rw [show i.succ=(⟨i,hi⟩ : {i // i ∈ P.remainingChildren H v}).val.succ from rfl,
      P.updatedRank_new H _ B.rank ⟨i,hi⟩]
    exact Or.inr ⟨⟨i,hi⟩,rfl⟩

/-- Inactive vertices that still have children are low; this is the additional
invariant allowing marked-child prime insertions only at non-low active parents. -/
def PartialSeed.InactiveLow (P : PartialSeed H) (δ : ℚ) : Prop :=
  ∀ i ∈ P.edges, P.rank i.succ ∉ P.A →
    P.rank i.succ ≤ δ ∨ P.remainingChildren H i.succ=∅

/-- Ordinary residual completion preserves the inactive-low protection rule. -/
theorem PartialSeed.fillChildren_inactiveLow (P : PartialSeed H) {δ : ℚ}
    (hLow : P.InactiveLow H δ) (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    (P.fillChildren H v hv B).InactiveLow H δ := by
  intro i hi hInactive
  rw [PartialSeed.fillChildren_edges] at hi
  rcases Finset.mem_union.mp hi with hi | hi
  · by_cases hiv : i.succ=v
    · exact Or.inr (hiv ▸ P.fillChildren_remaining_self H v hv B)
    · have hOldInactive : P.rank i.succ ∉ P.A := by
        intro hActive
        apply hInactive
        rw [P.fillChildren_old H v hv B hi,PartialSeed.fillChildren_A]
        left
        refine ⟨hActive,?_⟩
        change P.rank i.succ ≠ P.rank v
        intro heq
        rcases hv with hv0 | ⟨j,hj,hjv⟩
        · have := P.positive i hi
          rw [hv0,P.root_zero] at heq
          linarith
        · have hr : P.rank i.succ=P.rank j.succ := by simpa [hjv] using heq
          exact hiv ((congrArg Fin.succ (P.injective i hi j hj hr)).trans hjv)
      rcases hLow i hi hOldInactive with hl | he
      · left; rw [P.fillChildren_old H v hv B hi]; exact hl
      · right; rw [P.fillChildren_remaining_other H v hv B i.succ hiv]; exact he
  · exfalso
    apply hInactive
    change P.updatedRank H (P.remainingChildren H v) B.rank i.succ ∈
      (P.A \ {P.rank v}) ∪ range B.rank
    rw [show i.succ=(⟨i,hi⟩ : {i // i ∈ P.remainingChildren H v}).val.succ from rfl,
      P.updatedRank_new H _ B.rank ⟨i,hi⟩]
    exact Or.inr ⟨⟨i,hi⟩,rfl⟩

#print axioms PartialSeed.fillChildren_ready
#print axioms PartialSeed.fillChildren_inactiveLow
end FixedCore.Next
