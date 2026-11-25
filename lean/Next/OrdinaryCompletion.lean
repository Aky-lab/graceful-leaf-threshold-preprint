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

/-- Choose a legal bounded residual child batch, allowing both the root and
positive parents excluded from singleton eligibility. -/
theorem PartialSeed.exists_completionBatch (P : PartialSeed H) (hready : P.OrdinaryReady H)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    {M : ℚ} (hM : 0 < M) (hbound : ∀ x ∈ P.S, x ≤ M) :
    ∃ B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v),
      ∀ i, B.rank i ≤ M := by
  classical
  rcases hv with rfl | ⟨j,hj,hjv⟩
  · rw [P.root_zero]
    obtain ⟨B,hB⟩ := exists_fresh_rootBatch {i // i ∈ P.remainingChildren H 0} P.frontier hM
    exact ⟨B,fun i => (hB i).le⟩
  · have hp : 0 < P.rank v := by simpa [hjv] using P.positive j hj
    have hb : P.rank v ≤ M := by simpa [hjv] using hbound _ (P.assigned j hj)
    rcases hready j hj with hactive | heven
    · have hav : P.rank v ∈ P.A := by simpa [hjv] using hactive
      obtain ⟨B⟩ := exists_indexedChildBatch {i // i ∈ P.remainingChildren H v} P.frontier hav
      exact ⟨B,fun i => (B.rank_lt_parent hp i).le.trans hb⟩
    · have he : Even (Fintype.card {i // i ∈ P.remainingChildren H v}) := by
        simpa only [Fintype.card_coe,hjv] using heven
      obtain ⟨B⟩ := exists_indexedEvenChildBatch {i // i ∈ P.remainingChildren H v} P.frontier hp he
      exact ⟨B,fun i => (B.rank_lt_parent hp i).le.trans hb⟩

/-- Topological completion preserves every initially assigned rank and a
common upper bound. The initial assigned subtree need not be a sibling union. -/
theorem PartialSeed.exists_ordinaryStage (P : PartialSeed H) (hready : P.OrdinaryReady H)
    {M : ℚ} (hM : 0 < M) (hbound : ∀ x ∈ P.S, x ≤ M)
    (t : ℕ) (ht : t ≤ k+1) :
    ∃ T : PartialSeed H, T.OrdinaryReady H ∧ (∀ x ∈ T.S, x ≤ M) ∧
      (∀ i : Fin k, (H.parent i).val < t → i ∈ T.edges) ∧
      P.edges ⊆ T.edges ∧ (∀ i ∈ P.edges, T.rank i.succ=P.rank i.succ) := by
  classical
  induction t with
  | zero => exact ⟨P,hready,hbound,by omega,fun _ h=>h,fun _ _=>rfl⟩
  | succ t ih =>
    obtain ⟨T,hTr,hTb,hTc,hTi,hTp⟩ := ih (by omega)
    let v : Fin (k+1) := ⟨t,by omega⟩
    have hv : v=0 ∨ ∃ j ∈ T.edges, j.succ=v := by
      have hall : ∀ w : Fin (k+1), w.val=t → w=0 ∨ ∃ j ∈ T.edges, j.succ=w := by
        intro w
        refine Fin.cases ?_ (fun j hj => ?_) w
        · intro _; exact Or.inl rfl
        · right
          refine ⟨j,hTc j ?_,rfl⟩
          have he := H.earlier j
          simp only [Fin.val_succ] at hj
          omega
      exact hall v rfl
    obtain ⟨B,hB⟩ := T.exists_completionBatch H hTr v hv hM hTb
    let U := T.fillChildren H v hv B
    have hold : T.edges ⊆ U.edges := Finset.subset_union_left
    refine ⟨U,T.fillChildren_ready H hTr v hv B,?_,?_,hTi.trans hold,?_⟩
    · intro x hx
      change x ∈ T.S ∪ range B.rank at hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact hTb x hx
      · exact hB i
    · intro i hi
      by_cases he : (H.parent i).val < t
      · exact hold (hTc i he)
      · have hh : H.parent i=v := Fin.ext (by dsimp [v]; omega)
        exact T.childBlock_covers H v hv B i hh
    · intro i hi
      exact (T.fillChildren_old H v hv B (hTi hi)).trans (hTp i hi)

/-- A prepared partial tree with legal residual parity can be completed on the
same actual core, preserving its ranks, root, consistency and upper bound. -/
theorem PartialSeed.completeOrdinarily (P : PartialSeed H) (hready : P.OrdinaryReady H)
    {M : ℚ} (hM : 0 < M) (hbound : ∀ x ∈ P.S, x ≤ M) :
    ∃ R : RationalSeed H, (∀ i ∈ P.edges, R.rank i.succ=P.rank i.succ) ∧
      ∀ v, R.rank v ≤ M := by
  obtain ⟨T,hTr,hTb,hTc,hTi,hTp⟩ := P.exists_ordinaryStage H hready hM hbound (k+1) le_rfl
  have hfull : T.edges=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact hTc i (H.parent i).isLt
  refine ⟨T.finish H hfull,hTp,?_⟩
  intro v
  change T.rank v ≤ M
  refine Fin.cases ?_ (fun i => ?_) v
  · rw [T.root_zero]; exact hM.le
  · exact hTb _ (T.assigned i (hTc i (H.parent i).isLt))

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
#print axioms PartialSeed.exists_completionBatch
#print axioms PartialSeed.completeOrdinarily
#print axioms PartialSeed.fillChildren_inactiveLow
end FixedCore.Next
