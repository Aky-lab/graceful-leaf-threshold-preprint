import Next.PrimeInvariants
import Next.PartialTransport
import Next.PrimeMeasure

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Every already assigned marked nonroot vertex lies in an endpoint band. -/
def PartialSeed.GoodMarks (P : PartialSeed H) (marks : Finset (Fin (k+1))) (δ : ℚ) : Prop :=
  ∀ i ∈ P.edges, i.succ ∈ marks → P.rank i.succ ≤ δ ∨ 1-δ ≤ P.rank i.succ

/-- The actual-graph completion contract: all additional leaves have even
counts at marked sites only, initial assigned ranks are retained, and every
original mark has an endpoint-band rank. -/
structure PartialSeed.MarkedCompletion (P : PartialSeed H)
    (marks : Finset (Fin (k+1))) (δ : ℚ) where
  reserves : Demand k
  even : ∀ v, Even (reserves v)
  support : ∀ v ∉ marks, reserves v=0
  seed : RationalSeed (Reserves.core H reserves)
  old_rank : ∀ i ∈ P.edges, seed.rank (Reserves.old reserves i.succ)=P.rank i.succ
  bounded : ∀ v, seed.rank v ≤ 1
  marked : ∀ v ∈ marks,
    seed.rank (Reserves.old reserves v) ≤ δ ∨ 1-δ ≤ seed.rank (Reserves.old reserves v)

/-- Processing a child fiber preserves old marked ranks; new marked children
are permitted only when the supplied batch puts them below the low ceiling. -/
theorem PartialSeed.fillChildren_goodMarks (P : PartialSeed H)
    {marks : Finset (Fin (k+1))} {δ : ℚ} (hgood : P.GoodMarks H marks δ)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    (hnew : ∀ i, i.val.succ ∈ marks → B.rank i ≤ δ) :
    (P.fillChildren H v hv B).GoodMarks H marks δ := by
  intro i hi hm
  rw [PartialSeed.fillChildren_edges] at hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rw [P.fillChildren_old H v hv B hi]
    exact hgood i hi hm
  · left
    change P.updatedRank H (P.remainingChildren H v) B.rank i.succ ≤ δ
    rw [show i.succ=(⟨i,hi⟩ : {i // i ∈ P.remainingChildren H v}).val.succ from rfl,
      P.updatedRank_new H _ B.rank ⟨i,hi⟩]
    exact hnew ⟨i,hi⟩ hm

/-- Any low parent can assign its whole residual fiber with all child ranks
low, including a root with an arbitrary existing positive frontier. -/
theorem PartialSeed.exists_lowBatch (P : PartialSeed H) (hready : P.OrdinaryReady H)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    {δ : ℚ} (hδ : 0 < δ) (hp : P.rank v ≤ δ) :
    ∃ B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v),
      ∀ i, B.rank i < δ := by
  classical
  rcases hv with rfl | ⟨j,hj,hjv⟩
  · rw [P.root_zero]
    exact exists_fresh_rootBatch _ P.frontier hδ
  · have hpp : 0 < P.rank v := by simpa [hjv] using P.positive j hj
    rcases hready j hj with hactive | heven
    · have hav : P.rank v ∈ P.A := by simpa [hjv] using hactive
      obtain ⟨B⟩ := exists_indexedChildBatch {i // i ∈ P.remainingChildren H v} P.frontier hav
      exact ⟨B,fun i => (B.rank_lt_parent hpp i).trans_le hp⟩
    · have he : Even (Fintype.card {i // i ∈ P.remainingChildren H v}) := by
        simpa only [Fintype.card_coe,hjv] using heven
      obtain ⟨B⟩ := exists_indexedEvenChildBatch {i // i ∈ P.remainingChildren H v} P.frontier hpp he
      exact ⟨B,fun i => (B.rank_lt_parent hpp i).trans_le hp⟩

/-- A least-index unassigned edge always has an already assigned parent. -/
theorem PartialSeed.exists_pending_child (P : PartialSeed H) (hfull : P.edges ≠ Finset.univ) :
    ∃ c : Fin k, c ∉ P.edges ∧
      (H.parent c=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent c) := by
  classical
  have hn : (Finset.univ \ P.edges).Nonempty := by
    by_contra h
    have hempty : Finset.univ \ P.edges=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hs := Finset.sdiff_eq_empty_iff_subset.mp hempty
    exact hfull (Finset.Subset.antisymm (Finset.subset_univ _) hs)
  obtain ⟨c,hc,hmin⟩ := Finset.exists_min_image (Finset.univ \ P.edges) Fin.val hn
  have hnc : c ∉ P.edges := (Finset.mem_sdiff.mp hc).2
  refine ⟨c,hnc,?_⟩
  have hall : ∀ v : Fin (k+1), v.val<c.val+1 → v=0 ∨ ∃ j ∈ P.edges, j.succ=v := by
    intro v
    refine Fin.cases ?_ (fun j hj => ?_) v
    · intro _; exact Or.inl rfl
    · right
      refine ⟨j,?_,rfl⟩
      by_contra hjnot
      have hm := hmin j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hjnot⟩)
      simp only [Fin.val_succ] at hj
      omega
  exact hall (H.parent c) (H.earlier c)

/-- A fully assigned good partial seed needs no further leaves. -/
theorem PartialSeed.markedCompletion_of_full (P : PartialSeed H)
    {marks : Finset (Fin (k+1))} {δ : ℚ} (hδ : 0 ≤ δ)
    (hfull : P.edges=Finset.univ) (hbound : ∀ x ∈ P.S, x ≤ 1)
    (hgood : P.GoodMarks H marks δ) : Nonempty (P.MarkedCompletion H marks δ) := by
  classical
  let r : Demand k := 0
  let G := Reserves.core H r
  let L := P.reserveLift H r
  have hm (i : Fin k) : i ∈ P.edges := hfull ▸ Finset.mem_univ i
  have hLfull : L.edges=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
    cases e with
    | inl i => exact (P.reserveLift_old_assigned H r i).mpr (hm i)
    | inr l => exact Fin.elim0 l.2
  let R := L.finish G hLfull
  have hrank (v : Fin (k+1)) : R.rank (Reserves.old r v)=P.rank v :=
    P.reserveLift_rank_old H r v
  refine ⟨⟨r,by simp [r],by simp [r],R,fun i _ => hrank i.succ,?_,?_⟩⟩
  · intro v
    obtain ⟨w,rfl⟩ := (ReserveModel.vertexEquiv r).surjective v
    cases w with
    | inl v =>
      rw [ReserveModel.vertexEquiv_old,hrank]
      refine Fin.cases ?_ (fun i => hbound _ (P.assigned i (hm i))) v
      simp [P.root_zero]
    | inr l => exact Fin.elim0 l.2
  · intro v hv
    rw [hrank]
    revert hv
    refine Fin.cases ?_ (fun i hi => hgood i (hm i) hi) v
    intro _
    exact Or.inl (P.root_zero ▸ hδ)

/-- Ordinary filling strictly decreases the combined completion measure. -/
theorem PartialSeed.fillChildren_measure (P : PartialSeed H) (marks : Finset (Fin (k+1)))
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    (hne : (P.remainingChildren H v).Nonempty) :
    (k-(P.fillChildren H v hv B).edges.card)+
      ((P.fillChildren H v hv B).missingMarks H marks).card <
      (k-P.edges.card)+(P.missingMarks H marks).card := by
  have hcard : (P.fillChildren H v hv B).edges.card=
      P.edges.card+(P.remainingChildren H v).card := by
    rw [PartialSeed.fillChildren_edges,
      Finset.card_union_of_disjoint (P.remainingChildren_disjoint H v)]
  have hpos := Finset.card_pos.mpr hne
  have hle : (P.fillChildren H v hv B).edges.card ≤ k := by
    simpa using Finset.card_le_card (Finset.subset_univ (P.fillChildren H v hv B).edges)
  have hmarks : (P.fillChildren H v hv B).missingMarks H marks ⊆ P.missingMarks H marks := by
    intro i hi
    rw [PartialSeed.mem_missingMarks] at hi ⊢
    refine ⟨hi.1,?_⟩
    intro h
    exact hi.2 (Finset.mem_union_left _ h)
  have hmle := Finset.card_le_card hmarks
  omega

/-- A completed extension after ordinary filling also completes the original
partial seed, because previously assigned ranks are unchanged. -/
noncomputable def PartialSeed.MarkedCompletion.of_fillChildren (P : PartialSeed H)
    {marks : Finset (Fin (k+1))} {δ : ℚ} (v : Fin (k+1))
    (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    (C : (P.fillChildren H v hv B).MarkedCompletion H marks δ) : P.MarkedCompletion H marks δ where
  reserves := C.reserves
  even := C.even
  support := C.support
  seed := C.seed
  old_rank i hi := (C.old_rank i (Finset.mem_union_left _ hi)).trans (P.fillChildren_old H v hv B hi)
  bounded := C.bounded
  marked := C.marked

/-- Prime expansion makes precisely its newly assigned marked child low;
existing marked ranks are unchanged, and the new leaves are not marks. -/
theorem PartialSeed.PrimeExtension.goodMarks {P : PartialSeed H} {c : Fin k} {δ : ℚ}
    (E : P.PrimeExtension H c δ) (marks : Finset (Fin (k+1)))
    (hgood : P.GoodMarks H marks δ) :
    E.seed.GoodMarks (Reserves.core H (PrimeExtension.reserves c E.n))
      (marks.image (Reserves.old (PrimeExtension.reserves c E.n))) δ := by
  let r := PrimeExtension.reserves c E.n
  intro a ha hm
  obtain ⟨e,rfl⟩ := (ReserveModel.edgeEquiv r).surjective a
  cases e with
  | inl i =>
    simp only [ReserveModel.edgeEquiv_old] at ha hm ⊢
    rw [Reserves.oldEdge_child] at hm ⊢
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    have heq : v=i.succ := (PrimeMeasure.old_inj r).mp he
    subst v
    rcases (E.old_assigned i).mp ha with hi | rfl
    · rw [E.assigned_rank i hi]
      exact hgood i hi hv
    · exact Or.inl E.child_small.le
  | inr l =>
    simp only [ReserveModel.edgeEquiv_added,Reserves.addedEdge_child] at hm
    obtain ⟨v,_,he⟩ := Finset.mem_image.mp hm
    exact False.elim (PrimeMeasure.old_ne_added r v l he)

theorem PartialSeed.PrimeExtension.bounded {P : PartialSeed H} {c : Fin k} {ε : ℚ}
    (E : P.PrimeExtension H c ε) (hp : 0 < P.rank (H.parent c))
    (hparent : P.rank (H.parent c) ∈ P.A) (hbound : ∀ x ∈ P.S, x ≤ 1) :
    ∀ x ∈ E.seed.S, x ≤ 1 := by
  have hb := hbound _ (P.frontier.subset hparent)
  intro x hx
  rw [E.S_eq] at hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact hbound x hx
  · exact (PrimeBatch.rank_lt_parent hp E.n i).le.trans hb

/-- Flatten the supported even reserves accumulated after a prime step. -/
noncomputable def PartialSeed.MarkedCompletion.of_prime {P : PartialSeed H} {c : Fin k}
    {marks : Finset (Fin (k+1))} {δ : ℚ} (E : P.PrimeExtension H c δ)
    (hc : c.succ ∈ marks)
    (C : E.seed.MarkedCompletion (Reserves.core H (PrimeExtension.reserves c E.n))
      (marks.image (Reserves.old (PrimeExtension.reserves c E.n))) δ) :
    P.MarkedCompletion H marks δ := by
  classical
  let r := PrimeExtension.reserves c E.n
  have hs : ∀ l : Leaf r, C.reserves (Reserves.added r l)=0 := by
    intro l
    apply C.support
    intro h
    obtain ⟨v,_,he⟩ := Finset.mem_image.mp h
    exact PrimeMeasure.old_ne_added r v l he
  let e := ReserveComposition.flatten H r C.reserves hs
  have he0 : e.vertex 0=0 := ReserveComposition.flatten_root H r C.reserves hs
  let R := C.seed.transport e he0
  have hr (v : Fin (k+1)) :
      R.rank (Reserves.old (ReserveComposition.flat r C.reserves) v)=
        C.seed.rank (Reserves.old C.reserves (Reserves.old r v)) := by
    rw [← ReserveComposition.flatten_old H r C.reserves hs]
    exact C.seed.transport_rank e he0 _
  refine ⟨ReserveComposition.flat r C.reserves,?_,?_,R,?_,?_,?_⟩
  · exact ReserveComposition.even_flat r C.reserves E.reserve_even C.even
  · intro v hv
    have hvc : v ≠ c.succ := fun h => hv (h ▸ hc)
    have hrzero : r v=0 := PrimeExtension.reserves_away c E.n hvc
    have hczero : C.reserves (Reserves.old r v)=0 := by
      apply C.support
      intro h
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      exact hv ((PrimeMeasure.old_inj r).mp he ▸ hw)
    simp [ReserveComposition.flat,hrzero,hczero]
  · intro i hi
    rw [hr]
    have h := C.old_rank (Reserves.oldEdge r i) ((E.old_assigned i).mpr (Or.inl hi))
    rw [Reserves.oldEdge_child] at h
    exact h.trans (E.assigned_rank i hi)
  · intro v
    exact C.bounded (e.vertex.symm v)
  · intro v hv
    rw [hr]
    exact C.marked (Reserves.old r v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

/-- Strong-induction engine for the full marked completion. A prime step
keeps the number of unassigned edges fixed and removes one missing mark; an
ordinary step strictly decreases the number of unassigned edges. -/
theorem completeMarkedAux (n : ℕ) :
    ∀ {k : ℕ} (H : Core k) (P : PartialSeed H) (marks : Finset (Fin (k+1))) (δ : ℚ),
      0 < δ → δ ≤ 1 → P.OrdinaryReady H → P.InactiveLow H δ →
      (∀ x ∈ P.S, x ≤ 1) → P.GoodMarks H marks δ →
      (k-P.edges.card)+(P.missingMarks H marks).card=n →
      Nonempty (P.MarkedCompletion H marks δ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k H P marks δ hδ hδone hready hLow hbound hgood hn
    by_cases hfull : P.edges=Finset.univ
    · exact P.markedCompletion_of_full H hδ.le hfull hbound hgood
    obtain ⟨c,hc,hparent⟩ := P.exists_pending_child H hfull
    let v := H.parent c
    have hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v := hparent
    have hne : (P.remainingChildren H v).Nonempty :=
      ⟨c,(P.mem_remainingChildren H v c).mpr ⟨rfl,hc⟩⟩
    by_cases hpLow : P.rank v ≤ δ
    · obtain ⟨B,hB⟩ := P.exists_lowBatch H hready v hv hδ hpLow
      let T := P.fillChildren H v hv B
      have hTb : ∀ x ∈ T.S, x ≤ 1 := by
        intro x hx
        change x ∈ P.S ∪ range B.rank at hx
        rcases hx with hx | ⟨i,rfl⟩
        · exact hbound x hx
        · exact (hB i).le.trans hδone
      have hTg : T.GoodMarks H marks δ :=
        P.fillChildren_goodMarks H hgood v hv B (fun i _ => (hB i).le)
      have hm : (k-T.edges.card)+(T.missingMarks H marks).card<n := by
        rw [← hn]
        exact P.fillChildren_measure H marks v hv B hne
      obtain ⟨C⟩ := ih _ hm H T marks δ hδ hδone
        (P.fillChildren_ready H hready v hv B)
        (P.fillChildren_inactiveLow H hLow v hv B) hTb hTg rfl
      exact ⟨PartialSeed.MarkedCompletion.of_fillChildren H P v hv B C⟩
    · have hpHigh : δ < P.rank v := lt_of_not_ge hpLow
      by_cases hmarked : ∃ d ∈ P.remainingChildren H v, d.succ ∈ marks
      · obtain ⟨d,hd,hdmark⟩ := hmarked
        have hdi := (P.mem_remainingChildren H v d).mp hd
        have hdp : H.parent d=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent d := by
          rw [hdi.1]; exact hv
        have hdh : δ < P.rank (H.parent d) := by rw [hdi.1]; exact hpHigh
        have hdpPos : 0 < P.rank (H.parent d) := hδ.trans hdh
        have hdactive := P.parent_active_of_nonlow H hδ.le hLow d hdi.2 hdp hdh
        obtain ⟨E⟩ := P.exists_primeExtension H d hdi.2 hdp hdpPos hδ
        let r := PrimeExtension.reserves d E.n
        let G := Reserves.core H r
        let marks' := marks.image (Reserves.old r)
        have hm : ((k+total r)-E.seed.edges.card)+
            (E.seed.missingMarks G marks').card<n := by
          rw [← hn]
          exact E.measure_decreases marks hdmark
        obtain ⟨C⟩ := ih _ hm G E.seed marks' δ hδ hδone
          (E.ordinaryReady H hready hdactive) (E.inactiveLow H hLow hdactive)
          (E.bounded H hdpPos hdactive hbound) (E.goodMarks H marks hgood) rfl
        exact ⟨PartialSeed.MarkedCompletion.of_prime H E hdmark C⟩
      · obtain ⟨B,hB⟩ := P.exists_completionBatch H hready v hv (by norm_num : (0:ℚ)<1) hbound
        let T := P.fillChildren H v hv B
        have hTb : ∀ x ∈ T.S, x ≤ 1 := by
          intro x hx
          change x ∈ P.S ∪ range B.rank at hx
          rcases hx with hx | ⟨i,rfl⟩
          · exact hbound x hx
          · exact hB i
        have hTg : T.GoodMarks H marks δ := by
          apply P.fillChildren_goodMarks H hgood v hv B
          intro i hi
          exact False.elim (hmarked ⟨i.val,i.property,hi⟩)
        have hm : (k-T.edges.card)+(T.missingMarks H marks).card<n := by
          rw [← hn]
          exact P.fillChildren_measure H marks v hv B hne
        obtain ⟨C⟩ := ih _ hm H T marks δ hδ hδone
          (P.fillChildren_ready H hready v hv B)
          (P.fillChildren_inactiveLow H hLow v hv B) hTb hTg rfl
        exact ⟨PartialSeed.MarkedCompletion.of_fillChildren H P v hv B C⟩

/-- Complete a prepared actual subtree, adding even leaves only at marked
vertices. No local gadget, termination, or reserve-composition assumptions are
left implicit in this theorem. -/
theorem PartialSeed.completeMarked (P : PartialSeed H) (marks : Finset (Fin (k+1)))
    {δ : ℚ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hready : P.OrdinaryReady H) (hLow : P.InactiveLow H δ)
    (hbound : ∀ x ∈ P.S, x ≤ 1) (hgood : P.GoodMarks H marks δ) :
    Nonempty (P.MarkedCompletion H marks δ) :=
  completeMarkedAux _ H P marks δ hδ hδone hready hLow hbound hgood rfl

#print axioms PartialSeed.exists_pending_child
#print axioms PartialSeed.markedCompletion_of_full
#print axioms PartialSeed.fillChildren_measure
#print axioms PartialSeed.MarkedCompletion.of_prime
#print axioms PartialSeed.completeMarked
end FixedCore.Next
