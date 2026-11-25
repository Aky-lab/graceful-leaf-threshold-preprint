import Next.PartialSeed
import Next.BoundedDepthBatches
import Next.BoundedDepthExtension

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Insert a prescribed separated triple along three actual consecutive edges.
The parameter is supplied by a quantitative finite exclusion lemma, rather
than by an arbitrarily small rational choice. -/
theorem PartialSeed.exists_prescribedTripleBlock (P : PartialSeed H) (a b c : Fin k)
    (hb : H.parent b = a.succ) (hc : H.parent c = b.succ)
    (ha : H.parent a = 0 ∨ ∃ j ∈ P.edges, j.succ = H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges)
    (t : ℚ) (ht : 0 < t) (htp : 3*t < P.rank (H.parent a))
    (hf : ∀ x ∈ P.S, ¬ Dyadic t x)
    (hg : ∀ x ∈ P.S, ¬ Dyadic (P.rank (H.parent a)-t) x)
    (hh : ∀ x ∈ P.S, ¬ Dyadic (P.rank (H.parent a)-2*t) x)
    (hfg : ¬ Dyadic t (P.rank (H.parent a)-t))
    (hfh : ¬ Dyadic t (P.rank (H.parent a)-2*t))
    (hgh : ¬ Dyadic (P.rank (H.parent a)-t) (P.rank (H.parent a)-2*t)) :
    ∃ B : P.Block H,
      B.edges = {a,b,c} ∧
      B.A = P.A ∪ {t,P.rank (H.parent a)-t,P.rank (H.parent a)-2*t} ∧
      (P.extend H B).rank a.succ = t ∧
      (P.extend H B).rank b.succ = P.rank (H.parent a)-t ∧
      (P.extend H B).rank c.succ = P.rank (H.parent a)-2*t := by
  classical
  have habv : a.val < b.val := by have := H.earlier b; rw [hb] at this; simpa using this
  have hbcv : b.val < c.val := by have := H.earlier c; rw [hc] at this; simpa using this
  have hab : a ≠ b := by intro h; subst b; omega
  have hbc : b ≠ c := by intro h; subst c; omega
  have hac : a ≠ c := by intro h; subst c; omega
  let p := P.rank (H.parent a)
  have hgood : ∀ x ∈ ({t,p-t,p-2*t} : Set ℚ), 0 < x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> (try dsimp [p]) <;> linarith
  have hfresh : Disjoint ({t,p-t,p-2*t} : Set ℚ) P.S := by
    apply Set.disjoint_left.mpr
    intro x hx hxS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hf _ hxS (Dyadic.refl _)
    · exact hg _ hxS (Dyadic.refl _)
    · exact hh _ hxS (Dyadic.refl _)
  have hfront : SeedFrontier (P.S ∪ {t,p-t,p-2*t}) (P.A ∪ {t,p-t,p-2*t}) := by
    have F₁ := P.frontier.adjoin ht hf
    have F₂ := F₁.adjoin (hgood _ (by simp)) (show ∀ x ∈ insert t P.S, ¬ Dyadic (p-t) x from by
      intro x hx hd
      rcases hx with rfl | hx
      · exact hfg hd.symm
      · exact hg _ hx hd)
    have F₃ := F₂.adjoin (hgood _ (by simp)) (show ∀ x ∈ insert (p-t) (insert t P.S), ¬ Dyadic (p-2*t) x from by
      intro x hx hd
      rcases hx with rfl | rfl | hx
      · exact hgh hd.symm
      · exact hfh hd.symm
      · exact hh _ hx hd)
    convert F₃ using 1 <;> ext x <;> simp only [mem_union, mem_insert_iff, mem_singleton_iff] <;> tauto
  let Q : Finset (Fin k) := {a,b,c}
  let qa : {i // i ∈ Q} := ⟨a,by simp [Q]⟩
  let qb : {i // i ∈ Q} := ⟨b,by simp [Q]⟩
  let qc : {i // i ∈ Q} := ⟨c,by simp [Q]⟩
  have hab' : qa ≠ qb := fun h => hab (congrArg Subtype.val h)
  have hbc' : qb ≠ qc := fun h => hbc (congrArg Subtype.val h)
  have hac' : qa ≠ qc := fun h => hac (congrArg Subtype.val h)
  let r : {i // i ∈ Q} → ℚ := fun i => if i.val=a then t else if i.val=b then p-t else p-2*t
  have casesQ (i : {i // i ∈ Q}) : i=qa ∨ i=qb ∨ i=qc := by
    have hi := i.property
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Or.inl (Subtype.ext hi))
    · exact Or.inr (Or.inr (Subtype.ext hi))
  have ra : r qa=t := by simp [r,qa]
  have rb : r qb=p-t := by simp [r,qb,Ne.symm hab]
  have rc : r qc=p-2*t := by simp [r,qc,Ne.symm hac,Ne.symm hbc]
  have hrange : range r = ({t,p-t,p-2*t} : Set ℚ) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      rcases casesQ i with rfl | rfl | rfl <;> simp [ra,rb,rc]
    · intro hx
      simp only [mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with h | h | h
      · exact ⟨qa,ra.trans h.symm⟩
      · exact ⟨qb,rb.trans h.symm⟩
      · exact ⟨qc,rc.trans h.symm⟩
  have hd : Disjoint P.edges Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hq
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hna hi
    · exact hnb hi
    · exact hnc hi
  let e : Equiv.Perm {i // i ∈ Q} := (Equiv.swap qb qc).trans (Equiv.swap qa qb)
  have ea : e qa=qb := by
    change (Equiv.swap qa qb) ((Equiv.swap qb qc) qa)=qb
    rw [Equiv.swap_apply_of_ne_of_ne hab' hac', Equiv.swap_apply_left]
  have eb : e qb=qc := by
    change (Equiv.swap qa qb) ((Equiv.swap qb qc) qb)=qc
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hac'.symm hbc'.symm]
  have ec : e qc=qa := by
    change (Equiv.swap qa qb) ((Equiv.swap qb qc) qc)=qa
    rw [Equiv.swap_apply_right,Equiv.swap_apply_right]
  have hpa : P.updatedRank H Q r (H.parent a)=p := by
    rcases ha with h | ⟨j,hj,h⟩
    · rw [h,PartialSeed.updatedRank_zero]
      exact (h ▸ P.root_zero).symm
    · change P.updatedRank H Q r (H.parent a)=P.rank (H.parent a)
      rw [← h]
      exact P.updatedRank_old H Q r hd hj
  have hpb : P.updatedRank H Q r (H.parent b)=t := by
    rw [hb, show a.succ=qa.val.succ from rfl, P.updatedRank_new H Q r qa,ra]
  have hpc : P.updatedRank H Q r (H.parent c)=p-t := by
    rw [hc, show b.succ=qb.val.succ from rfl, P.updatedRank_new H Q r qb,rb]
  let B : P.Block H := {
    edges := Q
    disjoint := hd
    rank := r
    positive := by
      intro i
      rcases casesQ i with rfl | rfl | rfl <;> simp only [ra,rb,rc] <;> (try dsimp [p]) <;> linarith
    injective := by
      intro i j hij
      rcases casesQ i with rfl | rfl | rfl <;> rcases casesQ j with rfl | rfl | rfl
      all_goals first | rfl | (simp only [ra,rb,rc] at hij; dsimp [p] at hij; exfalso; linarith)
    fresh := by
      intro i
      apply Set.disjoint_left.mp hfresh
      rw [← hrange]
      exact ⟨i,rfl⟩
    closed := by
      intro i hi
      have hcases := casesQ ⟨i,hi⟩
      rcases hcases with h | h | h
      · have he : i=a := congrArg Subtype.val h
        subst i
        rcases ha with h | ⟨j,hj,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j,Finset.mem_union_left _ hj,h⟩
      · have he : i=b := congrArg Subtype.val h
        subst i
        exact Or.inr ⟨a,by simp [Q],hb.symm⟩
      · have he : i=c := congrArg Subtype.val h
        subst i
        exact Or.inr ⟨b,by simp [Q],hc.symm⟩
    permutation := e
    edge_difference := by
      intro i
      rcases casesQ i with rfl | rfl | rfl
      · rw [ea,ra,rb,hpa]
        exact abs_of_pos (by dsimp [p]; linarith)
      · rw [eb,rb,rc,hpb]
        rw [abs_of_nonpos (by dsimp [p]; linarith)]
        ring
      · rw [ec,rc,ra,hpc]
        have h : p-t-(p-2*t)=t := by ring
        rw [h,abs_of_pos ht]
    A := P.A ∪ {t,p-t,p-2*t}
    frontier := by simpa [hrange,p] using hfront
  }
  refine ⟨B,rfl,rfl,?_,?_,?_⟩
  · change P.updatedRank H Q r qa.val.succ=t
    rw [P.updatedRank_new H Q r qa,ra]
  · change P.updatedRank H Q r qb.val.succ=p-t
    rw [P.updatedRank_new H Q r qb,rb]
  · change P.updatedRank H Q r qc.val.succ=p-2*t
    rw [P.updatedRank_new H Q r qc,rc]


/-- Extending with a real block never introduces auxiliary occupied ranks. -/
theorem PartialSeed.extend_exactAssigned (P : PartialSeed H)
    (hP : BoundedDepth.ExactAssigned H P) (B : P.Block H) :
    BoundedDepth.ExactAssigned H (P.extend H B) := by
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · obtain ⟨i,hi,rfl⟩ := hP x hx
    exact ⟨i, Finset.mem_union_left _ hi, P.updatedRank_old H B.edges B.rank B.disjoint hi⟩
  · exact ⟨i.val, Finset.mem_union_right _ i.property,
      P.updatedRank_new H B.edges B.rank i⟩

/-- Every old vertex, including zero, retains its rank after a block. -/
theorem PartialSeed.extend_oldVertex (P : PartialSeed H) (B : P.Block H)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ i∈P.edges, i.succ=v) :
    (P.extend H B).rank v=P.rank v := by
  rcases hv with rfl | ⟨i,hi,rfl⟩
  · simp [P.root_zero]
  · exact P.updatedRank_old H B.edges B.rank B.disjoint hi

/-- Range bounds on a block and the old labels give the same global bound. -/
theorem PartialSeed.extend_range (P : PartialSeed H) (B : P.Block H) {l u : ℚ}
    (hP : P.S ⊆ Set.Icc l u) (hB : ∀ i, B.rank i ∈ Set.Icc l u) :
    (P.extend H B).S ⊆ Set.Icc l u := by
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact hP hx
  · exact hB i

/-- Unknown members of a prescribed block can be recognized from the three
explicit new ranks; useful when transporting quantitative bounds. -/
theorem PartialSeed.triple_rank_cases (P : PartialSeed H) (B : P.Block H)
    (a b c : Fin k) (he : B.edges={a,b,c}) (x : ℚ)
    (hx : x ∈ (P.extend H B).S) :
    x ∈ P.S ∨ x=(P.extend H B).rank a.succ ∨
      x=(P.extend H B).rank b.succ ∨ x=(P.extend H B).rank c.succ := by
  classical
  rcases hx with hx | ⟨i,rfl⟩
  · exact Or.inl hx
  · have hi : i.val=a ∨ i.val=b ∨ i.val=c := by
      simpa [he] using i.property
    have hr : B.rank i=(P.extend H B).rank i.val.succ :=
      (P.updatedRank_new H B.edges B.rank i).symm
    rcases hi with h | h | h <;> simp [hr,h]

#print axioms PartialSeed.exists_prescribedTripleBlock
#print axioms PartialSeed.extend_exactAssigned
end FixedCore.Next
