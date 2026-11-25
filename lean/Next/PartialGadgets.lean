import Next.PartialSeed

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Insert the triple gadget along three actual consecutive unassigned edges.
Its first parent is already assigned, and all three new vertices stay active. -/
theorem PartialSeed.exists_tripleBlock (P : PartialSeed H) (a b c : Fin k)
    (hb : H.parent b = a.succ) (hc : H.parent c = b.succ)
    (ha : H.parent a = 0 ∨ ∃ j ∈ P.edges, j.succ = H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges)
    (hp : 0 < P.rank (H.parent a)) {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℚ, ∃ B : P.Block H,
      0 < t ∧ t < ε ∧ 8*t < P.rank (H.parent a) ∧ B.edges = {a,b,c} ∧
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
  obtain ⟨t,ht,hte,htp,hf,hs,hfresh,hfront,hcons,hdev⟩ :=
    P.frontier.exists_triple hp hε
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
      apply hfresh (r i)
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
  refine ⟨t,B,ht,hte,htp,rfl,rfl,?_,?_,?_⟩
  · change P.updatedRank H Q r qa.val.succ=t
    rw [P.updatedRank_new H Q r qa,ra]
  · change P.updatedRank H Q r qb.val.succ=p-t
    rw [P.updatedRank_new H Q r qb,rb]
  · change P.updatedRank H Q r qc.val.succ=p-2*t
    rw [P.updatedRank_new H Q r qc,rc]

/-- Insert the quartet along four actual unassigned path edges. Its second
vertex is excluded from singleton-active ranks and must use even child batches. -/
theorem PartialSeed.exists_quartetBlock (P : PartialSeed H) (a b c d : Fin k)
    (hb : H.parent b = a.succ) (hc : H.parent c = b.succ) (hd : H.parent d = c.succ)
    (ha : H.parent a = 0 ∨ ∃ j ∈ P.edges, j.succ = H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges) (hnd : d ∉ P.edges)
    (hp : 0 < P.rank (H.parent a)) {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℚ, ∃ B : P.Block H,
      0 < t ∧ t < ε ∧ 8*t < P.rank (H.parent a) ∧ B.edges = {a,b,c,d} ∧
      B.A = P.A ∪ {t,P.rank (H.parent a)-t,P.rank (H.parent a)-3*t} ∧
      2*t ∉ B.A ∧
      (P.extend H B).rank a.succ = t ∧
      (P.extend H B).rank b.succ = 2*t ∧
      (P.extend H B).rank c.succ = P.rank (H.parent a)-t ∧
      (P.extend H B).rank d.succ = P.rank (H.parent a)-3*t := by
  classical
  have habv : a.val < b.val := by have := H.earlier b; rw [hb] at this; simpa using this
  have hbcv : b.val < c.val := by have := H.earlier c; rw [hc] at this; simpa using this
  have hcdv : c.val < d.val := by have := H.earlier d; rw [hd] at this; simpa using this
  have hab : a ≠ b := by intro h; subst b; omega
  have hac : a ≠ c := by intro h; subst c; omega
  have had : a ≠ d := by intro h; subst d; omega
  have hbc : b ≠ c := by intro h; subst c; omega
  have hbd : b ≠ d := by intro h; subst d; omega
  have hcd : c ≠ d := by intro h; subst d; omega
  let p := P.rank (H.parent a)
  obtain ⟨t,ht,hte,htp,hf,hs,hfresh,hfront,hcons,hdev⟩ :=
    P.frontier.exists_quartet hp hε
  let Q : Finset (Fin k) := {a,b,c,d}
  let qa : {i // i ∈ Q} := ⟨a,by simp [Q]⟩
  let qb : {i // i ∈ Q} := ⟨b,by simp [Q]⟩
  let qc : {i // i ∈ Q} := ⟨c,by simp [Q]⟩
  let qd : {i // i ∈ Q} := ⟨d,by simp [Q]⟩
  have hab' : qa ≠ qb := fun h => hab (congrArg Subtype.val h)
  have hac' : qa ≠ qc := fun h => hac (congrArg Subtype.val h)
  have had' : qa ≠ qd := fun h => had (congrArg Subtype.val h)
  have hbc' : qb ≠ qc := fun h => hbc (congrArg Subtype.val h)
  have hbd' : qb ≠ qd := fun h => hbd (congrArg Subtype.val h)
  have hcd' : qc ≠ qd := fun h => hcd (congrArg Subtype.val h)
  let r : {i // i ∈ Q} → ℚ := fun i =>
    if i.val=a then t else if i.val=b then 2*t else if i.val=c then p-t else p-3*t
  have casesQ (i : {i // i ∈ Q}) : i=qa ∨ i=qb ∨ i=qc ∨ i=qd := by
    have hi := i.property
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Or.inl (Subtype.ext hi))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext hi)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext hi)))
  have ra : r qa=t := by simp [r,qa]
  have rb : r qb=2*t := by simp [r,qb,Ne.symm hab]
  have rc : r qc=p-t := by simp [r,qc,Ne.symm hac,Ne.symm hbc]
  have rd : r qd=p-3*t := by simp [r,qd,Ne.symm had,Ne.symm hbd,Ne.symm hcd]
  have hrange : range r = ({t,2*t,p-t,p-3*t} : Set ℚ) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      rcases casesQ i with rfl | rfl | rfl | rfl <;> simp [ra,rb,rc,rd]
    · intro hx
      simp only [mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with h | h | h | h
      · exact ⟨qa,ra.trans h.symm⟩
      · exact ⟨qb,rb.trans h.symm⟩
      · exact ⟨qc,rc.trans h.symm⟩
      · exact ⟨qd,rd.trans h.symm⟩
  have hdis : Disjoint P.edges Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hq
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hna hi
    · exact hnb hi
    · exact hnc hi
    · exact hnd hi
  let e : Equiv.Perm {i // i ∈ Q} :=
    (Equiv.swap qa qc).trans ((Equiv.swap qa qd).trans (Equiv.swap qa qb))
  have ea : e qa=qc := by
    simp [e,Equiv.swap_apply_def,hac'.symm,hcd',hbc'.symm]
  have eb : e qb=qa := by
    simp [e,Equiv.swap_apply_def,hab'.symm,hbc',hbd']
  have ec : e qc=qd := by
    simp [e,Equiv.swap_apply_def,had'.symm,hbd'.symm]
  have ed : e qd=qb := by
    simp [e,Equiv.swap_apply_def,had'.symm,hcd'.symm]
  have hpa : P.updatedRank H Q r (H.parent a)=p := by
    rcases ha with h | ⟨j,hj,h⟩
    · rw [h,PartialSeed.updatedRank_zero]
      exact (h ▸ P.root_zero).symm
    · change P.updatedRank H Q r (H.parent a)=P.rank (H.parent a)
      rw [← h]
      exact P.updatedRank_old H Q r hdis hj
  have hpb : P.updatedRank H Q r (H.parent b)=t := by
    rw [hb, show a.succ=qa.val.succ from rfl, P.updatedRank_new H Q r qa,ra]
  have hpc : P.updatedRank H Q r (H.parent c)=2*t := by
    rw [hc, show b.succ=qb.val.succ from rfl, P.updatedRank_new H Q r qb,rb]
  have hpd : P.updatedRank H Q r (H.parent d)=p-t := by
    rw [hd, show c.succ=qc.val.succ from rfl, P.updatedRank_new H Q r qc,rc]
  let B : P.Block H := {
    edges := Q
    disjoint := hdis
    rank := r
    positive := by
      intro i
      rcases casesQ i with rfl | rfl | rfl | rfl <;>
        simp only [ra,rb,rc,rd] <;> (try dsimp [p]) <;> linarith
    injective := by
      intro i j hij
      rcases casesQ i with rfl | rfl | rfl | rfl <;>
        rcases casesQ j with rfl | rfl | rfl | rfl
      all_goals first | rfl | (simp only [ra,rb,rc,rd,p] at hij; exfalso; linarith)
    fresh := by
      intro i
      apply hfresh (r i)
      rw [← hrange]
      exact ⟨i,rfl⟩
    closed := by
      intro i hi
      have hcases := casesQ ⟨i,hi⟩
      rcases hcases with h | h | h | h
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
      · have he : i=d := congrArg Subtype.val h
        subst i
        exact Or.inr ⟨c,by simp [Q],hd.symm⟩
    permutation := e
    edge_difference := by
      intro i
      rcases casesQ i with rfl | rfl | rfl | rfl
      · rw [ea,ra,rc,hpa]
        exact abs_of_pos (by dsimp [p]; linarith)
      · rw [eb,rb,ra,hpb,abs_of_nonpos (by linarith)]
        ring
      · rw [ec,rc,rd,hpc,abs_of_nonpos (by dsimp [p]; linarith)]
        ring
      · rw [ed,rd,rb,hpd,abs_of_nonneg (by linarith)]
        ring
    A := P.A ∪ {t,p-t,p-3*t}
    frontier := by simpa [hrange,p] using hfront
  }
  refine ⟨t,B,ht,hte,htp,rfl,rfl,?_,?_,?_,?_,?_⟩
  · exact quartet_double_not_active P.frontier ht htp hf
  · change P.updatedRank H Q r qa.val.succ=t
    rw [P.updatedRank_new H Q r qa,ra]
  · change P.updatedRank H Q r qb.val.succ=2*t
    rw [P.updatedRank_new H Q r qb,rb]
  · change P.updatedRank H Q r qc.val.succ=p-t
    rw [P.updatedRank_new H Q r qc,rc]
  · change P.updatedRank H Q r qd.val.succ=p-3*t
    rw [P.updatedRank_new H Q r qd,rd]

#print axioms PartialSeed.exists_tripleBlock
#print axioms PartialSeed.exists_quartetBlock
end FixedCore.Next
