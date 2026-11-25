import Next.PartialGadgets
import Next.PartialChildren
import Next.CorePaths

/-! Actual-graph initial path construction for the preparation lemma. -/
namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- The one-edge anchor at the root. -/
noncomputable def PartialSeed.anchor (a : Fin k) (ha : H.parent a = 0) : PartialSeed H := by
  classical
  refine {
    edges := {a}
    rank := Fin.cases 0 (fun i => if i=a then 1 else 0)
    root_zero := rfl
    positive := ?_
    injective := ?_
    closed := ?_
    permutation := Equiv.refl _
    fixes := by simp
    maps := by simp
    edge_difference := ?_
    S := {1}
    A := {1}
    frontier := ?_
    assigned := ?_
  }
  · intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp
  · intro i hi j hj _; simp only [Finset.mem_singleton] at hi hj; exact hi.trans hj.symm
  · intro i hi; simp only [Finset.mem_singleton] at hi; subst i; exact Or.inl ha
  · intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp [ha]
  · refine ⟨finite_singleton _, ?_, fun _ h => h, ?_⟩
    · intro x hx; simp only [mem_singleton_iff] at hx; subst x; norm_num
    · intro x hx y hy _; simp only [mem_singleton_iff] at hx hy; subst x; subst y; rfl
  · intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp

@[simp] theorem PartialSeed.anchor_edges (a : Fin k) (ha : H.parent a=0) :
    (PartialSeed.anchor H a ha).edges={a} := rfl
@[simp] theorem PartialSeed.anchor_rank (a : Fin k) (ha : H.parent a=0) :
    (PartialSeed.anchor H a ha).rank a.succ=1 := by simp [PartialSeed.anchor]
@[simp] theorem PartialSeed.anchor_S (a : Fin k) (ha : H.parent a=0) :
    (PartialSeed.anchor H a ha).S={1} := rfl
@[simp] theorem PartialSeed.anchor_A (a : Fin k) (ha : H.parent a=0) :
    (PartialSeed.anchor H a ha).A={1} := rfl

/-- A child of an unassigned nonroot vertex is unassigned. -/
theorem PartialSeed.child_unassigned (P : PartialSeed H) {i j : Fin k}
    (hi : i ∉ P.edges) (hp : H.parent j=i.succ) : j ∉ P.edges := by
  intro hj
  rcases P.closed j hj with h | ⟨a,ha,h⟩
  · rw [hp] at h; exact Fin.succ_ne_zero _ h
  · rw [hp] at h
    exact hi (Fin.succ_injective _ h ▸ ha)

/-- Quantitative endpoint bands on all seed ranks, with a unit ceiling. -/
def PartialSeed.PathBands (P : PartialSeed H) (δ : ℚ) : Prop :=
  ∀ x ∈ P.S, x ≤ 1 ∧ (x ≤ δ ∨ 1-δ ≤ x)

/-- Every assigned vertex is singleton-active. -/
def PartialSeed.AllActive (P : PartialSeed H) : Prop :=
  ∀ i ∈ P.edges, P.rank i.succ ∈ P.A

/-- The only allowed inactive vertices are low and have an even residual fiber. -/
def PartialSeed.PathReady (P : PartialSeed H) (δ : ℚ) : Prop :=
  ∀ i ∈ P.edges, P.rank i.succ ∈ P.A ∨
    (P.rank i.succ ≤ δ ∧ Even (P.remainingChildren H i.succ).card)

/-- Extension bookkeeping needed when composing path gadgets. -/
structure PartialSeed.PathExtension (P Q : PartialSeed H) : Prop where
  edges : P.edges ⊆ Q.edges
  rank : ∀ i ∈ P.edges, Q.rank i.succ=P.rank i.succ
  active : P.A ⊆ Q.A

theorem PartialSeed.PathExtension.refl (P : PartialSeed H) : P.PathExtension H P :=
  ⟨fun _ h => h, fun _ _ => rfl, fun _ h => h⟩

theorem PartialSeed.PathExtension.trans {P Q R : PartialSeed H}
    (hPQ : P.PathExtension H Q) (hQR : Q.PathExtension H R) : P.PathExtension H R := by
  refine ⟨fun i hi => hQR.edges (hPQ.edges hi), ?_, fun x hx => hQR.active (hPQ.active hx)⟩
  intro i hi
  exact (hQR.rank i (hPQ.edges hi)).trans (hPQ.rank i hi)

theorem PartialSeed.PathBands.mono {P : PartialSeed H} {δ ε : ℚ}
    (h : P.PathBands H δ) (hδε : δ ≤ ε) : P.PathBands H ε := by
  intro x hx
  obtain ⟨hx1,hx⟩ := h x hx
  refine ⟨hx1, ?_⟩
  rcases hx with hx | hx
  · exact Or.inl (hx.trans hδε)
  · right; linarith

theorem PartialSeed.AllActive.ready {P : PartialSeed H} (h : P.AllActive H) (δ : ℚ) :
    P.PathReady H δ := fun i hi => Or.inl (h i hi)

theorem PartialSeed.Block.pathExtension {P : PartialSeed H} (B : P.Block H)
    (hA : P.A ⊆ B.A) : P.PathExtension H (P.extend H B) := by
  refine ⟨Finset.subset_union_left, ?_, hA⟩
  intro i hi
  exact P.updatedRank_old H B.edges B.rank B.disjoint hi

theorem PartialSeed.Block.rank_eq_extended {P : PartialSeed H} (B : P.Block H)
    (i : {i // i ∈ B.edges}) : B.rank i=(P.extend H B).rank i.val.succ := by
  exact (P.updatedRank_new H B.edges B.rank i).symm

/-- Verify bounds on a finite block by its actual vertex ranks. -/
theorem PartialSeed.Block.pathBands {P : PartialSeed H} {δ : ℚ}
    (B : P.Block H) (hP : P.PathBands H δ)
    (hB : ∀ i ∈ B.edges, (P.extend H B).rank i.succ ≤ 1 ∧
      ((P.extend H B).rank i.succ ≤ δ ∨ 1-δ ≤ (P.extend H B).rank i.succ)) :
    (P.extend H B).PathBands H δ := by
  intro x hx
  change x ∈ P.S ∪ range B.rank at hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact hP x hx
  · rw [B.rank_eq_extended H]
    exact hB i.val i.property

/-- Verify activity on a finite block by its actual vertex ranks. -/
theorem PartialSeed.Block.allActive {P : PartialSeed H} (B : P.Block H)
    (hP : P.AllActive H) (hA : P.A ⊆ B.A)
    (hB : ∀ i ∈ B.edges, (P.extend H B).rank i.succ ∈ B.A) :
    (P.extend H B).AllActive H := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · change (P.extend H B).rank i.succ ∈ B.A
    rw [(B.pathExtension H hA).rank i hi]
    exact hA (hP i hi)
  · exact hB i hi


/-- A bounded triple preserves all old active ranks and creates three active
ranks in the slightly widened endpoint bands. -/
theorem PartialSeed.exists_pathTriple (P : PartialSeed H) (a b c : Fin k)
    (hb : H.parent b=a.succ) (hc : H.parent c=b.succ)
    (ha : H.parent a=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges)
    (hactive : P.AllActive H) {β ε : ℚ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbands : P.PathBands H β) (hp : 0 < P.rank (H.parent a))
    (hp1 : P.rank (H.parent a) ≤ 1) (hhigh : 1-β ≤ P.rank (H.parent a)) :
    ∃ t : ℚ, ∃ Q : PartialSeed H,
      P.PathExtension H Q ∧ Q.edges=P.edges ∪ {a,b,c} ∧
      0 < t ∧ t < ε/4 ∧
      Q.rank a.succ=t ∧ Q.rank b.succ=P.rank (H.parent a)-t ∧
      Q.rank c.succ=P.rank (H.parent a)-2*t ∧
      Q.PathBands H (β+ε) ∧ Q.AllActive H := by
  classical
  obtain ⟨t,B,ht,hte,htp,hE,hA,haR,hbR,hcR⟩ :=
    P.exists_tripleBlock H a b c hb hc ha hna hnb hnc hp
      (ε := ε/4) (by positivity)
  have hAsub : P.A ⊆ B.A := by rw [hA]; exact subset_union_left
  have hcoords (i : Fin k) (hi : i ∈ B.edges) :
      (P.extend H B).rank i.succ=t ∨
      (P.extend H B).rank i.succ=P.rank (H.parent a)-t ∨
      (P.extend H B).rank i.succ=P.rank (H.parent a)-2*t := by
    rw [hE] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Or.inl haR
    · exact Or.inr (Or.inl hbR)
    · exact Or.inr (Or.inr hcR)
  refine ⟨t,P.extend H B,B.pathExtension H hAsub,by simp [hE],ht,hte,
    haR,hbR,hcR,?_,?_⟩
  · apply B.pathBands H (hbands.mono H (by linarith))
    intro i hi
    rcases hcoords i hi with hr | hr | hr <;> rw [hr]
    · constructor
      · linarith
      · left; linarith
    · constructor
      · linarith
      · right; linarith
    · constructor
      · linarith
      · right; linarith
  · apply B.allActive H hactive hAsub
    intro i hi
    rw [hA]
    rcases hcoords i hi with hr | hr | hr <;> rw [hr] <;> simp

/-- A nonroot child index is later than its parent index. -/
theorem edge_index_lt {a b : Fin k} (hb : H.parent b=a.succ) : a.val < b.val := by
  have h := H.earlier b
  rw [hb] at h
  simp only [Fin.val_succ] at h
  omega

/-- The quartet's second vertex has exactly its off-path children remaining. -/
theorem PartialSeed.quartet_remaining (P : PartialSeed H) (a b c d : Fin k)
    (hb : H.parent b=a.succ) (hc : H.parent c=b.succ) (hd : H.parent d=c.succ)
    (hnb : b ∉ P.edges) (Q : PartialSeed H)
    (hE : Q.edges=P.edges ∪ {a,b,c,d}) :
    Q.remainingChildren H b.succ=Finset.univ.filter (fun i => H.parent i=b.succ ∧ i≠c) := by
  have hab := edge_index_lt H hb
  have hbc := edge_index_lt H hc
  have hcd := edge_index_lt H hd
  have hna : H.parent a ≠ b.succ := by
    intro h
    have hba := edge_index_lt H h
    omega
  have hnb' : H.parent b ≠ b.succ := by
    intro h
    have := edge_index_lt H h
    omega
  have hnd : H.parent d ≠ b.succ := by
    intro h
    have he := Fin.succ_injective _ (hd.symm.trans h)
    have hv := congrArg Fin.val he
    omega
  ext i
  simp only [PartialSeed.mem_remainingChildren,Finset.mem_filter,Finset.mem_univ,true_and,hE,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hp,hn⟩
    exact ⟨hp,fun he => hn (Or.inr (Or.inr (Or.inr (Or.inl he))))⟩
  · rintro ⟨hp,hn⟩
    refine ⟨hp,?_⟩
    rintro (hi | rfl | rfl | rfl | rfl)
    · exact P.child_unassigned H hnb hp hi
    · exact hna hp
    · exact hnb' hp
    · exact hn rfl
    · exact hnd hp

/-- A terminal quartet is legal precisely when the residual children at its
inactive second vertex are even. Its inactive rank is within the low band. -/
theorem PartialSeed.exists_pathQuartet (P : PartialSeed H) (a b c d : Fin k)
    (hb : H.parent b=a.succ) (hc : H.parent c=b.succ) (hd : H.parent d=c.succ)
    (ha : H.parent a=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges) (hnd : d ∉ P.edges)
    (heven : Even (Finset.univ.filter (fun i => H.parent i=b.succ ∧ i≠c)).card)
    (hactive : P.AllActive H) {β ε : ℚ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbands : P.PathBands H β) (hp : 0 < P.rank (H.parent a))
    (hp1 : P.rank (H.parent a) ≤ 1) (hhigh : 1-β ≤ P.rank (H.parent a)) :
    ∃ Q : PartialSeed H, P.PathExtension H Q ∧ Q.edges=P.edges ∪ {a,b,c,d} ∧
      1-(β+ε) ≤ Q.rank d.succ ∧ Q.PathBands H (β+ε) ∧ Q.PathReady H (β+ε) := by
  classical
  obtain ⟨t,B,ht,hte,htp,hE,hA,hinactive,haR,hbR,hcR,hdR⟩ :=
    P.exists_quartetBlock H a b c d hb hc hd ha hna hnb hnc hnd hp
      (ε := ε/4) (by positivity)
  have hAsub : P.A ⊆ B.A := by rw [hA]; exact subset_union_left
  have hQB : (P.extend H B).edges=P.edges ∪ {a,b,c,d} := by simp [hE]
  have hcoords (i : Fin k) (hi : i ∈ B.edges) :
      (P.extend H B).rank i.succ=t ∨
      (P.extend H B).rank i.succ=2*t ∨
      (P.extend H B).rank i.succ=P.rank (H.parent a)-t ∨
      (P.extend H B).rank i.succ=P.rank (H.parent a)-3*t := by
    rw [hE] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact Or.inl haR
    · exact Or.inr (Or.inl hbR)
    · exact Or.inr (Or.inr (Or.inl hcR))
    · exact Or.inr (Or.inr (Or.inr hdR))
  refine ⟨P.extend H B,B.pathExtension H hAsub,hQB,?_,?_,?_⟩
  · rw [hdR]; linarith
  · apply B.pathBands H (hbands.mono H (by linarith))
    intro i hi
    rcases hcoords i hi with hr | hr | hr | hr <;> rw [hr]
    · constructor
      · linarith
      · left; linarith
    · constructor
      · linarith
      · left; linarith
    · constructor
      · linarith
      · right; linarith
    · constructor
      · linarith
      · right; linarith
  · intro i hi
    rw [hQB] at hi
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi | hi | hi
    · left
      change (P.extend H B).rank i.succ ∈ B.A
      rw [(B.pathExtension H hAsub).rank i hi]
      exact hAsub (hactive i hi)
    · subst i; left; change (P.extend H B).rank a.succ ∈ B.A; rw [haR,hA]; simp
    · subst i; right
      refine ⟨by rw [hbR]; linarith, ?_⟩
      rw [P.quartet_remaining H a b c d hb hc hd hnb _ hQB]
      exact heven
    · subst i; left; change (P.extend H B).rank c.succ ∈ B.A; rw [hcR,hA]; simp
    · subst i; left; change (P.extend H B).rank d.succ ∈ B.A; rw [hdR,hA]; simp


/-- A path construction records its exact edge support, including at most two
specified side edges, rather than assuming an abstract initial certificate. -/
structure PartialSeed.PathBuilt (P : PartialSeed H) (l : List (Fin k))
    (v : Fin k) (δ : ℚ) where
  seed : PartialSeed H
  extra : Finset (Fin k)
  extra_card : extra.card ≤ 2
  extra_parent : ∀ z ∈ extra, ∃ i ∈ l, H.parent z=i.succ
  extension : P.PathExtension H seed
  edges : seed.edges=P.edges ∪ l.toFinset ∪ extra
  endpoint : 1-δ ≤ seed.rank v.succ
  bands : seed.PathBands H δ
  ready : seed.PathReady H δ

/-- The four-edge terminal case: use a quartet for an even residual fiber;
otherwise divert one triple to an off-path child and finish through one reserve. -/
theorem PartialSeed.exists_pathFour (P : PartialSeed H) (a b c d z : Fin k)
    (hb : H.parent b=a.succ) (hc : H.parent c=b.succ) (hd : H.parent d=c.succ)
    (hz : H.parent z=d.succ)
    (ha : H.parent a=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent a)
    (hna : a ∉ P.edges) (hnb : b ∉ P.edges) (hnc : c ∉ P.edges) (hnd : d ∉ P.edges)
    (hactive : P.AllActive H) {β ε : ℚ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbands : P.PathBands H β) (hp : 0 < P.rank (H.parent a))
    (hp1 : P.rank (H.parent a) ≤ 1) (hhigh : 1-β ≤ P.rank (H.parent a)) :
    Nonempty (P.PathBuilt H [a,b,c,d] d (β+ε)) := by
  classical
  let O := Finset.univ.filter (fun i => H.parent i=b.succ ∧ i≠c)
  by_cases heven : Even O.card
  · obtain ⟨Q,hExt,hE,hend,hbands,hready⟩ := P.exists_pathQuartet H a b c d
      hb hc hd ha hna hnb hnc hnd heven hactive hβ hε hbands hp hp1 hhigh
    refine ⟨⟨Q,∅,by simp,by simp,hExt,?_,hend,hbands,hready⟩⟩
    simpa using hE
  · obtain ⟨w,hw⟩ := Finset.card_pos.mp ((Nat.not_even_iff_odd.mp heven).pos)
    have hw' : H.parent w=b.succ ∧ w≠c := by simpa [O] using hw
    have hnw := P.child_unassigned H hnb hw'.1
    obtain ⟨t,Q,hPQ,hQE,ht,hte,haR,hbR,hwR,hQbands,hQactive⟩ :=
      P.exists_pathTriple H a b w hb hw'.1 ha hna hnb hnw hactive hβ
        (show 0 < ε/2 by positivity) hbands hp hp1 hhigh
    have hab := edge_index_lt H hb
    have hbc := edge_index_lt H hc
    have hcd := edge_index_lt H hd
    have hca : c≠a := by intro h; have := congrArg Fin.val h; omega
    have hcb : c≠b := by intro h; have := congrArg Fin.val h; omega
    have hda : d≠a := by intro h; have := congrArg Fin.val h; omega
    have hdb : d≠b := by intro h; have := congrArg Fin.val h; omega
    have hdw : d≠w := by
      intro h
      have he : c=b := Fin.succ_injective _ (hd.symm.trans (h ▸ hw'.1))
      exact hcb he
    have hQc : c ∉ Q.edges := by simp [hQE,hnc,hca,hcb,hw'.2.symm]
    have hQd : d ∉ Q.edges := by simp [hQE,hnd,hda,hdb,hdw]
    have hQz := Q.child_unassigned H hQd hz
    have hbQ : b ∈ Q.edges := by simp [hQE]
    have hpc : Q.rank (H.parent c)=P.rank (H.parent a)-t := by rw [hc,hbR]
    have hpcpos : 0 < Q.rank (H.parent c) := by rw [hc]; exact Q.positive b hbQ
    have hpc1 : Q.rank (H.parent c) ≤ 1 := by rw [hpc]; linarith
    have hpchigh : 1-(β+ε/2) ≤ Q.rank (H.parent c) := by rw [hpc]; linarith
    obtain ⟨u,R,hQR,hRE,hu,hue,hcR,hdR,hzR,hRbands,hRactive⟩ :=
      Q.exists_pathTriple H c d z hd hz (Or.inr ⟨b,hbQ,hc.symm⟩)
        hQc hQd hQz hQactive (show 0 ≤ β+ε/2 by linarith)
        (show 0 < ε/2 by positivity) hQbands hpcpos hpc1 hpchigh
    have hbudget : β+ε/2+ε/2=β+ε := by ring
    refine ⟨⟨R,{w,z},by have := Finset.card_insert_le w ({z} : Finset (Fin k)); simpa using this,
      ?_,hPQ.trans H hQR,?_,?_,?_,?_⟩⟩
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · subst i; exact ⟨b,by simp,hw'.1⟩
      · subst i; exact ⟨d,by simp,hz⟩
    · rw [hRE,hQE]
      simp only [List.toFinset_cons,List.toFinset_nil,Finset.insert_eq,Finset.union_empty]
      ac_rfl
    · rw [hdR,hpc]
      linarith
    · simpa only [hbudget] using hRbands
    · exact hRactive.ready H (β+ε)


/-- Consume any fresh actual-parent path of at least two edges. Splitting the
positive error allowance in half at each triple bounds the total displacement.
A single child at the endpoint supplies the optional terminal reserve edge. -/
theorem PartialSeed.exists_pathSuffix (P : PartialSeed H) (a b : Fin k) (l : List (Fin k))
    (v z : Fin k)
    (hchain : (a::b::l).IsChain (fun i j => H.parent j=i.succ))
    (hnodup : (a::b::l).Nodup) (hlast : (a::b::l).getLast?=some v)
    (hz : H.parent z=v.succ)
    (ha : H.parent a=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent a)
    (hfresh : ∀ i ∈ a::b::l, i ∉ P.edges)
    (hactive : P.AllActive H) {β ε : ℚ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbands : P.PathBands H β) (hp : 0 < P.rank (H.parent a))
    (hp1 : P.rank (H.parent a) ≤ 1) (hhigh : 1-β ≤ P.rank (H.parent a)) :
    Nonempty (P.PathBuilt H (a::b::l) v (β+ε)) := by
  classical
  have hb := (List.isChain_cons_cons.mp hchain).1
  have hna := hfresh a (by simp)
  have hnb := hfresh b (by simp)
  cases l with
  | nil =>
    have hv : b=v := by simpa using hlast
    subst v
    have hnz := P.child_unassigned H hnb hz
    obtain ⟨t,Q,hPQ,hQE,ht,hte,haR,hbR,hzR,hQbands,hQactive⟩ :=
      P.exists_pathTriple H a b z hb hz ha hna hnb hnz hactive hβ hε hbands hp hp1 hhigh
    refine ⟨⟨Q,{z},by simp,?_,hPQ,?_,?_,hQbands,hQactive.ready H (β+ε)⟩⟩
    · intro i hi; simp only [Finset.mem_singleton] at hi; subst i; exact ⟨b,by simp,hz⟩
    · rw [hQE]
      simp only [List.toFinset_cons,List.toFinset_nil,Finset.insert_eq,Finset.union_empty]
      ac_rfl
    · rw [hbR]; linarith
  | cons c l =>
    have hc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).1
    have hnc := hfresh c (by simp)
    cases l with
    | nil =>
      have hv : c=v := by simpa using hlast
      subst v
      obtain ⟨t,Q,hPQ,hQE,ht,hte,haR,hbR,hcR,hQbands,hQactive⟩ :=
        P.exists_pathTriple H a b c hb hc ha hna hnb hnc hactive hβ hε hbands hp hp1 hhigh
      refine ⟨⟨Q,∅,by simp,by simp,hPQ,?_,?_,hQbands,hQactive.ready H (β+ε)⟩⟩
      · simpa using hQE
      · rw [hcR]; linarith
    | cons d l =>
      have hd := (List.isChain_cons_cons.mp
        (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).2).1
      have hnd := hfresh d (by simp)
      cases l with
      | nil =>
        have hv : d=v := by simpa using hlast
        subst v
        exact P.exists_pathFour H a b c d z hb hc hd hz ha hna hnb hnc hnd
          hactive hβ hε hbands hp hp1 hhigh
      | cons e l =>
        obtain ⟨t,Q,hPQ,hQE,ht,hte,haR,hbR,hcR,hQbands,hQactive⟩ :=
          P.exists_pathTriple H a b c hb hc ha hna hnb hnc hactive hβ
            (show 0 < ε/2 by positivity) hbands hp hp1 hhigh
        have hnodup' : (d::e::l).Nodup := hnodup.of_cons.of_cons.of_cons
        have hchain' : (d::e::l).IsChain (fun i j => H.parent j=i.succ) :=
          hchain.tail.tail.tail
        have hlast' : (d::e::l).getLast?=some v := by simpa using hlast
        have hQc : c ∈ Q.edges := by simp [hQE]
        have hfresh' : ∀ i ∈ d::e::l, i ∉ Q.edges := by
          intro i hi hQi
          rw [hQE] at hQi
          simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hQi
          rcases hQi with hQi | hQi | hQi | hQi
          · exact hfresh i (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi))) hQi
          · subst i
            exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi))
          · subst i
            exact (List.nodup_cons.mp hnodup.of_cons).1 (List.mem_cons_of_mem c hi)
          · subst i
            exact (List.nodup_cons.mp hnodup.of_cons.of_cons).1 hi
        have hpd : Q.rank (H.parent d)=P.rank (H.parent a)-2*t := by rw [hd,hcR]
        have hpdpos : 0 < Q.rank (H.parent d) := by rw [hd]; exact Q.positive c hQc
        have hpd1 : Q.rank (H.parent d) ≤ 1 := by rw [hpd]; linarith
        have hpdhigh : 1-(β+ε/2) ≤ Q.rank (H.parent d) := by rw [hpd]; linarith
        obtain ⟨R⟩ := PartialSeed.exists_pathSuffix Q d e l v z hchain' hnodup' hlast' hz
          (Or.inr ⟨c,hQc,hd.symm⟩) hfresh' hQactive (show 0 ≤ β+ε/2 by linarith)
          (show 0 < ε/2 by positivity) hQbands hpdpos hpd1 hpdhigh
        have hbudget : β+ε/2+ε/2=β+ε := by ring
        refine ⟨⟨R.seed,R.extra,R.extra_card,?_,hPQ.trans H R.extension,?_,?_,?_,?_⟩⟩
        · intro w hw
          obtain ⟨i,hi,hp⟩ := R.extra_parent w hw
          exact ⟨i,List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c hi)),hp⟩
        · rw [R.edges,hQE]
          simp only [List.toFinset_cons,Finset.insert_eq]
          ac_rfl
        · simpa only [hbudget] using R.endpoint
        · simpa only [hbudget] using R.bands
        · simpa only [hbudget] using R.ready
termination_by l.length


/-- Completed initial-path data on the actual graph. The seed itself supplies
root zero, injectivity, consistency, the global edge permutation, and frontier.
The support is exactly the selected path plus at most two incident side edges. -/
structure InitialPathSeed (v : Fin (k+1)) (δ : ℚ) where
  seed : PartialSeed H
  anchor : Fin k
  anchor_assigned : anchor ∈ seed.edges
  anchor_one : seed.rank anchor.succ=1
  selected_assigned : ∃ i ∈ seed.edges, i.succ=v
  selected_high : 1-δ ≤ seed.rank v
  bands : seed.PathBands H δ
  ready : seed.PathReady H δ
  extra : Finset (Fin k)
  extra_card : extra.card ≤ 2
  extra_parent : ∀ z ∈ extra, H.parent z ∈ CorePaths.path H v
  edges : seed.edges=(CorePaths.edges H v).toFinset ∪ extra

/-- For every selected path of length at least three, one available child at
its endpoint is enough to construct the initial assignment. Consequently two
pre-attached reserve leaves at each mark more than suffice. -/
theorem exists_initialPath (v : Fin (k+1))
    (hlong : 3 ≤ (CorePaths.edges H v).length)
    (hreserve : ∃ z : Fin k, H.parent z=v)
    {δ : ℚ} (hδ : 0 < δ) : Nonempty (InitialPathSeed H v δ) := by
  classical
  cases hE : CorePaths.edges H v with
  | nil => simp [hE] at hlong
  | cons r l =>
    cases l with
    | nil => simp [hE] at hlong
    | cons a l =>
      cases l with
      | nil => simp [hE] at hlong
      | cons b l =>
        have hr := CorePaths.first_edge_parent H v r (a::b::l) hE
        let P := PartialSeed.anchor H r hr
        have hchain : (r::a::b::l).IsChain (fun i j => H.parent j=i.succ) := by
          rw [← hE]; exact CorePaths.edges_chain H v
        have hnodup : (r::a::b::l).Nodup := by
          rw [← hE]; exact CorePaths.edges_nodup H v
        have ha := (List.isChain_cons_cons.mp hchain).1
        let w := (a::b::l).getLast (by simp)
        have hlast : (a::b::l).getLast?=some w := List.getLast?_eq_some_getLast (by simp)
        have hwmem : w ∈ a::b::l := List.getLast_mem (by simp)
        have hwv : w.succ=v := by
          have h := CorePaths.path_last H v
          rw [CorePaths.path_eq_edges,hE] at h
          simp only [List.map_cons,List.getLast?_cons_cons] at h
          have hh : ((a::b::l).map Fin.succ).getLast?=some w.succ := by
            rw [List.getLast?_map,hlast]; rfl
          simp only [List.map_cons,List.getLast?_cons_cons] at hh
          exact Option.some.inj (hh.symm.trans h)
        obtain ⟨z,hz⟩ := hreserve
        have hfresh : ∀ i ∈ a::b::l, i ∉ P.edges := by
          intro i hi hPi
          have he : i=r := by simpa [P] using hPi
          subst i
          exact (List.nodup_cons.mp hnodup).1 hi
        have hactive : P.AllActive H := by
          intro i hi
          have he : i=r := by simpa [P] using hi
          subst i
          simp [P]
        have hbands : P.PathBands H 0 := by
          intro x hx
          have he : x=1 := by simpa [P] using hx
          subst x
          norm_num
        have hp : P.rank (H.parent a)=1 := by simp [ha,P]
        obtain ⟨R⟩ := P.exists_pathSuffix H a b l w z hchain.tail hnodup.of_cons hlast
          (by simpa [hwv] using hz) (Or.inr ⟨r,by simp [P],ha.symm⟩)
          hfresh hactive (by norm_num : (0:ℚ) ≤ 0) hδ hbands
          (by rw [hp]; norm_num) (by rw [hp]) (by rw [hp]; norm_num)
        have hrP : r ∈ P.edges := by simp [P]
        have hwR : w ∈ R.seed.edges := by
          rw [R.edges]
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hwmem))
        refine ⟨⟨R.seed,r,R.extension.edges hrP,?_,⟨w,hwR,hwv⟩,?_,?_,?_,
          R.extra,R.extra_card,?_,?_⟩⟩
        · rw [R.extension.rank r hrP]; exact PartialSeed.anchor_rank H r hr
        · rw [← hwv]; simpa using R.endpoint
        · simpa using R.bands
        · simpa using R.ready
        · intro z hz
          obtain ⟨i,hi,hp⟩ := R.extra_parent z hz
          rw [hp,← CorePaths.edges_mem_iff]
          rw [hE]
          exact List.mem_cons_of_mem r hi
        · rw [R.edges,hE]
          change ({r} ∪ (a::b::l).toFinset) ∪ R.extra=(r::a::b::l).toFinset ∪ R.extra
          simp only [List.toFinset_cons,Finset.insert_eq]

#print axioms PartialSeed.exists_pathSuffix
#print axioms exists_initialPath
end FixedCore.Next
