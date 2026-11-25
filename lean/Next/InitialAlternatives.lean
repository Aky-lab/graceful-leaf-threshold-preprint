import Next.ShortPreparation

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- A two-edge branch beyond the selected endpoint is a root auxiliary branch
after rerooting there. The two selected endpoints are interchanged explicitly. -/
theorem exists_endAuxPrepared (a b c d : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (hc : H.parent c=b.succ) (hd : H.parent d=c.succ)
    {δ : ℚ} (hδ : 0 < δ) :
    ∃ K : Core k, ∃ e : CoreIso H K, e.vertex b.succ=0 ∧
      Nonempty (PreparedSeed K (e.vertex 0) δ) := by
  have hab : a≠b := by
    have h := edge_index_lt H hb
    intro he; have := congrArg Fin.val he; omega
  have hbc : b≠c := by
    have h := edge_index_lt H hc
    intro he; have := congrArg Fin.val he; omega
  have hcd : c≠d := by
    have h := edge_index_lt H hd
    intro he; have := congrArg Fin.val he; omega
  obtain ⟨K,e,hroot⟩ := Reroot.exists_reroot H b.succ
  have hbK : K.parent (e.edge b)=0 ∧ e.vertex a.succ=(e.edge b).succ := by
    rcases e.incidence b with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact False.elim (Fin.succ_ne_zero _ (h₂.symm.trans hroot))
    · exact ⟨h₂.symm.trans hroot,by simpa [hb] using h₁⟩
  have haK : K.parent (e.edge a)=(e.edge b).succ ∧ e.vertex 0=(e.edge a).succ := by
    rcases e.incidence a with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · have he : a=b := e.edge.injective (Fin.succ_injective _ (h₂.symm.trans hbK.2))
      exact False.elim (hab he)
    · exact ⟨h₂.symm.trans hbK.2,by simpa [ha] using h₁⟩
  have hcK : K.parent (e.edge c)=0 ∧ e.vertex c.succ=(e.edge c).succ := by
    rcases e.incidence c with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact ⟨h₁.symm.trans (by simpa [hc] using hroot),h₂⟩
    · have he : (e.edge c).succ=0 := h₁.symm.trans (by simpa [hc] using hroot)
      exact False.elim (Fin.succ_ne_zero _ he)
  have hdK : K.parent (e.edge d)=(e.edge c).succ := by
    rcases e.incidence d with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact h₁.symm.trans (by simpa [hd] using hcK.2)
    · have he : (e.edge d).succ=(e.edge c).succ := h₁.symm.trans (by simpa [hd] using hcK.2)
      exact False.elim (hcd (e.edge.injective (Fin.succ_injective _ he)).symm)
  obtain ⟨P,_⟩ := exists_rootAuxPrepared K (e.edge b) (e.edge a) (e.edge c) (e.edge d)
    hbK.1 haK.1 hcK.1 hdK (fun h => hbc (e.edge.injective h)) hδ
  refine ⟨K,e,hroot,?_⟩
  rw [haK.2]
  exact ⟨P⟩

/-- Every actual distance-two selected path either has a checked initial
preparation (possibly after swapping the endpoints), or is exactly the
exceptional pendant shape handled by the finite exceptional solver. -/
theorem distanceTwo_prepared_or_exception (v : Fin (k+1))
    (hdist : (CorePaths.edges H v).length=2) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, ∃ i j : Fin k, i≠j ∧ H.parent i=x ∧ H.parent j=x)
    {δ : ℚ} (hδ : 0 < δ) :
    Nonempty (PreparedSeed H v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (PreparedSeed K (e.vertex 0) δ)) ∨
      Nonempty (ExceptionalReserves.Certificate H marks) := by
  obtain ⟨a,b,hpath,ha,hb,hv⟩ := CorePaths.distance_two H v hdist
  subst v
  rcases DistanceTwoShape.alternatives H a b ha hb with hm | hr | he | hp
  · obtain ⟨w,hw,hwb⟩ := hm
    obtain ⟨P,_⟩ := exists_middlePrepared H a b w ha hb hw hwb.symm hδ
    exact Or.inl ⟨P⟩
  · obtain ⟨c,d,hc,hd,hca⟩ := hr
    obtain ⟨P,_⟩ := exists_rootAuxPrepared H a b c d ha hb hc hd hca.symm hδ
    exact Or.inl ⟨P⟩
  · obtain ⟨c,d,hc,hd⟩ := he
    exact Or.inr (Or.inl (exists_endAuxPrepared H a b c d ha hb hc hd hδ))
  · exact Or.inr (Or.inr (DistanceTwoShape.pendant_certificate_of_two_children
      H a b ha hb hp marks hmarks))

/-- Sharper distance-two alternative retaining the selected endpoints and
exact pendant incidence, for transporting the manuscript's shape exception. -/
theorem distanceTwo_prepared_or_pendant (v : Fin (k+1))
    (hdist : (CorePaths.edges H v).length=2) {δ : ℚ} (hδ : 0 < δ) :
    Nonempty (PreparedSeed H v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (PreparedSeed K (e.vertex 0) δ)) ∨
      (∃ a b : Fin k, H.parent a=0 ∧ H.parent b=a.succ ∧ v=b.succ ∧
        DistanceTwoShape.PendantShape H a b) := by
  obtain ⟨a,b,hpath,ha,hb,hv⟩ := CorePaths.distance_two H v hdist
  subst v
  rcases DistanceTwoShape.alternatives H a b ha hb with hm | hr | he | hp
  · obtain ⟨w,hw,hwb⟩ := hm
    obtain ⟨P,_⟩ := exists_middlePrepared H a b w ha hb hw hwb.symm hδ
    exact Or.inl ⟨P⟩
  · obtain ⟨c,d,hc,hd,hca⟩ := hr
    obtain ⟨P,_⟩ := exists_rootAuxPrepared H a b c d ha hb hc hd hca.symm hδ
    exact Or.inl ⟨P⟩
  · obtain ⟨c,d,hc,hd⟩ := he
    exact Or.inr (Or.inl (exists_endAuxPrepared H a b c d ha hb hc hd hδ))
  · exact Or.inr (Or.inr ⟨a,b,ha,hb,rfl,hp⟩)

#print axioms exists_endAuxPrepared
#print axioms distanceTwo_prepared_or_exception
#print axioms distanceTwo_prepared_or_pendant
end FixedCore.Next
