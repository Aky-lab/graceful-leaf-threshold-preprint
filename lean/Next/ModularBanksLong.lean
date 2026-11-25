import Next.ModularBanksPath

namespace FixedCore.ModularBanks
variable {k : ℕ}

/-- A long selected path has the actual quotient required by modular
labeling. The first edge is deleted, the second contracted, and the two
banks identified, after a proved rerooting at the far bank. -/
theorem exists_long_quotient (H : Core k) (a b : Fin k) (v : Fin (k+1))
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (hpath : b∈CorePaths.edges H v) (hv : v≠b.succ) :
    ∃ s : ℕ,∃ K : Core s,∃ Q : FourQuotient H K,
      Q.bank=v ∧ Q.high=a.succ ∧ Q.low=b.succ ∧ Q.anchor=a ∧
      (∀ j,Q.liftEdge j≠Q.anchor) ∧ s≤k := by
  obtain ⟨G,e,he⟩ := Reroot.exists_reroot H v
  have hpa : a∈CorePaths.edges H v := CorePaths.edges_parent_closed H v b a hpath hb
  have ra := reverse_path e v he a hpa
  have rb := reverse_path e v he b hpath
  have hzero : e.vertex 0=(e.edge a).succ := by simpa [ha] using ra.1
  have hhigh : e.vertex a.succ=(e.edge b).succ := by simpa [hb] using rb.1
  have hnz : e.vertex b.succ≠0 := by
    intro h
    exact hv (e.vertex.injective (he.trans h.symm))
  let z := CorePaths.predIndex (e.vertex b.succ) hnz
  have hz : z.succ=e.vertex b.succ := by
    apply Fin.ext
    have hp : 0<(e.vertex b.succ).val := by
      by_contra hp
      exact hnz (Fin.ext (by simp only [Fin.val_zero]; omega))
    dsimp [z,CorePaths.predIndex]
    omega
  have hw : G.parent (e.edge b)=z.succ := rb.2.symm.trans hz.symm
  have hu : G.parent (e.edge a)=(e.edge b).succ := ra.2.symm.trans hhigh
  let R := long G z (e.edge b) (e.edge a) hw hu
  let E : Finset (Fin k) := Finset.univ \ insert (e.edge a) {e.edge b}
  have hzw : z≠e.edge b := by
    have h := index_lt_of_parent G hw
    intro he; subst z; omega
  have hzu : z≠e.edge a := by
    have h1 := index_lt_of_parent G hw
    have h2 := index_lt_of_parent G hu
    intro he; subst z; omega
  have hwu : e.edge b≠e.edge a := by
    have h := index_lt_of_parent G hu
    intro he; have hh := congrArg Fin.val he; omega
  have hRbank : R.project (e.edge a).succ=0 := by
    apply (embed_strictMono _).injective
    simp [R,long,twoLevel]
  have hRmark : R.project (e.edge b).succ=R.project z.succ := by
    apply (R.project_eq_iff _ _).mpr
    simp [R,long,twoLevel,hwu,hzu,hzw]
  have root_translate (x : Fin (k+1))
      (h : e.vertex x=0 ∨ e.vertex x=(e.edge a).succ) : x=0 ∨ x=v := by
    rcases h with h | h
    · exact Or.inr (e.vertex.injective (h.trans he.symm))
    · exact Or.inl (e.vertex.injective (h.trans hzero.symm))
  have mark_translate (x : Fin (k+1))
      (h : e.vertex x=z.succ ∨ e.vertex x=(e.edge b).succ) : x=a.succ ∨ x=b.succ := by
    rcases h with h | h
    · exact Or.inr (e.vertex.injective (h.trans hz))
    · exact Or.inl (e.vertex.injective (h.trans hhigh.symm))
  let Q : FourQuotient H (R.core G) := {
    project := fun x => R.project (e.vertex x)
    bank := v
    high := a.succ
    low := b.succ
    mark := R.project z.succ
    bank_ne_zero := by
      intro h
      have hh : (e.edge a).succ=0 := hzero.symm.trans (by simpa [h] using he)
      exact Fin.succ_ne_zero _ hh
    high_ne_low := by
      intro h
      have hab := Fin.succ_injective k h
      have hlt := index_lt_of_parent H hb
      subst b
      omega
    mark_ne_zero := by
      intro h
      have hh := congrArg (embed E) h
      rw [R.embed_project,embed_zero] at hh
      have hh' : z.succ=0 := by simpa [R,long,twoLevel,hzu,hzw] using hh
      exact Fin.succ_ne_zero _ hh'
    root := by rw [hzero,hRbank]
    bank_root := by rw [he,R.project_root]
    high_mark := by rw [hhigh,hRmark]
    low_mark := by rw [← hz]
    fibers := by
      intro x y h
      have hh := twoLevel_one_fibers (e.edge a) z (e.edge b) _ _ _
        (e.vertex x) (e.vertex y) h
      rcases hh with hh | ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inl (e.vertex.injective hh)
      · exact Or.inr (Or.inl ⟨root_translate x hx,root_translate y hy⟩)
      · exact Or.inr (Or.inr ⟨mark_translate x hx,mark_translate y hy⟩)
    anchor := a
    bridge := b
    anchor_parent := ha
    anchor_child := rfl
    bridge_parent := hb
    bridge_child := rfl
    liftEdge := fun j => e.edge.symm (edgeOrder E j).val
    incidence := by
      intro j
      let i := e.edge.symm (edgeOrder E j).val
      have hei : e.edge i=(edgeOrder E j).val := e.edge.apply_symm_apply _
      have hchild : R.project (edgeOrder E j).val.succ=j.succ := by
        have hc := R.project_child (edgeOrder E j)
        change R.project (edgeOrder E j).val.succ=((edgeOrder E).symm (edgeOrder E j)).succ at hc
        simpa only [OrderIso.symm_apply_apply] using hc
      rcases e.incidence i with ⟨hp,hc⟩ | ⟨hp,hc⟩
      · left
        constructor
        · change R.project (e.vertex (H.parent i))=_
          rw [hp,hei]
          rfl
        · change R.project (e.vertex i.succ)=_
          rw [hc,hei,hchild]
      · right
        constructor
        · change R.project (e.vertex (H.parent i))=_
          rw [hp,hei,hchild]
        · change R.project (e.vertex i.succ)=_
          rw [hc,hei]
          rfl }
  refine ⟨E.card,R.core G,Q,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro j hj
    have heq := congrArg e.edge hj
    change e.edge (e.edge.symm (edgeOrder E j).val)=e.edge a at heq
    rw [e.edge.apply_symm_apply] at heq
    have hm := (edgeOrder E j).property
    have hn : (edgeOrder E j).val≠e.edge a := by
      have hh := (Finset.mem_sdiff.mp hm).2
      intro h
      exact hh (by simp [h])
    exact hn heq
  · exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)

#print axioms exists_long_quotient
end FixedCore.ModularBanks
