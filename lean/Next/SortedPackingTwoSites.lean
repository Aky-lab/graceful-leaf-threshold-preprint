import Next.SortedPackingBand

namespace FixedCore.SortedPacking
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- With no secondary transfers, all residual bank leaves use ordinary
mirror pairs. The root receives the remaining complement. -/
theorem two_supply_extension_no_secondary
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (used : Finset ℕ) (covers : ∀ i, 0 < S.rank i → S.rank i < S.rank v → S.rank i ∈ used)
    (emptySecondary : ∀ j, j≠0 → j≠v → c j=0)
    (evenBank : Even (c v))
    (rootSlack : k+total c+2*used.card+1≤S.rank v+k+c 0) :
    ExtendingGraceful H c S.rank := by
  classical
  let site : Fin 0 ↪ Fin (k+1) := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  have ht := PackingCapacity.total_sites c v hv site
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun j h0 hv _ => emptySecondary j h0 hv)
  simp at ht
  have hcap : (∅ : Finset ℕ).card+used.card+c v/2≤(S.rank v-1)/2 := by
    simp
    omega
  obtain ⟨J,hJcard,hJ,_⟩ := choose_outside_set used ∅ hcap
  have hJi : J⊆MirrorPairs.indices (S.rank v) := fun x hx => (MirrorPairs.available_spec.mp (hJ hx)).1
  let Bank := LowBands.pairLabels (S.rank v) J
  have hp (x) (hx : x∈Bank) : 0<x ∧ x<S.rank v := BandGeometry.pairLabels_positive hJi hx
  have hfree := BandGeometry.intact_fresh hJ
  have hcard : Bank.card=c v := by
    rw [LowBands.pairLabels_card hJi,hJcard]
    obtain ⟨t,ht⟩ := evenBank
    omega
  refine extending_of_natural_bands S bound v hv site
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) Fin.elim0 Bank Fin.elim0
    ?_ ?_ ?_ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by simpa using hcard) (fun j h0 hv _ => emptySecondary j h0 hv)
  · exact fun z hz => (hp z hz).2.le.trans (bound v)
  · intro z hz i he
    have ⟨hpos,hlt⟩ := hp z hz
    exact Finset.disjoint_left.mp hfree hz
      (he ▸ covers i (he.symm ▸ hpos) (he.symm ▸ hlt))
  · intro z hz
    obtain ⟨he,hm⟩ := Packing.pairLabels_complement hJi hz
    exact ⟨he.le,hm⟩

end FixedCore.SortedPacking
