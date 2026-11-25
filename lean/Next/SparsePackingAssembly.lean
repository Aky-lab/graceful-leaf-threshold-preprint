import Next.SparsePackingBounds
import Next.SparsePackingOneBank
import Next.SparseSupportAssembly

namespace FixedCore.SparsePacking

open SparseEffective TreeEncoding

/-- If the unchanged two-site test rejects, the tighter support cutoff
bounds the actual cutoff at some root. -/
theorem exists_namedCutoff_le_of_support {k : ℕ} (c : Demand k)
    (hq : 0 < (positiveDemandSites c).card)
    (ht : twoSiteCertificate c = false)
    (h : supportCutoff (k+1) (positiveDemandSites c).card ≤ k + total c) :
    ∃ x, namedCutoff 1 c x ≤ k + total c := by
  obtain ⟨x, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (k+1))) c Finset.univ_nonempty
  have hm : ∀ y, c y ≤ c x := fun y => hmax y (Finset.mem_univ y)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hq
  have hy' : 0 < c y := by simpa [positiveDemandSites] using hy
  have hx := lt_of_lt_of_le hy' (hm y)
  have hreserve := offSiteReserve_le_positiveSites_sub_one c hx
  have hres := offSiteEven_le_of_twoSite_false c hx hm ht
  have hcut : namedCutoff 1 c x ≤ supportCutoff (k+1) (positiveDemandSites c).card := by
    unfold namedCutoff supportCutoff
    apply cutoff_mono_size_residual
    · rw [Fintype.card_fin]
      omega
    · simpa only [twoSiteTrigger, SparseSupport.trigger] using hres
  exact ⟨x, hcut.trans h⟩

/-- The tighter one-bank check and unchanged two-site check both apply
to the actual graph represented by a numbered demand. -/
theorem graceful_of_namedCutoff {k : ℕ} (H : Core k) (c : Demand k) (x : Fin (k+1))
    (hN : namedCutoff 1 c x ≤ k + total c) : Graceful H c := by
  let e : CoreDiameter.graph H ≃g CoreDiameter.graph H := RelIso.refl _
  let f := leafExtensionIso e c
  apply (graphGraceful_iff_representation f).mp
  apply sparse_packing_leaf_extension (graph_isTree H) c x
  rw [representation_edge_count f]
  exact hN

theorem graceful_of_support_cutoff {k : ℕ} (H : Core k) (c : Demand k)
    (hq : 0 < (positiveDemandSites c).card)
    (h : supportCutoff (k+1) (positiveDemandSites c).card ≤ k + total c) :
    Graceful H c := by
  cases ht : twoSiteCertificate c with
  | true => exact twoSiteCertificate_sound H c ht
  | false =>
    obtain ⟨x, hx⟩ := exists_namedCutoff_le_of_support c hq ht h
    exact graceful_of_namedCutoff H c x hx

theorem graceful_of_uniform_cutoff {k : ℕ} (H : Core k) (c : Demand k)
    (h : supportCutoff (k+1) (k+1) ≤ k + total c) : Graceful H c := by
  by_cases hq : 0 < (positiveDemandSites c).card
  · exact graceful_of_support_cutoff H c hq
      ((supportCutoff_mono_support (SparseSupport.support_card_le c)).trans h)
  · have hzero : ∀ x, c x = 0 := by
      intro x
      by_contra! hx
      have hx' : x ∈ positiveDemandSites c := by
        simp [positiveDemandSites, Nat.pos_of_ne_zero hx]
      exact hq (Finset.card_pos.mpr ⟨x,hx'⟩)
    have ht : total c = 0 := by simp [total, hzero]
    have hc := (order_le_uniform_cutoff k).trans h
    omega

end FixedCore.SparsePacking
