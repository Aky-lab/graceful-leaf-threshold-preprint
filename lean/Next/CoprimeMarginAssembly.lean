import Next.CoprimeMarginBounds
import Next.CoprimeTwoSites
import Next.SparsePackingAssembly

namespace FixedCore.CoprimeMargin

open TreeEncoding

variable {k : ℕ}

theorem graceful_of_two_sites (H : Core k) (c : Demand k) (u v : Fin (k+1))
    (huv : u ≠ v)
    (hu : trigger (k+1) (positiveDemandSites c).card ≤ c u)
    (hv : trigger (k+1) (positiveDemandSites c).card ≤ c v) : Graceful H c := by
  have hsupport (i : Fin (k+1)) (hi : i ∉ positiveDemandSites c) : c i = 0 := by
    by_contra h
    exact hi (by simp [positiveDemandSites, Nat.pos_of_ne_zero h])
  have hg := PolynomialTwoBank.BandMargin.two_large_sites_grid_or_exception_with_coprime_budget H c
    (positiveDemandSites c) u v huv 1 (k+1) (by decide) le_rfl
    hsupport (by simpa [trigger, PolynomialTwoBank.CoprimeMargin.gridTrigger] using hu) (by simpa [trigger, PolynomialTwoBank.CoprimeMargin.gridTrigger] using hv)
  rcases hg with hg | hx
  · exact hg.graceful
  · exact hx.graceful

theorem graceful_of_support_cutoff (H : Core k) (c : Demand k)
    (hq : 0 < (positiveDemandSites c).card)
    (hN : supportCutoff (k+1) (positiveDemandSites c).card ≤ k + total c) : Graceful H c := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (k+1))) c Finset.univ_nonempty
  have hm : ∀ y, c y ≤ c x := fun y => hx y (Finset.mem_univ y)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hq
  have hyp : 0 < c y := by simpa [positiveDemandSites] using hy
  have hxp := hyp.trans_le (hm y)
  by_cases h : ∃ y, y ≠ x ∧ trigger (k+1) (positiveDemandSites c).card ≤ c y
  · obtain ⟨y, hne, hy⟩ := h
    exact graceful_of_two_sites H c x y hne.symm (hy.trans (hm y)) hy
  · push Not at h
    have hR := SparseEffective.offSiteReserve_le_positiveSites_sub_one c hxp
    have hL := offSiteEven_le_of_small c hxp h
    apply SparsePacking.graceful_of_namedCutoff H c x
    refine le_trans ?_ hN
    unfold SparsePacking.namedCutoff supportCutoff
    apply SparsePacking.cutoff_mono_size_residual
    · rw [Fintype.card_fin]
      omega
    · exact hL

theorem graceful_of_uniform_cutoff (H : Core k) (c : Demand k)
    (hN : supportCutoff (k+1) (k+1) ≤ k + total c) : Graceful H c := by
  by_cases hq : 0 < (positiveDemandSites c).card
  · exact graceful_of_support_cutoff H c hq
      ((supportCutoff_mono_support (SparseSupport.support_card_le c)).trans hN)
  · have hzero : ∀ x, c x = 0 := by
      intro x
      by_contra! hx
      exact hq (Finset.card_pos.mpr ⟨x, by simp [positiveDemandSites, Nat.pos_of_ne_zero hx]⟩)
    have ht : total c = 0 := by simp [total, hzero]
    have hh := (order_le_uniform_cutoff k).trans hN
    omega

/-- With no secondary demand only the two-bank mirror allocation is needed. -/
theorem graceful_of_two_active (H : Core k) (c : Demand k) (u v : Fin (k+1))
    (huv : u≠v) (hempty : ∀ i,i≠u → i≠v → c i=0)
    (hu : 720*(k+1)-90≤c u) (hv : 720*(k+1)-90≤c v) : Graceful H c := by
  rcases PolynomialTwoBank.CoprimeMargin.two_active_sites_grid_or_exception H c u v huv
    1 (k+1) (by decide) le_rfl hempty
    (by simpa [PolynomialTwoBank.CoprimeMargin.twoOnlyTrigger] using hu)
    (by simpa [PolynomialTwoBank.CoprimeMargin.twoOnlyTrigger] using hv) with hg | hx
  · exact hg.graceful
  · exact hx.graceful

end FixedCore.CoprimeMargin
