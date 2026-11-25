import Next.CoprimeMarginAssembly
import Next.ParityPacketTwoBank
import Next.ParityPacketBounds

namespace FixedCore.ParityPacket
open TreeEncoding SparseOneBank
variable {k : ℕ}

theorem graceful_of_two_sites_adaptive (H : Core k) (c : Demand k) (u v : Fin (k+1))
    (huv : u≠v)
    (hu : trigger (k+1) (positiveDemandSites c).card (offSiteReserve c u)≤c u)
    (hv : trigger (k+1) (positiveDemandSites c).card (offSiteReserve c u)≤c v) :
    Graceful H c := by
  let q := (positiveDemandSites c).card
  let o := offSiteReserve c u
  have ht := trigger_pos (k+1) q o
  have hup : 0<c u := ht.trans_le hu
  have hvp : 0<c v := ht.trans_le hv
  have hq : 2≤q := by
    have hsub : ({u,v} : Finset (Fin (k+1))) ⊆ positiveDemandSites c := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl <;> simp [positiveDemandSites, hup, hvp]
    simpa [q,huv] using Finset.card_le_card hsub
  have hqn := SparseSupport.support_card_le c
  have ho := SparseEffective.offSiteReserve_le_positiveSites_sub_one c hup
  obtain ⟨hj1,hj⟩ := PolynomialTwoBank.ParityPacket.budget_inputs hq hqn (show o<q by omega)
  have hsupport (i : Fin (k+1)) (hi : i∉positiveDemandSites c) : c i=0 := by
    by_contra h
    exact hi (by simp [positiveDemandSites,Nat.pos_of_ne_zero h])
  have hg := PolynomialTwoBank.BandMargin.two_large_sites_grid_or_exception_with_parity_budget H c
    (positiveDemandSites c) u v huv 1 (k+1) (PolynomialTwoBank.ParityPacket.edgeBudget (k+1) q o)
    (by decide) le_rfl hj hj1 hsupport
    (PolynomialTwoBank.ParityPacket.reserve_edges_le c u v huv hup hvp) hu hv
  rcases hg with hg | hx
  · exact hg.graceful
  · exact hx.graceful

theorem graceful_of_two_sites (H : Core k) (c : Demand k) (u v : Fin (k+1)) (huv : u≠v)
    (hu : trigger (k+1) (positiveDemandSites c).card 0≤c u)
    (hv : trigger (k+1) (positiveDemandSites c).card 0≤c v) : Graceful H c :=
  graceful_of_two_sites_adaptive H c u v huv ((trigger_le_no_discount ..).trans hu)
    ((trigger_le_no_discount ..).trans hv)

theorem graceful_of_support_cutoff (H : Core k) (c : Demand k)
    (x : Fin (k+1)) (hxp : 0<c x) (hm : ∀ y,c y≤c x)
    (hN : supportCutoff (k+1) (positiveDemandSites c).card (offSiteReserve c x)≤k+total c) :
    Graceful H c := by
  by_cases h : ∃ y,y≠x ∧ trigger (k+1) (positiveDemandSites c).card (offSiteReserve c x)≤c y
  · obtain ⟨y,hne,hy⟩ := h
    exact graceful_of_two_sites_adaptive H c x y hne.symm (hy.trans (hm y)) hy
  · push Not at h
    have hL := offSiteEven_le_of_small c hxp h
    apply SparsePacking.graceful_of_namedCutoff H c x
    refine le_trans ?_ hN
    unfold SparsePacking.namedCutoff supportCutoff
    apply SparsePacking.cutoff_mono_size_residual
    · rw [Fintype.card_fin]
    · exact hL

end FixedCore.ParityPacket
