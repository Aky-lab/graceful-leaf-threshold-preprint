import Next.SparseSupportBounds
import Next.SparseSupportResidual

namespace FixedCore.SparseSupport

open SparseEffective

theorem support_card_le {k : ℕ} (c : Demand k) :
    (TreeEncoding.positiveDemandSites c).card ≤ k+1 := by
  simpa using Finset.card_le_univ (TreeEncoding.positiveDemandSites c)

/-- At nonempty support, the exact support-dependent edge cutoff guarantees
coverage by the existing two numerical certificates. -/
theorem combinedCertificate_of_support_cutoff {k : ℕ} (c : Demand k)
    (hq : 0 < (TreeEncoding.positiveDemandSites c).card)
    (h : cutoff (k+1) (TreeEncoding.positiveDemandSites c).card ≤ k+total c) :
    combinedCertificate c = true := by
  cases ht : twoSiteCertificate c with
  | true => simp [combinedCertificate, ht]
  | false =>
    obtain ⟨x, _, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin (k+1))) c Finset.univ_nonempty
    have hm : ∀ y, c y ≤ c x := fun y => hmax y (Finset.mem_univ y)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hq
    have hy' : 0 < c y := by simpa [TreeEncoding.positiveDemandSites] using hy
    have hx := lt_of_lt_of_le hy' (hm y)
    have hreserve := offSiteReserve_le_positiveSites_sub_one c hx
    have hresidual := offSiteEven_le_of_twoSite_false c hx hm ht
    have hs : SparseOneBank.namedCutoff 1 c x ≤ cutoff (k+1)
        (TreeEncoding.positiveDemandSites c).card := by
      unfold SparseOneBank.namedCutoff cutoff
      apply SparseOneBank.cutoff_mono_size_residual
      · rw [Fintype.card_fin]
        omega
      · simpa only [twoSiteTrigger, trigger] using hresidual
    have hf : quickCertificate c = true := (quickCertificate_iff c).mpr ⟨x, hs.trans h⟩
    simp [combinedCertificate, hf]

/-- The uniform cutoff is strictly larger than the edge count of the core
with no new leaves. -/
theorem order_le_uniform_cutoff (k : ℕ) : k+1 ≤ cutoff (k+1) (k+1) := by
  have hS : k+1 ≤ k+1+(k+1)-1 := by omega
  have hp : k+1 ≤ (k+1+(k+1)-1)^3 := by
    have h := Nat.pow_le_pow_left hS 3
    have hk : k+1 ≤ (k+1)^3 := by
      have h' : 1 ≤ (k+1)^2 := Nat.one_le_pow _ _ (by omega)
      calc
        k+1 = (k+1)*1 := (Nat.mul_one _).symm
        _ ≤ (k+1)*(k+1)^2 := Nat.mul_le_mul_left _ h'
        _ = (k+1)^3 := by ring
    exact hk.trans h
  unfold cutoff SparseOneBank.cutoff SparseOneBank.ratio
  exact hp.trans ((Nat.le_mul_of_pos_left _ (by decide)).trans
    ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _)))

theorem combinedCertificate_of_uniform_cutoff {k : ℕ} (c : Demand k)
    (h : cutoff (k+1) (k+1) ≤ k+total c) : combinedCertificate c = true := by
  by_cases hq : 0 < (TreeEncoding.positiveDemandSites c).card
  · exact combinedCertificate_of_support_cutoff c hq
      ((cutoff_mono_support (support_card_le c)).trans h)
  · have hzero : ∀ x, c x = 0 := by
      intro x
      by_contra! hx
      have hx' : x ∈ TreeEncoding.positiveDemandSites c := by
        simp [TreeEncoding.positiveDemandSites, Nat.pos_of_ne_zero hx]
      exact hq (Finset.card_pos.mpr ⟨x,hx'⟩)
    have ht : total c = 0 := by simp [total, hzero]
    have hc := (order_le_uniform_cutoff k).trans h
    omega

theorem graceful_of_support_cutoff {k : ℕ} (H : Core k) (c : Demand k)
    (hq : 0 < (TreeEncoding.positiveDemandSites c).card)
    (h : cutoff (k+1) (TreeEncoding.positiveDemandSites c).card ≤ k+total c) :
    Graceful H c :=
  combinedCertificate_sound H c (combinedCertificate_of_support_cutoff c hq h)

theorem graceful_of_uniform_cutoff {k : ℕ} (H : Core k) (c : Demand k)
    (h : cutoff (k+1) (k+1) ≤ k+total c) : Graceful H c :=
  combinedCertificate_sound H c (combinedCertificate_of_uniform_cutoff c h)

end FixedCore.SparseSupport
