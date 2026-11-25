import Next.SparseQuickCertificate
import Next.TreeEncodingPolynomialDegreeSevenComplete

namespace FixedCore.SparseEffective

def twoSiteTrigger {k : ℕ} (c : Demand k) : ℕ :=
  10^9*((TreeEncoding.positiveDemandSites c).card+2)^2*(k+2)

/-- Count the qualifying vertices, not demand multiplicity. -/
def twoSiteCertificate {k : ℕ} (c : Demand k) : Bool :=
  decide (1 < ((Finset.univ : Finset (Fin (k+1))).filter
    (fun x => twoSiteTrigger c ≤ c x)).card)

theorem twoSiteCertificate_iff {k : ℕ} (c : Demand k) :
    twoSiteCertificate c = true ↔
      ∃ u v, u ≠ v ∧ twoSiteTrigger c ≤ c u ∧ twoSiteTrigger c ≤ c v := by
  simp only [twoSiteCertificate, decide_eq_true_eq, Finset.one_lt_card,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨u,hu,v,hv,huv⟩ => ⟨u,v,huv,hu,hv⟩,
    fun ⟨u,v,huv,hu,hv⟩ => ⟨u,hu,v,hv,huv⟩⟩

theorem twoSiteCertificate_sound {k : ℕ} (H : Core k) (c : Demand k)
    (h : twoSiteCertificate c = true) : Graceful H c := by
  let G := CoreDiameter.graph H
  let e : CoreDiameter.graph H ≃g G := RelIso.refl _
  obtain ⟨u,v,huv,hu,hv⟩ := (twoSiteCertificate_iff c).mp h
  apply (TreeEncoding.graphGraceful_iff_representation
    (TreeEncoding.leafExtensionIso e c)).mp
  apply TreeEncoding.poly_degree_seven (TreeEncoding.graph_isTree H) c
  right
  exact ⟨u,v,huv,by simpa [twoSiteTrigger] using hu,by simpa [twoSiteTrigger] using hv⟩

/-- Either independently sound sufficient certificate can prune exact search. -/
def combinedCertificate {k : ℕ} (c : Demand k) : Bool :=
  quickCertificate c || twoSiteCertificate c

theorem combinedCertificate_sound {k : ℕ} (H : Core k) (c : Demand k)
    (h : combinedCertificate c = true) : Graceful H c := by
  have he : quickCertificate c = true ∨ twoSiteCertificate c = true := by
    simpa only [combinedCertificate,Bool.or_eq_true] using h
  exact he.elim (quickCertificate_sound H c) (twoSiteCertificate_sound H c)

#print axioms twoSiteCertificate_sound
#print axioms combinedCertificate_sound

end FixedCore.SparseEffective
