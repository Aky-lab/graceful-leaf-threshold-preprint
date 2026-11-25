import Next.SparseParityScan
import Next.TreeEncodingSparseOneBank

namespace FixedCore.SparseEffective

def namedQuickCertificate {V : Type*} [Fintype V] (sites : List V) (c : V → ℕ) (N : ℕ) : Bool :=
  SparseParityScan.accepts sites c (SparseOneBank.namedCutoff 1 c) N

theorem namedQuickCertificate_iff {V : Type*} [Fintype V]
    (sites : List V) (c : V → ℕ) (N : ℕ) :
    namedQuickCertificate sites c N = true ↔
      ∃ x ∈ sites, SparseOneBank.namedCutoff 1 c x ≤ N := by
  exact SparseParityScan.accepts_iff sites c _ N
    (fun x _ y _ => SparseOneBank.namedCutoff_sameParity 1 c x y)

theorem namedQuickCertificate_sound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (sites : List V) (c : V → ℕ)
    (h : namedQuickCertificate sites c (Nat.card (TreeEncoding.leafExtension G c).edgeSet) = true) :
    TreeEncoding.GraphGraceful (TreeEncoding.leafExtension G c) := by
  obtain ⟨x,_,hx⟩ := (namedQuickCertificate_iff sites c _).mp h
  exact TreeEncoding.sparse_leaf_extension hG c x hx

/-- Low-cost numerical gate directly on a numbered demand vector: no rerooting,
graph edge enumeration, or exact graceful search is executed by this test. -/
def quickCertificate {k : ℕ} (c : Demand k) : Bool :=
  namedQuickCertificate (List.finRange (k+1)) c (k+total c)

theorem quickCertificate_iff {k : ℕ} (c : Demand k) :
    quickCertificate c = true ↔ ∃ x, SparseOneBank.namedCutoff 1 c x ≤ k+total c := by
  simp [quickCertificate,namedQuickCertificate_iff]

theorem quickCertificate_sound {k : ℕ} (H : Core k) (c : Demand k)
    (h : quickCertificate c = true) : Graceful H c := by
  let G := CoreDiameter.graph H
  have hG := TreeEncoding.graph_isTree H
  let e : CoreDiameter.graph H ≃g G := RelIso.refl _
  have he := TreeEncoding.representation_edge_count (TreeEncoding.leafExtensionIso e c)
  have hc : namedQuickCertificate (List.finRange (k+1)) c
      (Nat.card (TreeEncoding.leafExtension G c).edgeSet) = true := by
    rw [he]
    exact h
  exact (TreeEncoding.graphGraceful_iff_representation
    (TreeEncoding.leafExtensionIso e c)).mp (namedQuickCertificate_sound hG _ c hc)

#print axioms namedQuickCertificate_iff
#print axioms quickCertificate_sound

end FixedCore.SparseEffective
