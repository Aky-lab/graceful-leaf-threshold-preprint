import Next.InitialAlternatives
import Next.PreparationCompletion

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- Complete initial-path dichotomy for every distinct selected endpoint.
The two-child assumption is only needed to identify the exceptional marks. -/
theorem initial_prepared_or_exception (v : Fin (k+1)) (hv : v≠0)
    (hreserve : ∃ z : Fin k, H.parent z=v) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, ∃ i j : Fin k, i≠j ∧ H.parent i=x ∧ H.parent j=x)
    {δ : ℚ} (hδ : 0 < δ) :
    Nonempty (PreparedSeed H v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (PreparedSeed K (e.vertex 0) δ)) ∨
      Nonempty (ExceptionalReserves.Certificate H marks) := by
  by_cases hlong : 3 ≤ (CorePaths.edges H v).length
  · obtain ⟨P⟩ := exists_initialPath H v hlong hreserve hδ
    exact Or.inl ⟨P.toPreparedSeed H⟩
  by_cases htwo : (CorePaths.edges H v).length=2
  · exact distanceTwo_prepared_or_exception H v htwo marks hmarks hδ
  have hne : CorePaths.edges H v ≠ [] := by
    intro he
    have hh := CorePaths.target_mem H v
    rw [CorePaths.path_eq_edges,he] at hh
    simp only [List.map_nil,List.mem_singleton] at hh
    exact hv hh
  have hlen : (CorePaths.edges H v).length=1 := by
    have := List.length_pos_iff.mpr hne
    omega
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hlen
  have hpa := CorePaths.first_edge_parent H v a [] ha
  have hav : a.succ=v := by
    have hh := CorePaths.path_last H v
    rw [CorePaths.path_eq_edges,ha] at hh
    simpa using hh
  exact Or.inl ⟨hav ▸ prepared_root_edge H a hpa hδ⟩

/-- The entire preparation lemma on a rooted reserve-augmented core: either
finish on this root, interchange the selected endpoints and finish there, or
produce the explicit exceptional certificate. No initial certificate is assumed. -/
theorem rooted_preparation_or_exception (v : Fin (k+1)) (hv : v≠0)
    (hreserve : ∃ z : Fin k, H.parent z=v) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, ∃ i j : Fin k, i≠j ∧ H.parent i=x ∧ H.parent j=x)
    {δ : ℚ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    Nonempty (RootedPreparation H marks v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (RootedPreparation K (marks.image e.vertex) (e.vertex 0) δ)) ∨
      Nonempty (ExceptionalReserves.Certificate H marks) := by
  rcases initial_prepared_or_exception H v hv hreserve marks hmarks hδ with
    hP | ⟨K,e,hroot,P⟩ | hexception
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.complete H marks hδ hδone)
  · obtain ⟨P⟩ := P
    exact Or.inr (Or.inl ⟨K,e,hroot,P.complete K (marks.image e.vertex) hδ hδone⟩)
  · exact Or.inr (Or.inr hexception)

/-- The unified initial construction with the exact selected pendant shape
retained, rather than forgetting its endpoints in a generic exception certificate. -/
theorem initial_prepared_or_pendant (v : Fin (k+1)) (hv : v≠0)
    (hreserve : ∃ z : Fin k, H.parent z=v) {δ : ℚ} (hδ : 0 < δ) :
    Nonempty (PreparedSeed H v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (PreparedSeed K (e.vertex 0) δ)) ∨
      (∃ a b : Fin k, H.parent a=0 ∧ H.parent b=a.succ ∧ v=b.succ ∧
        DistanceTwoShape.PendantShape H a b) := by
  by_cases hlong : 3 ≤ (CorePaths.edges H v).length
  · obtain ⟨P⟩ := exists_initialPath H v hlong hreserve hδ
    exact Or.inl ⟨P.toPreparedSeed H⟩
  by_cases htwo : (CorePaths.edges H v).length=2
  · exact distanceTwo_prepared_or_pendant H v htwo hδ
  have hne : CorePaths.edges H v ≠ [] := by
    intro he
    have hh := CorePaths.target_mem H v
    rw [CorePaths.path_eq_edges,he] at hh
    simp only [List.map_nil,List.mem_singleton] at hh
    exact hv hh
  have hlen : (CorePaths.edges H v).length=1 := by
    have := List.length_pos_iff.mpr hne
    omega
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hlen
  have hpa := CorePaths.first_edge_parent H v a [] ha
  have hav : a.succ=v := by
    have hh := CorePaths.path_last H v
    rw [CorePaths.path_eq_edges,ha] at hh
    simpa using hh
  exact Or.inl ⟨hav ▸ prepared_root_edge H a hpa hδ⟩

/-- Fully completed preparation with an exact geometric exception. -/
theorem rooted_preparation_or_pendant (v : Fin (k+1)) (hv : v≠0)
    (hreserve : ∃ z : Fin k, H.parent z=v) (marks : Finset (Fin (k+1)))
    {δ : ℚ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    Nonempty (RootedPreparation H marks v δ) ∨
      (∃ K : Core k, ∃ e : CoreIso H K, e.vertex v=0 ∧
        Nonempty (RootedPreparation K (marks.image e.vertex) (e.vertex 0) δ)) ∨
      (∃ a b : Fin k, H.parent a=0 ∧ H.parent b=a.succ ∧ v=b.succ ∧
        DistanceTwoShape.PendantShape H a b) := by
  rcases initial_prepared_or_pendant H v hv hreserve hδ with
    hP | ⟨K,e,hroot,P⟩ | hexception
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.complete H marks hδ hδone)
  · obtain ⟨P⟩ := P
    exact Or.inr (Or.inl ⟨K,e,hroot,P.complete K (marks.image e.vertex) hδ hδone⟩)
  · exact Or.inr (Or.inr hexception)

#print axioms initial_prepared_or_exception
#print axioms rooted_preparation_or_exception
#print axioms initial_prepared_or_pendant
#print axioms rooted_preparation_or_pendant
end FixedCore.Next
