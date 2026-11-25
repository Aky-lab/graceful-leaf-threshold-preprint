import Next.PreparedSeed
import Next.MarkedCompletion

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- Completed rational preparation relative to the current distinguished root.
Only even additional leaves at marked vertices are used. -/
structure RootedPreparation (marks : Finset (Fin (k+1))) (v : Fin (k+1)) (δ : ℚ) where
  extra : Demand k
  even : ∀ x, Even (extra x)
  support : ∀ x ∉ marks, extra x=0
  seed : RationalSeed (Reserves.core H extra)
  maximum_one : ∃ x, seed.rank x=1
  bounded : ∀ x, seed.rank x ≤ 1
  bank_high : 1-δ ≤ seed.rank (Reserves.old extra v)
  marked : ∀ x ∈ marks,
    seed.rank (Reserves.old extra x) ≤ δ ∨ 1-δ ≤ seed.rank (Reserves.old extra x)

/-- All initial path cases feed the same fully checked marked completion. -/
theorem PreparedSeed.complete {v : Fin (k+1)} {δ : ℚ} (P : PreparedSeed H v δ)
    (marks : Finset (Fin (k+1))) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    Nonempty (RootedPreparation H marks v δ) := by
  have hready : P.seed.OrdinaryReady H := by
    intro i hi
    rcases P.ready i hi with h | h
    · exact Or.inl h
    · exact Or.inr h.2
  have hLow : P.seed.InactiveLow H δ := by
    intro i hi hn
    exact Or.inl ((P.ready i hi).resolve_left hn).1
  have hbound : ∀ x ∈ P.seed.S, x ≤ 1 := fun x hx => (P.bands x hx).1
  have hgood : P.seed.GoodMarks H marks δ := by
    intro i hi _
    exact (P.bands _ (P.seed.assigned i hi)).2
  obtain ⟨C⟩ := P.seed.completeMarked H marks hδ hδone hready hLow hbound hgood
  refine ⟨⟨C.reserves,C.even,C.support,C.seed,?_,C.bounded,?_,C.marked⟩⟩
  · refine ⟨Reserves.old C.reserves P.anchor.succ,?_⟩
    rw [C.old_rank P.anchor P.anchor_assigned,P.anchor_one]
  · obtain ⟨i,hi,hiv⟩ := P.selected_assigned
    have hr := C.old_rank i hi
    rw [hiv] at hr
    rw [hr]
    exact P.selected_high

/-- Distance one requires only the unit root edge; no path gadget is needed. -/
noncomputable def prepared_root_edge (a : Fin k) (ha : H.parent a=0)
    {δ : ℚ} (hδ : 0 < δ) : PreparedSeed H a.succ δ := by
  let P := PartialSeed.anchor H a ha
  refine ⟨P,a,by simp [P],by simp [P],⟨a,by simp [P],rfl⟩,?_,?_,?_⟩
  · rw [show P.rank a.succ=1 from PartialSeed.anchor_rank H a ha]
    linarith
  · intro x hx
    have hx1 : x=1 := hx
    subst x
    exact ⟨le_rfl,Or.inr (by linarith)⟩
  · intro i hi
    have hi' : i=a := by simpa [P] using hi
    subst i
    left
    simp [P]

/-- A complete actual-graph preparation when the selected marks are adjacent. -/
theorem exists_root_edge_preparation (a : Fin k) (ha : H.parent a=0)
    (marks : Finset (Fin (k+1))) {δ : ℚ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    Nonempty (RootedPreparation H marks a.succ δ) :=
  (prepared_root_edge H a ha hδ).complete H marks hδ hδone

/-- Every selected path of length at least three is now fully prepared on the
actual graph, including all marked side subtrees and exact even reserve growth. -/
theorem exists_long_preparation (v : Fin (k+1))
    (hlong : 3 ≤ (CorePaths.edges H v).length)
    (hreserve : ∃ z : Fin k, H.parent z=v)
    (marks : Finset (Fin (k+1))) {δ : ℚ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    Nonempty (RootedPreparation H marks v δ) := by
  obtain ⟨P⟩ := exists_initialPath H v hlong hreserve hδ
  exact (P.toPreparedSeed H).complete H marks hδ hδone

#print axioms PreparedSeed.complete
#print axioms exists_root_edge_preparation
#print axioms exists_long_preparation
end FixedCore.Next
