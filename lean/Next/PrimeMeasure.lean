import Next.PartialPrime
import Next.ReserveModel

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- Marked core children still awaiting a rank assignment. -/
def PartialSeed.missingMarks (P : PartialSeed H) (marks : Finset (Fin (k+1))) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.succ ∈ marks ∧ i ∉ P.edges)

@[simp] theorem PartialSeed.mem_missingMarks (P : PartialSeed H) (marks : Finset (Fin (k+1)))
    (i : Fin k) : i ∈ P.missingMarks H marks ↔ i.succ ∈ marks ∧ i ∉ P.edges := by
  simp [PartialSeed.missingMarks]

namespace PrimeMeasure
@[simp] theorem old_inj (r : Demand k) {i j : Fin (k+1)} :
    Reserves.old r i=Reserves.old r j ↔ i=j := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  · exact congrArg (Reserves.old r)

@[simp] theorem oldEdge_inj (r : Demand k) {i j : Fin k} :
    Reserves.oldEdge r i=Reserves.oldEdge r j ↔ i=j := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  · exact congrArg (Reserves.oldEdge r)

theorem old_ne_added (r : Demand k) (i : Fin (k+1)) (l : Leaf r) :
    Reserves.old r i≠Reserves.added r l := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=k+1+(Reserves.enumerate r l).val at hv
  have := i.isLt
  omega
end PrimeMeasure

namespace PartialSeed.PrimeExtension
variable {H : Core k} {P : PartialSeed H} {c : Fin k} {ε : ℚ}
    (E : P.PrimeExtension H c ε)

/-- Prime expansion assigns just its chosen original marked child. All other
missing marks survive through the canonical original-edge embedding. -/
theorem missingMarks_eq (marks : Finset (Fin (k+1))) :
    E.seed.missingMarks (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n))
      (marks.image (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n))) =
    ((P.missingMarks H marks).erase c).image
      (Reserves.oldEdge (FixedCore.Next.PrimeExtension.reserves c E.n)) := by
  classical
  let R := FixedCore.Next.PrimeExtension.reserves c E.n
  ext i
  obtain ⟨i,rfl⟩ := (ReserveModel.edgeEquiv R).surjective i
  rcases i with i | l
  · dsimp only [R]
    simp only [ReserveModel.edgeEquiv_old,PartialSeed.mem_missingMarks,
      Reserves.oldEdge_child,E.old_assigned]
    simp only [Finset.mem_image,PrimeMeasure.old_inj,PrimeMeasure.oldEdge_inj,
      exists_eq_right,Finset.mem_erase,PartialSeed.mem_missingMarks]
    tauto
  · simp only [ReserveModel.edgeEquiv_added,PartialSeed.mem_missingMarks,
      Reserves.addedEdge_child,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv,he⟩,_⟩
      exact False.elim (PrimeMeasure.old_ne_added R v l he)
    · rintro ⟨j,_,he⟩
      exact False.elim (FixedCore.Next.PrimeExtension.old_ne_added R j l he)

/-- A marked prime step reduces the number of missing marked children by one. -/
theorem missingMarks_card (marks : Finset (Fin (k+1))) (hc : c.succ ∈ marks) :
    (E.seed.missingMarks (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n))
      (marks.image (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n)))).card+1 =
      (P.missingMarks H marks).card := by
  classical
  rw [E.missingMarks_eq]
  have hinj : Function.Injective (Reserves.oldEdge (FixedCore.Next.PrimeExtension.reserves c E.n)) := by
    intro i j h
    exact (PrimeMeasure.oldEdge_inj _).mp h
  rw [Finset.card_image_of_injective _ hinj]
  have hm : c ∈ P.missingMarks H marks := (P.mem_missingMarks H marks c).mpr ⟨hc,E.original_unassigned⟩
  exact Finset.card_erase_add_one hm

/-- The number of unassigned actual core edges stays constant: one original
edge and n reserves are assigned, while n+1 reserves have been introduced. -/
theorem unassigned_count :
    k+total (FixedCore.Next.PrimeExtension.reserves c E.n)-E.seed.edges.card=k-P.edges.card := by
  have ht := E.total_reserves
  have hg := E.edge_growth
  omega

/-- A marked prime step strictly decreases the combined termination measure. -/
theorem measure_decreases (marks : Finset (Fin (k+1))) (hc : c.succ ∈ marks) :
    (k+total (FixedCore.Next.PrimeExtension.reserves c E.n)-E.seed.edges.card) +
      (E.seed.missingMarks (Reserves.core H (FixedCore.Next.PrimeExtension.reserves c E.n))
        (marks.image (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n)))).card <
      (k-P.edges.card)+(P.missingMarks H marks).card := by
  rw [E.unassigned_count]
  have h := E.missingMarks_card marks hc
  omega

end PartialSeed.PrimeExtension
#print axioms PartialSeed.PrimeExtension.measure_decreases
end FixedCore.Next
