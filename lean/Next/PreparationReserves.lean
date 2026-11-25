import Next.PreparationCompletion
import Next.ReserveIso

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- Absorbing leaves does not change any original root-to-vertex path. -/
theorem reserve_edges (r : Demand k) (v : Fin (k+1)) :
    CorePaths.edges (Reserves.core H r) (Reserves.old r v) =
      (CorePaths.edges H v).map (Reserves.oldEdge r) := by
  induction hv : v.val using Nat.strong_induction_on generalizing v with
  | h n ih =>
    cases v using Fin.cases with
    | zero => simp [show Reserves.old r 0=0 from rfl]
    | succ i =>
      rw [← Reserves.oldEdge_child, CorePaths.edges_succ, Reserves.oldEdge_parent,
        CorePaths.edges_succ, List.map_append]
      rw [ih (H.parent i).val (by have := H.earlier i; simp only [Fin.val_succ] at hv; omega)
        (H.parent i) rfl]
      rfl

@[simp] theorem reserve_distance (r : Demand k) (v : Fin (k+1)) :
    (CorePaths.edges (Reserves.core H r) (Reserves.old r v)).length =
      (CorePaths.edges H v).length := by rw [reserve_edges]; simp

/-- Two prescribed reserve leaves provide two distinct actual child edges. -/
theorem reserve_two_children (r : Demand k) (v : Fin (k+1)) (hr : 2 ≤ r v) :
    ∃ i j : Fin (k+total r), i≠j ∧
      (Reserves.core H r).parent i=Reserves.old r v ∧
      (Reserves.core H r).parent j=Reserves.old r v := by
  let l₀ : Leaf r := ⟨v,⟨0,by omega⟩⟩
  let l₁ : Leaf r := ⟨v,⟨1,by omega⟩⟩
  refine ⟨Reserves.addedEdge r l₀,Reserves.addedEdge r l₁,?_,by simp [l₀],by simp [l₁]⟩
  intro he
  have he' : Reserves.enumerate r l₀=Reserves.enumerate r l₁ := by
    apply Fin.ext
    have := congrArg Fin.val he
    simp only [Reserves.addedEdge] at this
    omega
  have hl := (Reserves.enumerate r).injective he'
  have := congrArg (fun l : Leaf r => l.2.val) hl
  norm_num [l₀,l₁] at this

/-- Every original marked vertex has the two-child reserve needed by path
preparation, with no assumption on its original degree. -/
theorem reserve_marks_two_children (marks : Finset (Fin (k+1))) (r : Demand k)
    (hr : ∀v∈marks,2≤r v) :
    ∀x∈marks.image (Reserves.old r), ∃i j : Fin (k+total r), i≠j ∧
      (Reserves.core H r).parent i=x ∧ (Reserves.core H r).parent j=x := by
  classical
  intro x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  exact reserve_two_children H r v (hr v hv)

#print axioms reserve_edges
#print axioms reserve_marks_two_children
end FixedCore.Next
