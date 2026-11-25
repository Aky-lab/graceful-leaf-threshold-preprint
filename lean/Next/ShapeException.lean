import Next.DistanceTwoShape
import Next.ThresholdAssembly
import Next.ReserveModel

/-! Exact exceptional-shape certificates, including endpoint and mark data. -/
namespace FixedCore
open DistanceTwoShape

namespace ThresholdAssembly
variable {k : ℕ} (H : Core k)

/-- The actual pendant configuration has the exact, narrower exception
required by the preparation theorem, not just a sufficient graceful solver. -/
theorem shapeException_of_pendant (a b : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (shape : PendantShape H a b) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, x=0 ∨ x=b.succ) :
    Nonempty (ShapeException H marks 0 b.succ) := by
  classical
  have hab : a≠b := by
    intro h; subst b
    have he := H.earlier a
    rw [hb] at he
    simp at he
  let e := edgeEquiv H a b hab
  let v := childEquiv e
  have size : k=2+total (reserves H a b) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin] using h
  have hp : ∀ i, v (H.parent i)=(Reserves.core pathTwo (reserves H a b)).parent (e i) := by
    intro i
    by_cases hia : i=a
    · subst i
      simp [v,e,ha,pathTwo]
      rfl
    · by_cases hib : i=b
      · subst i
        simp [v,e,hb,pathTwo]
      · have hj := (shape i hia hib).1
        let j : Other a b := ⟨i,hia,hib⟩
        have hei : e i=Reserves.addedEdge (reserves H a b) (leavesEquiv H a b j) :=
          edgeEquiv_other H a b hab j
        rw [hei,Reserves.addedEdge_parent,leavesEquiv_parent]
        rcases hj with hj | hj
        · simp [v,hj,side,j]
          rfl
        · have hn : H.parent i ≠ 0 := by rw [hj]; exact Fin.succ_ne_zero _
          simp [v,e,hj,side,j]
  let iso := isoOfEquivalences size v e hp (fun _ => rfl)
  have hzero : (iso.vertex (Fin.cast (congrArg (fun n => n+1) size) 0)).val=0 := by
    rw [isoOfEquivalences_vertex]
    rfl
  have hbank : (iso.vertex (Fin.cast (congrArg (fun n => n+1) size) b.succ)).val=2 := by
    rw [isoOfEquivalences_vertex]
    change (edgeEquiv H a b hab b).val+1=2
    rw [edgeEquiv_b]
    rfl
  let G : ExceptionalReserves.Certificate H marks :=
    { smallCore := pathTwo
      reserves := reserves H a b
      size := size
      iso := iso
      shape := by
        intro x hx
        rcases hmarks x hx with rfl | rfl
        · rw [hzero]; omega
        · rw [hbank]; omega }
  refine ⟨{
    graph := G
    path_core := rfl
    no_middle_leaves := reserves_middle H a b
    marks_at_ends := ?_
    selected_ends := Or.inl ⟨hzero,hbank⟩ }⟩
  intro x hx
  rcases hmarks x hx with rfl | rfl
  · exact Or.inl hzero
  · exact Or.inr hbank

/-- Exact exception certificates are invariant under an arbitrary reindexing
or rerooting of the original graph. -/
noncomputable def ShapeException.pullback {H K : Core k} (e : CoreIso H K)
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    (X : ShapeException K (marks.image e.vertex) (e.vertex u) (e.vertex v)) :
    ShapeException H marks u v := by
  classical
  rcases X with ⟨⟨G,r,size,iso,shape⟩,hG,hm,hmarks,hends⟩
  subst k
  refine {
    graph := {
      smallCore := G
      reserves := r
      size := rfl
      iso := e.trans iso
      shape := ?_ }
    path_core := hG
    no_middle_leaves := hm
    marks_at_ends := ?_
    selected_ends := ?_ }
  · intro x hx
    exact shape (e.vertex x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · intro x hx
    exact hmarks (e.vertex x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · exact hends

/-- Adding leaves cannot hide a non-pendant edge in the original core. -/
theorem pendant_of_reserved (r : Demand k) (a b : Fin k)
    (shape : PendantShape (Reserves.core H r) (Reserves.oldEdge r a) (Reserves.oldEdge r b)) :
    PendantShape H a b := by
  intro i hia hib
  have hii : Reserves.oldEdge r i ≠ Reserves.oldEdge r a := by
    intro h
    exact hia (Fin.ext (congrArg (fun x : Fin (k+total r) => x.val) h))
  have hib' : Reserves.oldEdge r i ≠ Reserves.oldEdge r b := by
    intro h
    exact hib (Fin.ext (congrArg (fun x : Fin (k+total r) => x.val) h))
  obtain ⟨hp,hleaf⟩ := shape (Reserves.oldEdge r i) hii hib'
  refine ⟨?_,?_⟩
  · rw [Reserves.oldEdge_parent,Reserves.oldEdge_child] at hp
    rcases hp with hp | hp
    · left
      apply Fin.ext
      exact congrArg (fun x : Fin (k+total r+1) => x.val) hp
    · right
      apply Fin.ext
      exact congrArg (fun x : Fin (k+total r+1) => x.val) hp
  · intro j hj
    apply hleaf (Reserves.oldEdge r j)
    rw [Reserves.oldEdge_parent,Reserves.oldEdge_child,hj]

/-- Two reserved children exclude marks at the middle or pendant leaves. -/
theorem marked_end_of_reserved_pendant (r : Demand k) (a b : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (shape : PendantShape (Reserves.core H r) (Reserves.oldEdge r a) (Reserves.oldEdge r b))
    (x : Fin (k+1)) (hx : 2 ≤ r x) : x=0 ∨ x=b.succ := by
  let l₀ : Leaf r := ⟨x,⟨0,by omega⟩⟩
  let l₁ : Leaf r := ⟨x,⟨1,by omega⟩⟩
  have hne : Reserves.addedEdge r l₀ ≠ Reserves.addedEdge r l₁ := by
    intro h
    have he : ReserveModel.edgeEquiv r (.inr l₀)=ReserveModel.edgeEquiv r (.inr l₁) := by
      simpa using h
    have hl : l₀=l₁ := Sum.inr.inj ((ReserveModel.edgeEquiv r).injective he)
    have hv := congrArg (fun l : Leaf r => l.2.val) hl
    norm_num [l₀,l₁] at hv
  have hp₀ : (Reserves.core H r).parent (Reserves.oldEdge r a)=0 := by
    rw [Reserves.oldEdge_parent,ha]
    rfl
  have hp₁ : (Reserves.core H r).parent (Reserves.oldEdge r b)=
      (Reserves.oldEdge r a).succ := by
    rw [Reserves.oldEdge_parent,Reserves.oldEdge_child,hb]
  have hend := branching_site_endpoint (Reserves.core H r)
    (Reserves.oldEdge r a) (Reserves.oldEdge r b) hp₀ hp₁ shape (Reserves.old r x)
    ⟨Reserves.addedEdge r l₀,Reserves.addedEdge r l₁,hne,
      Reserves.addedEdge_parent H r l₀,Reserves.addedEdge_parent H r l₁⟩
  rw [Reserves.oldEdge_child] at hend
  rcases hend with h | h
  · exact Or.inl (Fin.ext (congrArg (fun y : Fin (k+total r+1) => y.val) h))
  · exact Or.inr (Fin.ext (congrArg (fun y : Fin (k+total r+1) => y.val) h))

/-- The exact original-core exception follows from the pendant alternative
on its reserved augmentation. All added reserves may now be forgotten. -/
theorem shapeException_of_reserved_pendant (r : Demand k) (a b : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (shape : PendantShape (Reserves.core H r) (Reserves.oldEdge r a) (Reserves.oldEdge r b))
    (marks : Finset (Fin (k+1))) (hr : ∀ x ∈ marks, 2 ≤ r x) :
    Nonempty (ShapeException H marks 0 b.succ) :=
  shapeException_of_pendant H a b ha hb (pendant_of_reserved H r a b shape) marks
    (fun x hx => marked_end_of_reserved_pendant H r a b ha hb shape x (hr x hx))

#print axioms shapeException_of_pendant
#print axioms ShapeException.pullback
#print axioms pendant_of_reserved
end ThresholdAssembly
end FixedCore
