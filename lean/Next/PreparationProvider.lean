import Next.PathPreparation
import Next.PreparationReserves
import Next.RootedPreparationCertificate
import Next.ShapeException

namespace FixedCore.ThresholdAssembly
open Next
variable {k : ℕ} (H : Core k)

/-- A pendant alternative on the absorbed graph has original path edges
whenever its selected endpoint is an original vertex. -/
theorem reserved_pendant_exception (marks : Finset (Fin (k+1))) (r : Demand k)
    (hr : ∀x∈marks,2≤r x) (v : Fin (k+1))
    (a b : Fin (k+total r))
    (ha : (Reserves.core H r).parent a=0)
    (hb : (Reserves.core H r).parent b=a.succ)
    (hv : Reserves.old r v=b.succ)
    (hs : DistanceTwoShape.PendantShape (Reserves.core H r) a b) :
    Nonempty (ShapeException H marks 0 v) := by
  have hbval : b.val < k := by
    have hvv := congrArg Fin.val hv
    have := v.isLt
    simp only [Reserves.old,Absorption.old_val,Fin.val_succ] at hvv
    omega
  let b₀ : Fin k := ⟨b.val,hbval⟩
  have hbb : Reserves.oldEdge r b₀=b := Fin.ext rfl
  have haval : a.val < k := by
    have h := (Reserves.core H r).earlier b
    rw [hb] at h
    simp only [Fin.val_succ] at h
    omega
  let a₀ : Fin k := ⟨a.val,haval⟩
  have haa : Reserves.oldEdge r a₀=a := Fin.ext rfl
  have ha₀ : H.parent a₀=0 := by
    rw [← haa,Reserves.oldEdge_parent] at ha
    exact Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) ha)
  have hb₀ : H.parent b₀=a₀.succ := by
    rw [← hbb,← haa,Reserves.oldEdge_parent,Reserves.oldEdge_child] at hb
    exact Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) hb)
  have hv₀ : v=b₀.succ := Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) hv)
  subst v
  apply shapeException_of_reserved_pendant H r a₀ b₀ ha₀ hb₀ _ marks hr
  simpa [haa,hbb] using hs

/-- Full preparation with the first selected vertex already at the root. -/
theorem rooted_tableEntry (marks : Finset (Fin (k+1))) (v : Fin (k+1))
    (hv : v≠0) (hvm : v∈marks) (parity : Fin (k+1)→Fin 2)
    {δ : ℚ} (hδ : 0<δ) (hδone : δ≤1) :
    Nonempty (NearEndCertificate H marks 0 v parity δ ⊕ ShapeException H marks 0 v) := by
  classical
  let r := initialReserves marks parity
  let J := Reserves.core H r
  have hr : ∀x∈marks,2≤r x := by
    intro x hx
    simp [r,initialReserves,hx]
  have hv' : Reserves.old r v ≠ 0 := by
    intro he
    apply hv
    exact Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) he)
  obtain ⟨i,j,hij,hi,hj⟩ := reserve_two_children H r v (hr v hvm)
  rcases rooted_preparation_or_pendant J (Reserves.old r v) hv' ⟨i,hi⟩
    (marks.image (Reserves.old r)) hδ hδone with hP | hP | hX
  · obtain ⟨P⟩ := hP
    obtain ⟨C⟩ := nearEndCertificate_of_rootedPreparation marks 0 v parity hδ.le
      J (CoreIso.refl J) 0 v (Or.inl ⟨rfl,rfl⟩) rfl P
    exact ⟨Sum.inl C⟩
  · obtain ⟨K,e,he,⟨P⟩⟩ := hP
    have hmarks : marks.image (fun x => e.vertex (Reserves.old r x)) =
        (marks.image (Reserves.old r)).image e.vertex := by rw [Finset.image_image]; rfl
    have P' : RootedPreparation K
        (marks.image (fun x => e.vertex (Reserves.old r x)))
        (e.vertex (Reserves.old r 0)) δ := by simpa only [hmarks] using P
    obtain ⟨C⟩ := nearEndCertificate_of_rootedPreparation marks 0 v parity hδ.le
      K e v 0 (Or.inr ⟨rfl,rfl⟩) he P'
    exact ⟨Sum.inl C⟩
  · obtain ⟨a,b,ha,hb,hv,hs⟩ := hX
    obtain ⟨X⟩ := reserved_pendant_exception H marks r hr v a b ha hb hv hs
    exact ⟨Sum.inr X⟩

/-- The complete marked preparation lemma, with no supplied preparation
oracle: every finite core and every marked set admit the finite table. -/
theorem allPreparation (marks : Finset (Fin (k+1))) : Preparation H marks := by
  classical
  intro δ hδ hδsmall index
  obtain ⟨⟨⟨u,v⟩,hu,hv,huv⟩,parity⟩ := index
  obtain ⟨J,e,he⟩ := Reroot.exists_reroot H u
  have hvzero : e.vertex v ≠ 0 := by
    intro hv0
    exact huv (e.vertex.injective (he.trans hv0.symm))
  have hvm : e.vertex v ∈ marks.image e.vertex := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  obtain ⟨C⟩ := rooted_tableEntry J (marks.image e.vertex) (e.vertex v)
    hvzero hvm (fun x => parity (e.vertex.symm x)) hδ (by linarith)
  rcases C with C | X
  · have C' : NearEndCertificate J (marks.image e.vertex) (e.vertex u) (e.vertex v)
        (fun x => parity (e.vertex.symm x)) δ := by rw [he]; exact C
    exact ⟨Sum.inl (C'.pullback e)⟩
  · have X' : ShapeException J (marks.image e.vertex) (e.vertex u) (e.vertex v) := by
      rw [he]; exact X
    exact ⟨Sum.inr (ShapeException.pullback H e X')⟩

#print axioms rooted_tableEntry
#print axioms allPreparation
end FixedCore.ThresholdAssembly
