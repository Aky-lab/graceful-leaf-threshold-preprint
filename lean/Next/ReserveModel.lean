import Next.Reserves
import Next.CoreIso

namespace FixedCore.ReserveModel
variable {k : ℕ}

/-- Canonical finite numbering of the vertices of a leaf extension. -/
noncomputable def vertexEquiv (r : Demand k) : Vertex r ≃ Fin (k+total r+1) :=
  ((Equiv.sumCongr (Equiv.refl _) (Reserves.enumerate r)).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- Canonical finite numbering of the edges of a leaf extension. -/
noncomputable def edgeEquiv (r : Demand k) : Edge r ≃ Fin (k+total r) :=
  (Equiv.sumCongr (Equiv.refl _) (Reserves.enumerate r)).trans finSumFinEquiv

@[simp] theorem vertexEquiv_old (r : Demand k) (i : Fin (k+1)) :
    vertexEquiv r (.inl i) = Reserves.old r i := by apply Fin.ext; rfl

@[simp] theorem vertexEquiv_added (r : Demand k) (l : Leaf r) :
    vertexEquiv r (.inr l) = Reserves.added r l := by apply Fin.ext; rfl

@[simp] theorem edgeEquiv_old (r : Demand k) (i : Fin k) :
    edgeEquiv r (.inl i) = Reserves.oldEdge r i := by apply Fin.ext; rfl

@[simp] theorem edgeEquiv_added (r : Demand k) (l : Leaf r) :
    edgeEquiv r (.inr l) = Reserves.addedEdge r l := by apply Fin.ext; rfl

/-- The numbered core is exactly the original tree with its reserved leaves. -/
theorem incidence (H : Core k) (r : Demand k) (e : Edge r) :
    (Reserves.core H r).parent (edgeEquiv r e) = vertexEquiv r (ends H r e).1 ∧
      (edgeEquiv r e).succ = vertexEquiv r (ends H r e).2 := by
  cases e with
  | inl i => simp [ends]
  | inr l => simp [ends]

end FixedCore.ReserveModel
