import Next.ReserveModel

/-! Reserve growth commutes with arbitrary undirected core isomorphisms,
including rerootings. All equal-size casts and old-vertex maps are explicit. -/
namespace FixedCore.CoreIso
variable {k : ℕ} {H K : Core k}

/-- Size equality for transporting a reserve vector along the vertex map. -/
theorem reserveSize (e : CoreIso H K) (r : Demand k) :
    k+total r = k+total (e.demand r) := by rw [e.total_demand]

noncomputable def reserveVertex (e : CoreIso H K) (r : Demand k) :
    Fin (k+total r+1) ≃ Fin (k+total (e.demand r)+1) :=
  (ReserveModel.vertexEquiv r).symm.trans
    ((e.vertexEquiv r).trans (ReserveModel.vertexEquiv (e.demand r)))

noncomputable def reserveEdge (e : CoreIso H K) (r : Demand k) :
    Fin (k+total r) ≃ Fin (k+total (e.demand r)) :=
  (ReserveModel.edgeEquiv r).symm.trans
    ((e.edgeEquiv r).trans (ReserveModel.edgeEquiv (e.demand r)))

@[simp] theorem reserveVertex_old (e : CoreIso H K) (r : Demand k) (i : Fin (k+1)) :
    e.reserveVertex r (Reserves.old r i) = Reserves.old (e.demand r) (e.vertex i) := by
  rw [← ReserveModel.vertexEquiv_old r i]
  simp only [reserveVertex,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact ReserveModel.vertexEquiv_old (e.demand r) (e.vertex i)

@[simp] theorem reserveVertex_added (e : CoreIso H K) (r : Demand k) (l : Leaf r) :
    e.reserveVertex r (Reserves.added r l) = Reserves.added (e.demand r) (e.leafEquiv r l) := by
  rw [← ReserveModel.vertexEquiv_added r l]
  simp only [reserveVertex,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact ReserveModel.vertexEquiv_added (e.demand r) (e.leafEquiv r l)

@[simp] theorem reserveEdge_old (e : CoreIso H K) (r : Demand k) (i : Fin k) :
    e.reserveEdge r (Reserves.oldEdge r i) = Reserves.oldEdge (e.demand r) (e.edge i) := by
  rw [← ReserveModel.edgeEquiv_old r i]
  simp only [reserveEdge,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact ReserveModel.edgeEquiv_old (e.demand r) (e.edge i)

@[simp] theorem reserveEdge_added (e : CoreIso H K) (r : Demand k) (l : Leaf r) :
    e.reserveEdge r (Reserves.addedEdge r l) = Reserves.addedEdge (e.demand r) (e.leafEquiv r l) := by
  rw [← ReserveModel.edgeEquiv_added r l]
  simp only [reserveEdge,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact ReserveModel.edgeEquiv_added (e.demand r) (e.leafEquiv r l)

theorem reserve_incidence (e : CoreIso H K) (r : Demand k) (i : Fin (k+total r)) :
    (e.reserveVertex r ((Reserves.core H r).parent i) =
        (Reserves.core K (e.demand r)).parent (e.reserveEdge r i) ∧
      e.reserveVertex r i.succ = (e.reserveEdge r i).succ) ∨
    (e.reserveVertex r ((Reserves.core H r).parent i) = (e.reserveEdge r i).succ ∧
      e.reserveVertex r i.succ = (Reserves.core K (e.demand r)).parent (e.reserveEdge r i)) := by
  obtain ⟨a,rfl⟩ := (ReserveModel.edgeEquiv r).surjective i
  have ev : ∀ v : Vertex r, e.reserveVertex r (ReserveModel.vertexEquiv r v) =
      ReserveModel.vertexEquiv (e.demand r) (e.vertexEquiv r v) := by
    intro v; simp [reserveVertex]
  have ee : e.reserveEdge r (ReserveModel.edgeEquiv r a) =
      ReserveModel.edgeEquiv (e.demand r) (e.edgeEquiv r a) := by simp [reserveEdge]
  rw [(ReserveModel.incidence H r a).1,(ReserveModel.incidence H r a).2,ev,ev,ee,
    (ReserveModel.incidence K (e.demand r) (e.edgeEquiv r a)).1,
    (ReserveModel.incidence K (e.demand r) (e.edgeEquiv r a)).2]
  rcases e.ends_transport r a with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨congrArg _ h₁,congrArg _ h₂⟩
  · exact Or.inr ⟨congrArg _ h₁,congrArg _ h₂⟩

private def castIso {m n : ℕ} {G : Core m} {L : Core n} (size : m=n)
    (v : Fin (m+1) ≃ Fin (n+1)) (e : Fin m ≃ Fin n)
    (h : ∀ i, (v (G.parent i)=L.parent (e i) ∧ v i.succ=(e i).succ) ∨
      (v (G.parent i)=(e i).succ ∧ v i.succ=L.parent (e i))) : CoreIso (size ▸ G) L := by
  subst n
  exact ⟨v,e,h⟩

@[simp] private theorem castIso_vertex {m n : ℕ} {G : Core m} {L : Core n} (size : m=n)
    (v : Fin (m+1) ≃ Fin (n+1)) (e : Fin m ≃ Fin n)
    (h : ∀ i, (v (G.parent i)=L.parent (e i) ∧ v i.succ=(e i).succ) ∨
      (v (G.parent i)=(e i).succ ∧ v i.succ=L.parent (e i))) (i : Fin (m+1)) :
    (castIso size v e h).vertex (Fin.cast (congrArg (fun n => n+1) size) i) = v i := by
  subst n
  rfl

/-- Lift the full actual core isomorphism through reserve growth. -/
noncomputable def reserveLift (e : CoreIso H K) (r : Demand k) :
    CoreIso (e.reserveSize r ▸ Reserves.core H r) (Reserves.core K (e.demand r)) :=
  castIso (e.reserveSize r) (e.reserveVertex r) (e.reserveEdge r) (e.reserve_incidence r)

@[simp] theorem reserveLift_old (e : CoreIso H K) (r : Demand k) (i : Fin (k+1)) :
    (e.reserveLift r).vertex
      (Fin.cast (congrArg (fun n => n+1) (e.reserveSize r)) (Reserves.old r i)) =
      Reserves.old (e.demand r) (e.vertex i) := by
  rw [reserveLift,castIso_vertex,reserveVertex_old]

/-- Explicit size equality when the transported demand is given another name. -/
theorem reserveSizeTo (e : CoreIso H K) (r s : Demand k) (h : e.demand r=s) :
    k+total r = k+total s := by rw [← h,e.total_demand]

noncomputable def reserveLiftTo (e : CoreIso H K) (r s : Demand k) (h : e.demand r=s) :
    CoreIso (e.reserveSizeTo r s h ▸ Reserves.core H r) (Reserves.core K s) := by
  subst s
  exact e.reserveLift r

@[simp] theorem reserveLiftTo_old (e : CoreIso H K) (r s : Demand k) (h : e.demand r=s)
    (i : Fin (k+1)) :
    (e.reserveLiftTo r s h).vertex
      (Fin.cast (congrArg (fun n => n+1) (e.reserveSizeTo r s h)) (Reserves.old r i)) =
      Reserves.old s (e.vertex i) := by
  subst s
  exact e.reserveLift_old r i

theorem demand_pullback (e : CoreIso H K) (s : Demand k) :
    e.demand (e.symm.demand s) = s := by
  funext i
  simp [demand,symm]

/-- Pull back reserves chosen after rerooting, then grow both graphs. -/
noncomputable def pullbackReserveLift (e : CoreIso H K) (s : Demand k) :
    CoreIso (e.reserveSizeTo (e.symm.demand s) s (e.demand_pullback s) ▸
      Reserves.core H (e.symm.demand s)) (Reserves.core K s) :=
  e.reserveLiftTo (e.symm.demand s) s (e.demand_pullback s)

@[simp] theorem pullbackReserveLift_old (e : CoreIso H K) (s : Demand k) (i : Fin (k+1)) :
    (e.pullbackReserveLift s).vertex
      (Fin.cast (congrArg (fun n => n+1)
        (e.reserveSizeTo (e.symm.demand s) s (e.demand_pullback s)))
          (Reserves.old (e.symm.demand s) i)) = Reserves.old s (e.vertex i) :=
  e.reserveLiftTo_old _ _ _ i

#print axioms reserveLift
#print axioms pullbackReserveLift_old
end FixedCore.CoreIso
