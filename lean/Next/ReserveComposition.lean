import Next.ReserveModel

namespace FixedCore.ReserveComposition

/-- An orientation-preserving core isomorphism, allowing different but
provably equal edge-count indices. -/
structure OrientedIso {a b : ℕ} (H : Core a) (K : Core b) where
  vertex : Fin (a+1) ≃ Fin (b+1)
  edge : Fin a ≃ Fin b
  parent_eq : ∀ i, vertex (H.parent i)=K.parent (edge i)
  child_eq : ∀ i, vertex i.succ=(edge i).succ

namespace OrientedIso
variable {a b : ℕ} {H : Core a} {K : Core b}

theorem size (e : OrientedIso H K) : a=b := by
  simpa using Fintype.card_congr e.edge

def symm (e : OrientedIso H K) : OrientedIso K H where
  vertex := e.vertex.symm
  edge := e.edge.symm
  parent_eq i := by
    have h := e.parent_eq (e.edge.symm i)
    simp only [e.edge.apply_symm_apply] at h
    exact e.vertex.symm_apply_eq.mpr h.symm
  child_eq i := by
    have h := e.child_eq (e.edge.symm i)
    simp only [e.edge.apply_symm_apply] at h
    exact e.vertex.symm_apply_eq.mpr h.symm

/-- Recover the repository's ordinary same-size undirected CoreIso. -/
def toCoreIso (e : OrientedIso H K) : CoreIso (e.size ▸ H) K := by
  have h := e.size
  subst b
  exact ⟨e.vertex,e.edge,fun i => Or.inl ⟨e.parent_eq i,e.child_eq i⟩⟩

end OrientedIso

variable {k : ℕ}

/-- Reclassifying reserved leaves as core vertices gives precisely the same
numbered rooted graph, including its orientation. -/
noncomputable def absorption (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    OrientedIso (Reserves.core H c)
      (Reserves.core (Reserves.core H r) (Reserves.residual c r)) := by
  let v := Equiv.ofBijective (Reserves.vertex c r)
    ⟨Reserves.vertex_injective c r,Reserves.vertex_surjective c r hr⟩
  let e := Equiv.ofBijective (Reserves.edge c r) (Reserves.edge_bijective c r hr)
  let V := (ReserveModel.vertexEquiv c).symm.trans (v.trans (ReserveModel.vertexEquiv (Reserves.residual c r)))
  let E := (ReserveModel.edgeEquiv c).symm.trans (e.trans (ReserveModel.edgeEquiv (Reserves.residual c r)))
  have hv (x : Vertex c) : V (ReserveModel.vertexEquiv c x)=
      ReserveModel.vertexEquiv (Reserves.residual c r) (Reserves.vertex c r x) := by simp [V,v]
  have he (x : Edge c) : E (ReserveModel.edgeEquiv c x)=
      ReserveModel.edgeEquiv (Reserves.residual c r) (Reserves.edge c r x) := by simp [E,e]
  refine ⟨V,E,?_,?_⟩
  · intro i
    obtain ⟨x,rfl⟩ := (ReserveModel.edgeEquiv c).surjective i
    rw [(ReserveModel.incidence H c x).1,hv,he]
    rw [(ReserveModel.incidence (Reserves.core H r) (Reserves.residual c r) _).1]
    rw [Reserves.ends_commute]
  · intro i
    obtain ⟨x,rfl⟩ := (ReserveModel.edgeEquiv c).surjective i
    rw [(ReserveModel.incidence H c x).2,hv,he]
    rw [(ReserveModel.incidence (Reserves.core H r) (Reserves.residual c r) _).2]
    rw [Reserves.ends_commute]

@[simp] theorem absorption_old (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i)
    (i : Fin (k+1)) :
    (absorption H c r hr).vertex (Reserves.old c i)=
      Reserves.old (Reserves.residual c r) (Reserves.old r i) := by
  change ReserveModel.vertexEquiv (Reserves.residual c r)
    (Reserves.vertex c r ((ReserveModel.vertexEquiv c).symm (Reserves.old c i)))=_
  rw [← ReserveModel.vertexEquiv_old c i,Equiv.symm_apply_apply]
  rfl

/-- Rewrite the residual demand without hiding the vertex-preservation law. -/
noncomputable def absorptionTo (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i)
    (s : Demand (k+total r)) (h : Reserves.residual c r=s) :
    OrientedIso (Reserves.core H c) (Reserves.core (Reserves.core H r) s) :=
  h ▸ absorption H c r hr

@[simp] theorem absorptionTo_old (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i)
    (s : Demand (k+total r)) (h : Reserves.residual c r=s) (i : Fin (k+1)) :
    (absorptionTo H c r hr s h).vertex (Reserves.old c i)=
      Reserves.old s (Reserves.old r i) := by
  subst s
  exact absorption_old H c r hr i

/-- All second-stage reserves at original vertices are added to the original
reserve vector. Second-stage reserves at already added leaves are disallowed. -/
def flat (r : Demand k) (s : Demand (k+total r)) : Demand k :=
  fun i => r i+s (Reserves.old r i)

theorem le_flat (r : Demand k) (s : Demand (k+total r)) (i : Fin (k+1)) :
    r i ≤ flat r s i := by simp [flat]

theorem residual_flat (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) : Reserves.residual (flat r s) r=s := by
  funext v
  obtain ⟨v,rfl⟩ := (ReserveModel.vertexEquiv r).surjective v
  rcases v with i | l
  · simp [flat]
  · simp [hs]

theorem size (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) :
    k+total r+total s=k+total (flat r s) := by
  have h := Reserves.edge_count (flat r s) r (le_flat r s)
  rwa [residual_flat r s hs] at h

/-- Flatten two rounds of reserves into one without changing the actual
rooted graph. The equivalence is built from the verified partition bijection,
so it does not depend on arbitrary details of finite leaf enumeration. -/
noncomputable def flatten (H : Core k) (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) :
    OrientedIso (Reserves.core (Reserves.core H r) s) (Reserves.core H (flat r s)) :=
  (absorptionTo H (flat r s) r (le_flat r s) s (residual_flat r s hs)).symm

@[simp] theorem flatten_old (H : Core k) (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) (i : Fin (k+1)) :
    (flatten H r s hs).vertex (Reserves.old s (Reserves.old r i))=
      Reserves.old (flat r s) i := by
  apply (absorptionTo H (flat r s) r (le_flat r s) s (residual_flat r s hs)).vertex.symm_apply_eq.mpr
  exact (absorptionTo_old H (flat r s) r (le_flat r s) s (residual_flat r s hs) i).symm

@[simp] theorem flatten_root (H : Core k) (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) :
    (flatten H r s hs).vertex 0=0 := flatten_old H r s hs 0

@[simp] theorem flatten_oldEdge (H : Core k) (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) (i : Fin k) :
    (flatten H r s hs).edge (Reserves.oldEdge s (Reserves.oldEdge r i))=
      Reserves.oldEdge (flat r s) i := by
  apply Fin.succ_injective
  rw [← (flatten H r s hs).child_eq]
  simp only [Reserves.oldEdge_child,flatten_old]

theorem total_flat (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) :
    total (flat r s)=total r+total s := by
  have h := size r s hs
  omega

theorem even_flat (r : Demand k) (s : Demand (k+total r))
    (hr : ∀ i, Even (r i)) (hs : ∀ i, Even (s i)) (i : Fin (k+1)) :
    Even (flat r s i) := (hr i).add (hs (Reserves.old r i))

noncomputable def coreIso (H : Core k) (r : Demand k) (s : Demand (k+total r))
    (hs : ∀ l : Leaf r, s (Reserves.added r l)=0) :
    CoreIso ((size r s hs) ▸ Reserves.core (Reserves.core H r) s) (Reserves.core H (flat r s)) :=
  (flatten H r s hs).toCoreIso

#print axioms flatten
#print axioms flatten_old
end FixedCore.ReserveComposition
