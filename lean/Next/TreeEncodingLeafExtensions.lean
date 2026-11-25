import Next.TreeEncoding

/-! Actual simple-graph and edge-set semantics for the core-plus-leaves model. -/
namespace FixedCore.TreeEncoding
variable {k : ℕ}

/-- The simple graph represented by a core and its pendant-leaf counts. -/
def extensionGraph (H : Core k) (c : Demand k) : SimpleGraph (Vertex c) where
  Adj a b := ∃ e : Edge c,
    (a = (ends H c e).1 ∧ b = (ends H c e).2) ∨
    (b = (ends H c e).1 ∧ a = (ends H c e).2)
  symm := fun _ _ ⟨e,he⟩ => ⟨e,he.symm⟩
  loopless := by
    constructor
    intro a ⟨e,he⟩
    rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
      exact ends_ne H c e (h₁.symm.trans h₂)

@[simp] theorem extensionGraph_old_old (H : Core k) (c : Demand k) (a b : Fin (k+1)) :
    (extensionGraph H c).Adj (.inl a) (.inl b) ↔ CoreDiameter.Adj H a b := by
  simp [extensionGraph, ends, CoreDiameter.Adj]

@[simp] theorem extensionGraph_old_leaf (H : Core k) (c : Demand k) (a : Fin (k+1))
    (l : Leaf c) : (extensionGraph H c).Adj (.inl a) (.inr l) ↔ a = l.1 := by
  simp [extensionGraph, ends]
  constructor
  · rintro ⟨x,h⟩
    exact (congrArg Sigma.fst h).symm
  · intro ha
    subst a
    exact ⟨l.2,rfl⟩

@[simp] theorem extensionGraph_leaf_old (H : Core k) (c : Demand k) (a : Fin (k+1))
    (l : Leaf c) : (extensionGraph H c).Adj (.inr l) (.inl a) ↔ a = l.1 := by
  rw [SimpleGraph.adj_comm, extensionGraph_old_leaf]

@[simp] theorem extensionGraph_leaf_leaf (H : Core k) (c : Demand k) (a b : Leaf c) :
    ¬ (extensionGraph H c).Adj (.inr a) (.inr b) := by
  simp [extensionGraph, ends]

def extensionEdge (H : Core k) (c : Demand k) (e : Edge c) : (extensionGraph H c).edgeSet :=
  ⟨s((ends H c e).1, (ends H c e).2), ⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩

theorem extensionEdge_bijective (H : Core k) (c : Demand k) :
    Function.Bijective (extensionEdge H c) := by
  constructor
  · intro a b hab
    have he := Sym2.eq_iff.mp (congrArg Subtype.val hab)
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [ends, Sum.inl.injEq] at he
        obtain ⟨hp,hc⟩ | ⟨hp,hc⟩ := he
        · exact congrArg Sum.inl (Fin.succ_injective _ hc)
        · have hi := H.earlier i
          have hj := H.earlier j
          have hp' := congrArg Fin.val hp
          have hc' := congrArg Fin.val hc
          simp only [Fin.val_succ] at *
          omega
      | inr l => simp [ends] at he
    | inr l =>
      cases b with
      | inl j => simp [ends] at he
      | inr m =>
        simp only [ends, Sum.inl.injEq, Sum.inr.injEq,
          Sum.inl.injEq, reduceCtorEq, and_false, or_false] at he
        exact congrArg Sum.inr he.2
  · rintro ⟨s,hs⟩
    induction s using Sym2.inductionOn with
    | _ a b =>
      change (extensionGraph H c).Adj a b at hs
      obtain ⟨e,he⟩ := hs
      refine ⟨e,Subtype.ext ?_⟩
      rcases he with ⟨hp,hc⟩ | ⟨hp,hc⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨hp.symm,hc.symm⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨hp.symm,hc.symm⟩)

noncomputable def extensionEdgeEquiv (H : Core k) (c : Demand k) :
    Edge c ≃ (extensionGraph H c).edgeSet :=
  Equiv.ofBijective (extensionEdge H c) (extensionEdge_bijective H c)

/-- A representation contains the actual vertex bijection and every adjacency. -/
abbrev Representation {V : Type*} (G : SimpleGraph V) (H : Core k) (c : Demand k) :=
  extensionGraph H c ≃g G

noncomputable def representationEdges {V : Type*} {G : SimpleGraph V}
    {H : Core k} {c : Demand k} (e : Representation G H c) : Edge c ≃ G.edgeSet :=
  (extensionEdgeEquiv H c).trans e.mapEdgeSet

@[simp] theorem representationEdges_incidence {V : Type*} {G : SimpleGraph V}
    {H : Core k} {c : Demand k} (e : Representation G H c) (a : Edge c) :
    (representationEdges e a).val = s(e (ends H c a).1, e (ends H c a).2) := rfl

 theorem representation_vertex_count {V : Type*} [Fintype V] {G : SimpleGraph V}
    {H : Core k} {c : Demand k} (e : Representation G H c) :
    Fintype.card V = k+total c+1 := by
  rw [← Fintype.card_congr e.toEquiv, vertex_card]

 theorem representation_edge_count {V : Type*} {G : SimpleGraph V}
    {H : Core k} {c : Demand k} (e : Representation G H c) :
    Nat.card G.edgeSet = k+total c := by
  rw [← Nat.card_congr (representationEdges e), Nat.card_eq_fintype_card, edge_card]

/-- Represented pendant vertices have actual degree one in the target graph. -/
theorem representation_leaf_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {H : Core k} {c : Demand k} (e : Representation G H c)
    (l : Leaf c) : G.degree (e (.inr l))=1 := by
  classical
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨e (.inl l.1),?_,?_⟩
  · exact e.map_rel_iff.mpr ((extensionGraph_leaf_old H c l.1 l).mpr rfl)
  · intro w hw
    obtain ⟨v,hv⟩ := e.toEquiv.surjective w
    change e v=w at hv
    subst w
    have ha := e.map_rel_iff.mp hw
    cases v with
    | inl i =>
      have hi := (extensionGraph_leaf_old H c i l).mp ha
      exact congrArg e (congrArg Sum.inl hi)
    | inr m => exact False.elim (extensionGraph_leaf_leaf H c l m ha)

#print axioms extensionEdge_bijective
#print axioms representationEdges_incidence
end FixedCore.TreeEncoding
