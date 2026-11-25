import Next.InternalCoreRepresentation
import Next.PolynomialRootAssembly

/-! Labeling statements on ordinary finite simple graphs, and transport from
actual core/leaf representations. -/
namespace FixedCore.TreeEncoding
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Literal bijective vertex palette and exact differences along actual edges. -/
def GraphLabeling (G : SimpleGraph V) (f : V → Fin (Nat.card G.edgeSet+1)) : Prop :=
  Function.Bijective f ∧ ∀ d : Fin (Nat.card G.edgeSet),
    ∃ a b : V, G.Adj a b ∧ diff (f a).val (f b).val = d.val+1

def GraphGraceful (G : SimpleGraph V) : Prop := ∃ f, GraphLabeling G f

/-- Every vertex of actual degree at least two has a label divisible by `b`. -/
def InternalGridGraceful (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) : Prop :=
  ∃ f, GraphLabeling G f ∧ ∀ v, 2 ≤ G.degree v → b ∣ (f v).val

/-- Transport a complete labeling and retain each individual vertex label. -/
theorem labeling_of_representation {k : ℕ} {H : Core k} {c : Demand k}
    (e : Representation G H c) (g : Vertex c → Fin (k+total c+1))
    (hg : Function.Injective g)
    (hcover : ∀ d : Fin (k+total c), ∃ a : Edge c,
      diff (g (ends H c a).1).val (g (ends H c a).2).val=d.val+1) :
    ∃ f, GraphLabeling G f ∧ ∀ v, (f (e v)).val=(g v).val := by
  have hc := representation_edge_count e
  let cr : Fin (k+total c+1) ≃ Fin (Nat.card G.edgeSet+1) := finCongr (by omega)
  let f : V → Fin (Nat.card G.edgeSet+1) := fun v => cr (g (e.symm v))
  have hgb : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hg,(vertex_card c).trans (Fintype.card_fin _).symm⟩
  refine ⟨f,⟨cr.bijective.comp (hgb.comp e.toEquiv.symm.bijective),?_⟩,?_⟩
  · intro d
    let d' : Fin (k+total c) := ⟨d.val,by have := d.isLt; omega⟩
    obtain ⟨a,ha⟩ := hcover d'
    refine ⟨e (ends H c a).1,e (ends H c a).2,?_,?_⟩
    · exact e.map_rel_iff.mpr ⟨a,Or.inl ⟨rfl,rfl⟩⟩
    · simpa [f,cr] using ha
  · intro v
    simp only [f, RelIso.symm_apply_apply]
    rfl

theorem graphGraceful_of_representation {k : ℕ} {H : Core k} {c : Demand k}
    (e : Representation G H c) (hg : Graceful H c) : GraphGraceful G := by
  obtain ⟨g,hg,hcover⟩ := hg
  obtain ⟨f,hf,-⟩ := labeling_of_representation e g hg hcover
  exact ⟨f,hf⟩

theorem internalGrid_of_representation [DecidableRel G.Adj]
    {k b : ℕ} {H : Core k} {c : Demand k}
    (e : Representation G H c) (hleaf : ∀ l, G.degree (e (.inr l)) = 1)
    (hg : PolynomialRootAssembly.GridGraceful H c b) : InternalGridGraceful G b := by
  obtain ⟨g,hginj,hcover,hgrid⟩ := hg.labeling
  obtain ⟨f,hf,hlabels⟩ := labeling_of_representation e g hginj hcover
  refine ⟨f,hf,?_⟩
  intro v hv
  obtain ⟨w,hw⟩ := e.toEquiv.surjective v
  change e w = v at hw
  subst v
  cases w with
  | inl i => rw [hlabels]; exact hgrid i
  | inr l => have := hleaf l; omega

 theorem graceful_of_graph_representation {k : ℕ} {H : Core k} {c : Demand k}
    (e : Representation G H c) (hG : GraphGraceful G) : Graceful H c := by
  obtain ⟨f,hf,hcover⟩ := hG
  have hc := representation_edge_count e
  let cr : Fin (Nat.card G.edgeSet+1) ≃ Fin (k+total c+1) := finCongr (by omega)
  let g : Vertex c → Fin (k+total c+1) := fun v => cr (f (e v))
  refine ⟨g,fun a b hab => e.injective (hf.1 (cr.injective hab)),?_⟩
  intro d
  let d' : Fin (Nat.card G.edgeSet) := ⟨d.val,by have := d.isLt; omega⟩
  obtain ⟨a,b,hab,hd⟩ := hcover d'
  have hp : (extensionGraph H c).Adj (e.symm a) (e.symm b) :=
    e.symm.map_rel_iff.mpr hab
  have hd' : diff (g (e.symm a)).val (g (e.symm b)).val = d.val+1 := by
    simpa [g,cr] using hd
  obtain ⟨z,(⟨ha,hb⟩ | ⟨hb,ha⟩)⟩ := hp
  · rw [ha,hb] at hd'
    exact ⟨z,hd'⟩
  · rw [ha,hb] at hd'
    refine ⟨z,?_⟩
    rw [diff_comm]
    exact hd'

 theorem graphGraceful_iff_representation {k : ℕ} {H : Core k} {c : Demand k}
    (e : Representation G H c) : GraphGraceful G ↔ Graceful H c :=
  ⟨graceful_of_graph_representation e,graphGraceful_of_representation e⟩

/-- The zero-demand leaf extension is exactly the original core graph. -/
def zeroIso {k : ℕ} (H : Core k) :
    extensionGraph H (fun _ => 0) ≃g CoreDiameter.graph H where
  toFun := Sum.elim id (fun l => Fin.elim0 l.2)
  invFun := Sum.inl
  left_inv := by
    intro v
    cases v with
    | inl i => rfl
    | inr l => exact Fin.elim0 l.2
  right_inv := fun _ => rfl
  map_rel_iff' := by
    intro a b
    cases a with
    | inr l => exact Fin.elim0 l.2
    | inl i =>
      cases b with
      | inr l => exact Fin.elim0 l.2
      | inl j => exact (extensionGraph_old_old H _ i j).symm

 theorem graphGraceful_core_iff {k : ℕ} (H : Core k) :
    GraphGraceful (CoreDiameter.graph H) ↔ Graceful H (fun _ => 0) :=
  graphGraceful_iff_representation (zeroIso H)

#print axioms labeling_of_representation
#print axioms graphGraceful_of_representation
#print axioms internalGrid_of_representation
end FixedCore.TreeEncoding
