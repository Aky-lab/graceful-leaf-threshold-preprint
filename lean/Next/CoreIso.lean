import FixedCore.Semantics
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

namespace FixedCore
variable {k : ℕ}

/-- An undirected core isomorphism, retaining a bijection of actual edges.
The distinguished root is intentionally not required to be preserved. -/
structure CoreIso (H K : Core k) where
  vertex : Equiv.Perm (Fin (k+1))
  edge : Equiv.Perm (Fin k)
  incidence : ∀ i,
    (vertex (H.parent i) = K.parent (edge i) ∧ vertex i.succ = (edge i).succ) ∨
    (vertex (H.parent i) = (edge i).succ ∧ vertex i.succ = K.parent (edge i))

namespace CoreIso
variable {H K L : Core k}

def refl (H : Core k) : CoreIso H H :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => Or.inl ⟨rfl,rfl⟩⟩

def symm (e : CoreIso H K) : CoreIso K H where
  vertex := e.vertex.symm
  edge := e.edge.symm
  incidence i := by
    have h := e.incidence (e.edge.symm i)
    simp only [e.edge.apply_symm_apply] at h
    rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨by simpa using (congrArg e.vertex.symm h₁).symm,
        by simpa using (congrArg e.vertex.symm h₂).symm⟩
    · exact Or.inr ⟨by simpa using (congrArg e.vertex.symm h₂).symm,
        by simpa using (congrArg e.vertex.symm h₁).symm⟩

def trans (e : CoreIso H K) (f : CoreIso K L) : CoreIso H L where
  vertex := e.vertex.trans f.vertex
  edge := e.edge.trans f.edge
  incidence i := by
    have he := e.incidence i
    have hf := f.incidence (e.edge i)
    change (_ ∧ _) ∨ (_ ∧ _)
    dsimp only [Equiv.trans_apply]
    rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
      rw [h₁,h₂] <;> tauto

/-- Demand follows the vertex rather than the chosen topological numbering. -/
def demand (e : CoreIso H K) (c : Demand k) : Demand k := fun i => c (e.vertex.symm i)

@[simp] theorem total_demand (e : CoreIso H K) (c : Demand k) :
    total (e.demand c) = total c := by
  unfold total demand
  exact Equiv.sum_comp e.vertex.symm c

noncomputable def leafEquiv (e : CoreIso H K) (c : Demand k) :
    Leaf c ≃ Leaf (e.demand c) :=
  Equiv.sigmaCongr e.vertex (fun i => Equiv.cast (by simp [demand]))

noncomputable def vertexEquiv (e : CoreIso H K) (c : Demand k) :
    Vertex c ≃ Vertex (e.demand c) := Equiv.sumCongr e.vertex (e.leafEquiv c)

noncomputable def edgeEquiv (e : CoreIso H K) (c : Demand k) :
    Edge c ≃ Edge (e.demand c) := Equiv.sumCongr e.edge (e.leafEquiv c)

@[simp] theorem leafEquiv_parent (e : CoreIso H K) (c : Demand k) (l : Leaf c) :
    (e.leafEquiv c l).1 = e.vertex l.1 := rfl

theorem ends_transport (e : CoreIso H K) (c : Demand k) (a : Edge c) :
    (e.vertexEquiv c (ends H c a).1 = (ends K (e.demand c) (e.edgeEquiv c a)).1 ∧
     e.vertexEquiv c (ends H c a).2 = (ends K (e.demand c) (e.edgeEquiv c a)).2) ∨
    (e.vertexEquiv c (ends H c a).1 = (ends K (e.demand c) (e.edgeEquiv c a)).2 ∧
     e.vertexEquiv c (ends H c a).2 = (ends K (e.demand c) (e.edgeEquiv c a)).1) := by
  cases a with
  | inl i =>
    rcases e.incidence i with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨congrArg Sum.inl h₁, congrArg Sum.inl h₂⟩
    · exact Or.inr ⟨congrArg Sum.inl h₁, congrArg Sum.inl h₂⟩
  | inr l => exact Or.inl ⟨rfl,rfl⟩

/-- Gracefulness depends on the undirected graph, not root or numbering. -/
theorem graceful (e : CoreIso H K) (c : Demand k) :
    Graceful H c → Graceful K (e.demand c) := by
  classical
  rintro ⟨r, hinj, hcover⟩
  let castRank : Fin (k + total c + 1) ≃ Fin (k + total (e.demand c) + 1) :=
    finCongr (by rw [e.total_demand])
  let f := fun v => castRank (r ((e.vertexEquiv c).symm v))
  refine ⟨f, fun _ _ h => (e.vertexEquiv c).symm.injective (hinj _ _ (castRank.injective h)), ?_⟩
  intro d
  let d' : Fin (k + total c) := ⟨d.val, by simpa using d.isLt⟩
  obtain ⟨a, ha⟩ := hcover d'
  refine ⟨e.edgeEquiv c a, ?_⟩
  rcases e.ends_transport c a with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [← h₁, ← h₂]
    simpa [f, castRank] using ha
  · rw [← h₁, ← h₂]
    simpa [f, castRank, diff_comm] using ha

@[simp] theorem demand_symm (e : CoreIso H K) (c : Demand k) :
    e.symm.demand (e.demand c) = c := by
  funext i
  simp [demand, symm]

theorem graceful_iff (e : CoreIso H K) (c : Demand k) :
    Graceful H c ↔ Graceful K (e.demand c) :=
  ⟨e.graceful c, fun h => by simpa using e.symm.graceful (e.demand c) h⟩

/-- Eventual thresholds are invariant under changing root and numbering. -/
theorem works_iff (e : CoreIso H K) (b : ℕ) : Works H b ↔ Works K b := by
  constructor
  · intro h c hc
    have hg := e.graceful (e.symm.demand c)
      (h _ (by simpa using hc))
    have hh : e.demand (e.symm.demand c) = c := by
      funext i
      simp [demand, symm]
    simpa [hh] using hg
  · intro h c hc
    exact (e.graceful_iff c).2 (h _ (by simpa using hc))

#print axioms graceful_iff
#print axioms works_iff
end CoreIso
end FixedCore
