import Next.CoreDiameter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Fin.Basic

/-! Every finite nonempty mathematical tree admits the earlier-parent encoding.
The equivalence preserves the actual simple graph, not merely vertex counts. -/
namespace FixedCore.TreeEncoding
open CoreDiameter

variable {k : ℕ}

/-- Append one pendant vertex, numbering it last. -/
def snoc (H : Core k) (x : Fin (k+1)) : Core (k+1) where
  parent := Fin.lastCases x.castSucc (fun i => (H.parent i).castSucc)
  earlier := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using x.isLt
    · simpa using H.earlier j

@[simp] theorem snoc_parent_old (H : Core k) (x : Fin (k+1)) (i : Fin k) :
    (snoc H x).parent i.castSucc = (H.parent i).castSucc := by simp [snoc]

@[simp] theorem snoc_parent_last (H : Core k) (x : Fin (k+1)) :
    (snoc H x).parent (Fin.last k) = x.castSucc := by simp [snoc]

@[simp] theorem snoc_adj_old (H : Core k) (x a b : Fin (k+1)) :
    Adj (snoc H x) a.castSucc b.castSucc ↔ Adj H a b := by
  constructor
  · rintro ⟨i,hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa only [snoc_parent_old, ← Fin.castSucc_succ, Fin.castSucc_inj] using
        (fun h => (show Adj H a b from ⟨j,h⟩))
  · rintro ⟨i,hi⟩
    exact ⟨i.castSucc, by simpa only [snoc_parent_old, ← Fin.castSucc_succ, Fin.castSucc_inj] using hi⟩

@[simp] theorem snoc_adj_last (H : Core k) (x a : Fin (k+1)) :
    Adj (snoc H x) a.castSucc (Fin.last (k+1)) ↔ a = x := by
  constructor
  · rintro ⟨i,hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · intro h
      rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have := congrArg Fin.val hb
        have := j.isLt
        simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at *
        omega
      · have := congrArg Fin.val ha
        have := (H.parent j).isLt
        simp only [snoc_parent_old, Fin.val_last, Fin.val_castSucc] at *
        omega
  · rintro rfl
    exact ⟨Fin.last k, Or.inl ⟨by simp, by simp⟩⟩

/-- Restore a deleted leaf to an encoded induced graph. -/
noncomputable def attachLeaf {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (v u : V) (huv : u ≠ v)
    (hv : ∀ w, G.Adj v w ↔ w = u)
    (H : Core k) (e : graph H ≃g G.induce {v}ᶜ) :
    graph (snoc H (e.symm ⟨u,huv⟩)) ≃g G where
  toEquiv := ((finSuccEquiv' (Fin.last (k+1))).trans
    (Equiv.optionCongr e.toEquiv)).trans (Equiv.optionSubtypeNe v)
  map_rel_iff' := by
    intro a b
    refine Fin.lastCases ?_ (fun i => ?_) a <;>
      refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [graph, Adj, snoc]
    · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv'_last_apply_castSucc,
        Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
      change G.Adj v (e j).val ↔ Adj (snoc H (e.symm ⟨u,huv⟩))
        (Fin.last (k+1)) j.castSucc
      rw [show Adj (snoc H (e.symm ⟨u,huv⟩)) (Fin.last (k+1)) j.castSucc ↔
        Adj (snoc H (e.symm ⟨u,huv⟩)) j.castSucc (Fin.last (k+1)) from
        ⟨adj_symm, adj_symm⟩]
      rw [snoc_adj_last, hv]
      exact ⟨fun h => e.injective (by simpa using (Subtype.ext h : e j = ⟨u,huv⟩)),
        fun h => by simp [h]⟩
    · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv'_last_apply_castSucc,
        Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
      change G.Adj (e i).val v ↔ Adj (snoc H (e.symm ⟨u,huv⟩))
        i.castSucc (Fin.last (k+1))
      rw [snoc_adj_last, G.adj_comm, hv]
      exact ⟨fun h => e.injective (by simpa using (Subtype.ext h : e i = ⟨u,huv⟩)),
        fun h => by simp [h]⟩
    · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv'_last_apply_castSucc,
        Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
      change G.Adj (e i).val (e j).val ↔ Adj (snoc H (e.symm ⟨u,huv⟩))
        i.castSucc j.castSucc
      rw [snoc_adj_old]
      exact e.map_rel_iff


/-- Core edge indices biject with the actual unordered graph edges. -/
def edgeMap (H : Core k) (i : Fin k) : (graph H).edgeSet :=
  ⟨s(H.parent i, i.succ), ⟨i, Or.inl ⟨rfl,rfl⟩⟩⟩

theorem edgeMap_bijective (H : Core k) : Function.Bijective (edgeMap H) := by
  constructor
  · intro i j hij
    have he := congrArg Subtype.val hij
    obtain (⟨hp,hc⟩ | ⟨hp,hc⟩) := Sym2.eq_iff.mp he
    · exact Fin.succ_injective _ hc
    · have hi := H.earlier i
      have hj := H.earlier j
      have hp' := congrArg Fin.val hp
      have hc' := congrArg Fin.val hc
      simp only [Fin.val_succ] at *
      omega
  · rintro ⟨s,hs⟩
    induction s using Sym2.inductionOn with
    | _ a b =>
      change Adj H a b at hs
      obtain ⟨i,hi⟩ := hs
      refine ⟨i, Subtype.ext ?_⟩
      rcases hi with ⟨hp,hc⟩ | ⟨hp,hc⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨hp.symm,hc.symm⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨hp.symm,hc.symm⟩)

noncomputable def edgeEquiv (H : Core k) : Fin k ≃ (graph H).edgeSet :=
  Equiv.ofBijective (edgeMap H) (edgeMap_bijective H)

/-- The vertex isomorphism induces an explicit edge bijection preserving endpoints. -/
noncomputable def transportedEdges {V : Type*} {G : SimpleGraph V} (H : Core k)
    (e : graph H ≃g G) : Fin k ≃ G.edgeSet :=
  (edgeEquiv H).trans e.mapEdgeSet

@[simp] theorem transportedEdges_incidence {V : Type*} {G : SimpleGraph V} (H : Core k)
    (e : graph H ≃g G) (i : Fin k) :
    (transportedEdges H e i).val = s(e (H.parent i), e i.succ) := rfl

/-- The numerical core encoding is itself an actual finite tree. -/
theorem graph_isTree (H : Core k) : (graph H).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨graph_connected H, ?_⟩
  have hc := Nat.card_congr (edgeEquiv H)
  simp only [Nat.card_fin] at hc ⊢
  omega

/-- Every tree on exactly `k+1` vertices is isomorphic to an earlier-parent core. -/
theorem exists_core_of_card (n : ℕ) :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n+1 → G.IsTree → ∃ H : Core n, Nonempty (graph H ≃g G) := by
  classical
  induction n with
  | zero =>
    intro V inst G hcard htree
    letI : Subsingleton V := ⟨Fintype.card_le_one_iff.mp (by omega)⟩
    let H : Core 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    refine ⟨H, ⟨?_⟩⟩
    refine { toEquiv := (Fintype.equivFinOfCardEq hcard).symm
             map_rel_iff' := ?_ }
    intro a b
    have hab : a = b := Fin.ext (by have := a.isLt; have := b.isLt; omega)
    subst b
    simp
  | succ n ih =>
    intro V inst G hcard htree
    letI : Nontrivial V := ⟨Fintype.one_lt_card_iff.mp (by omega)⟩
    obtain ⟨v,hv⟩ := htree.exists_vert_degree_one_of_nontrivial
    obtain ⟨u,hu,huuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have hc : Fintype.card ({v}ᶜ : Set V) = n+1 := by
      change Fintype.card {x : V // ¬ x = v} = n+1
      rw [Fintype.card_subtype_compl, hcard]
      simp
    have ht : (G.induce {v}ᶜ).IsTree :=
      ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hv,
        htree.isAcyclic.induce _⟩
    obtain ⟨H,⟨e⟩⟩ := ih (G.induce {v}ᶜ) hc ht
    exact ⟨snoc H (e.symm ⟨u,hu.ne'⟩), ⟨attachLeaf G v u hu.ne'
      (fun w => ⟨huuniq w, fun he => he ▸ hu⟩) H e⟩⟩

/-- The representation theorem needs no supplied numbering or root. -/
theorem exists_core {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    ∃ k, ∃ H : Core k, Nonempty (graph H ≃g G) := by
  letI : Nonempty V := hG.connected.nonempty
  exact ⟨Fintype.card V-1, exists_core_of_card _ G (by have := Fintype.card_pos (α:=V); omega) hG⟩

#print axioms exists_core_of_card
#print axioms exists_core
end FixedCore.TreeEncoding
