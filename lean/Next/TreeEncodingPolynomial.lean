import Next.TreeEncodingGraceful
import Next.PolynomialTwoBankTransport
import Next.ModularBanksPrepared
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Prod.Lex
import FixedCore.SmallCores

/-! The ordinary part of Theorem 21 on an arbitrary finite mathematical tree,
with leaves indexed by the actual original vertices rather than a supplied Core. -/
namespace FixedCore.TreeEncoding
variable {V : Type*} (G : SimpleGraph V) (c : V → ℕ)

/-- Attach the prescribed number of distinct pendant leaves to each actual
vertex of an arbitrary graph. -/
def leafExtension : SimpleGraph (V ⊕ ((v : V) × Fin (c v))) where
  Adj
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr l => a=l.1
    | .inr l, .inl b => b=l.1
    | .inr _, .inr _ => False
  symm := by
    intro a b h
    cases a <;> cases b
    · exact G.symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a
    · exact G.irrefl
    · exact not_false

variable {G c} {k : ℕ} {H : Core k}

/-- The arbitrary-vertex leaf extension is exactly the encoded leaf extension,
under an explicit dependent leaf-fiber bijection. -/
noncomputable def leafExtensionIso (e : CoreDiameter.graph H ≃g G) (c : V → ℕ) :
    extensionGraph H (fun i => c (e i)) ≃g leafExtension G c where
  toEquiv := Equiv.sumCongr e.toEquiv
    (Equiv.sigmaCongr e.toEquiv (fun i => Equiv.refl (Fin (c (e i)))))
  map_rel_iff' := by
    intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        rw [extensionGraph_old_old]
        exact e.map_rel_iff
      | inr l =>
        rw [extensionGraph_old_leaf]
        change e i=e l.1 ↔ i=l.1
        exact e.injective.eq_iff
    | inr l =>
      cases b with
      | inl i =>
        rw [extensionGraph_leaf_old]
        change e i=e l.1 ↔ i=l.1
        exact e.injective.eq_iff
      | inr m =>
        simp only [extensionGraph_leaf_leaf, iff_false]
        exact not_false

 theorem leafExtension_edge_count [Fintype V] (hG : G.IsTree) (c : V → ℕ) :
    Nat.card (leafExtension G c).edgeSet = Fintype.card V-1+∑ v,c v := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  have hcard := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_fin] at hcard
  have htotal : total (fun i => c (e i))=∑ v,c v := Equiv.sum_comp e.toEquiv c
  have hedges := representation_edge_count (leafExtensionIso e c)
  omega

#print axioms leafExtensionIso
#print axioms leafExtension_edge_count
end FixedCore.TreeEncoding
