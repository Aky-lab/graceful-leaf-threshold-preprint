import FixedCore.Semantics
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Multiset.FinsetOps

/-! A packing interface in which unused ranks choose their parents.
The finite fibers produce the actual indexed leaves; no particular leaf
indexing or ownership algorithm is assumed. -/
namespace FixedCore.RankOwnership
variable {k : ℕ} {c : Demand k}

abbrev Missing (r : Fin (k+1) ↪ Fin (k + total c + 1)) :=
  {x : Fin (k + total c + 1) // x ∉ Set.range r}

noncomputable def fill (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : Missing r → Fin (k+1))
    (counts : ∀ i, Fintype.card {x : Missing r // owner x = i} = c i) :
    Leaf c ≃ Missing r := by
  classical
  exact (Equiv.sigmaCongrRight fun i => Fintype.equivOfCardEq
    (by simpa using (counts i).symm)).trans (Equiv.sigmaFiberEquiv owner)

theorem fill_owner (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : Missing r → Fin (k+1))
    (counts : ∀ i, Fintype.card {x : Missing r // owner x = i} = c i)
    (l : Leaf c) : owner (fill r owner counts l) = l.1 := by
  classical
  exact (Fintype.equivOfCardEq
    (show Fintype.card (Fin (c l.1)) = Fintype.card {x : Missing r // owner x = l.1}
      by simpa using (counts l.1).symm) l.2).property

noncomputable def ownedDifferences (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1)) (owner : Missing r → Fin (k+1)) :
    Multiset ℕ := by
  classical
  exact Finset.univ.val.map (fun i : Fin k => diff (r (H.parent i)).val (r i.succ).val) +
    Finset.univ.val.map (fun x : Missing r => diff (r (owner x)).val x.val.val)

def palette (n : ℕ) : Multiset ℕ :=
  Finset.univ.val.map (fun i : Fin n => i.val + 1)

/-- A complete packing of missing ranks by parent ownership yields the actual
canonical demanded graph, with leaf multiplicities justified by finite fibers. -/
theorem graceful_of_ownership (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : Missing r → Fin (k+1))
    (counts : ∀ i, Fintype.card {x : Missing r // owner x = i} = c i)
    (consistent : ownedDifferences H r owner = palette (k + total c)) :
    Graceful H c := by
  classical
  let q := fill r owner counts
  let f : Vertex c → Fin (k + total c + 1)
    | .inl i => r i
    | .inr l => (q l).val
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (r.injective h)
      | inr l => exact False.elim ((q l).property ⟨i, h⟩)
    | inr l =>
      cases y with
      | inl i => exact False.elim ((q l).property ⟨i, h.symm⟩)
      | inr m => exact congrArg Sum.inr (q.injective (Subtype.ext h))
  · intro d
    have hm : d.val + 1 ∈ palette (k + total c) :=
      Multiset.mem_map.mpr ⟨d, by simp, rfl⟩
    rw [← consistent] at hm
    simp only [ownedDifferences, Multiset.mem_add, Multiset.mem_map,
      Finset.mem_val, Finset.mem_univ, true_and] at hm
    rcases hm with ⟨i, hi⟩ | ⟨x, hx⟩
    · exact ⟨.inl i, hi⟩
    · let l := q.symm x
      have hq : q l = x := q.apply_symm_apply x
      have ho : owner x = l.1 := by
        rw [← hq]
        exact fill_owner r owner counts l
      refine ⟨.inr l, ?_⟩
      change diff (r l.1).val (q l).val.val = d.val + 1
      rw [hq, ← ho]
      exact hx

/-- Reindexing leaf differences is enough to preserve the global identity.
This keeps the vertex ranks fixed while ownership is allowed to change. -/
theorem ownedDifferences_of_permutation (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner owner' : Missing r → Fin (k+1)) (e : Equiv.Perm (Missing r))
    (h : ∀ x, diff (r (owner' x)).val x.val.val =
      diff (r (owner (e x))).val (e x).val.val) :
    ownedDifferences H r owner' = ownedDifferences H r owner := by
  classical
  unfold ownedDifferences
  congr 1
  have hu : Finset.univ.val.map e = (Finset.univ : Finset (Missing r)).val := by
    exact congrArg Finset.val (Finset.univ_map_equiv_to_embedding e)
  calc
    _ = Finset.univ.val.map (fun x : Missing r =>
        diff (r (owner (e x))).val (e x).val.val) := by
      apply Multiset.map_congr rfl
      intro x _
      exact h x
    _ = (Finset.univ.val.map e).map
        (fun x : Missing r => diff (r (owner x)).val x.val.val) := by
      rw [Multiset.map_map]
      rfl
    _ = _ := by rw [hu]

/-- Move two chosen leaf ranks to a new parent. The pair-sum equality
exchanges their differences and leaves the full edge multiset unchanged.
Fiber cardinalities may change, so a new demand must be supplied separately
when realizing the resulting ownership as a canonical demanded tree. -/
theorem transfer_pair (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : Missing r → Fin (k+1)) (x y : Missing r) (q : Fin (k+1))
    (_hxy : x ≠ y) (hp : owner x = owner y)
    (hsum : x.val.val + y.val.val = (r (owner x)).val + (r q).val) :
    ownedDifferences H r (fun z => if z = x ∨ z = y then q else owner z) =
      ownedDifferences H r owner := by
  classical
  apply ownedDifferences_of_permutation H r _ _ (Equiv.swap x y)
  intro z
  by_cases hx : z = x
  · subst z
    simp only [true_or, ite_true, Equiv.swap_apply_left]
    rw [← hp]
    unfold diff
    omega
  · by_cases hy : z = y
    · subst z
      simp only [or_true, ite_true, Equiv.swap_apply_right]
      unfold diff
      omega
    · simp [hx, hy, Equiv.swap_apply_of_ne_of_ne hx hy]

#print axioms graceful_of_ownership
#print axioms transfer_pair

end FixedCore.RankOwnership
