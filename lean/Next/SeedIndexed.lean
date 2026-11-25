import Next.SeedFrontier
import Mathlib.Data.Fintype.EquivFin

namespace FixedCore.Next
open Set

/-- A child batch indexed by the actual finite type of child vertices. -/
structure IndexedChildBatch (ι : Type*) [Fintype ι] (S A : Set ℚ) (p : ℚ) where
  rank : ι → ℚ
  injective : Function.Injective rank
  fresh : ∀ i, rank i ∉ S
  positive : ∀ i, 0 < rank i
  consistent : Finset.univ.val.map (fun i => |p-rank i|) = Finset.univ.val.map rank
  frontier : SeedFrontier (S ∪ range rank) ((A \ {p}) ∪ range rank)

/-- Reindex a list batch by any finite child type of the same size. -/
noncomputable def ChildBatch.index {ι : Type*} [Fintype ι] {S A : Set ℚ} {p : ℚ}
    (B : ChildBatch S A p (Fintype.card ι)) : IndexedChildBatch ι S A p := by
  classical
  let e : ι ≃ Fin B.labels.length := Fintype.equivOfCardEq (by simp [B.length_eq])
  let r : ι → ℚ := fun i => B.labels.get (e i)
  have hm (i : ι) : r i ∈ B.labels := List.get_mem _ _
  have hr : range r = {x | x ∈ B.labels} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hm i
    · intro hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      exact ⟨e.symm j, by simpa [r] using hj⟩
  have hmap : Finset.univ.val.map r = (B.labels : Multiset ℚ) := by
    calc
      _ = (Finset.univ.val.map e).map B.labels.get := by rw [Multiset.map_map]; rfl
      _ = Finset.univ.val.map B.labels.get := by rw [Multiset.map_univ_val_equiv]
      _ = _ := by rw [Fin.univ_val_map, List.ofFn_get]
  refine ⟨r, ?_, fun i => B.fresh _ (hm i), fun i => B.positive _ (hm i), ?_, ?_⟩
  · intro i j h
    exact e.injective (B.nodup.injective_get h)
  · calc
      _ = (Finset.univ.val.map r).map (fun x => |p-x|) := by simp [Multiset.map_map]
      _ = _ := by rw [hmap, B.consistent]
  · simpa [hr] using B.frontier

/-- An indexed child batch also gives a bijective matching of its incident
edges to its child ranks, so global assembly can avoid multiset bookkeeping. -/
theorem IndexedChildBatch.exists_matching {ι : Type*} [Fintype ι]
    {S A : Set ℚ} {p : ℚ} (B : IndexedChildBatch ι S A p) :
    ∃ e : Equiv.Perm ι, ∀ i, |p-B.rank i| = B.rank (e i) := by
  classical
  have hex (i : ι) : ∃ j : ι, |p-B.rank i| = B.rank j := by
    have hm : |p-B.rank i| ∈ Finset.univ.val.map B.rank := by
      rw [← B.consistent]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
    exact ⟨j, hj.symm⟩
  choose f hf using hex
  have hsurj : Function.Surjective f := by
    intro j
    have hm : B.rank j ∈ Finset.univ.val.map (fun i => |p-B.rank i|) := by
      rw [B.consistent]
      exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, B.injective ((hf i).symm.trans hi)⟩
  exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp hsurj), hf⟩

/-- Every finite positive locally consistent child batch lies strictly below
its positive parent. Thus ordinary descent preserves any inherited ceiling. -/
theorem IndexedChildBatch.rank_lt_parent {ι : Type*} [Fintype ι]
    {S A : Set ℚ} {p : ℚ} (B : IndexedChildBatch ι S A p) (hp : 0 < p)
    (i : ι) : B.rank i < p := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ B.rank ⟨i, Finset.mem_univ i⟩
  obtain ⟨e, he⟩ := B.exists_matching
  have hmax (l : ι) : B.rank l ≤ B.rank j := hj l (Finset.mem_univ l)
  have hm : B.rank j < p := by
    by_contra hn
    have hpm : p ≤ B.rank j := le_of_not_gt hn
    have hxpos := B.positive (e.symm j)
    have hxmax := hmax (e.symm j)
    have hlt : |p-B.rank (e.symm j)| < B.rank j := by
      rw [abs_lt]
      constructor <;> linarith
    have heq := he (e.symm j)
    simp only [Equiv.apply_symm_apply] at heq
    linarith
  exact lt_of_le_of_lt (hmax i) hm

#print axioms IndexedChildBatch.rank_lt_parent
#print axioms ChildBatch.index
#print axioms IndexedChildBatch.exists_matching
end FixedCore.Next
