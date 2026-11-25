import FixedCore
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets

namespace FixedCore

variable {k : ℕ}

/-- An integer sparse labeling of the core, with the exact permutation between
its edge differences and its positive (nonroot) vertex ranks. -/
structure ConsistentSeed (H : Core k) where
  rank : Fin (k + 1) → ℕ
  root_zero : rank 0 = 0
  injective : Function.Injective rank
  edgePermutation : Equiv.Perm (Fin k)
  edge_difference : ∀ i, diff (rank (H.parent i)) (rank i.succ) =
    rank (edgePermutation i).succ

/-- Demand concentrated entirely at core vertex zero. -/
def rootDemand (k n : ℕ) : Demand k := fun i => if i = 0 then n else 0

@[simp] theorem total_rootDemand (k n : ℕ) : total (rootDemand k n) = n := by
  simp [total, rootDemand]

/-- Filling the unused integer ranks at the root turns a consistent seed into
an actual graceful labeling, provided the desired palette contains the seed. -/
theorem ConsistentSeed.graceful_root_supported {H : Core k} (S : ConsistentSeed H)
    (c : Demand k) (hc : ∀ i, i ≠ 0 → c i = 0)
    (hbound : ∀ i, S.rank i ≤ k + total c) : Graceful H c := by
  classical
  let r : Fin (k + 1) ↪ Fin (k + total c + 1) :=
    ⟨fun i => ⟨S.rank i, by have := hbound i; omega⟩,
      fun i j h => S.injective (congrArg Fin.val h)⟩
  let Missing := {x : Fin (k + total c + 1) // x ∉ Set.range r}
  have hcard : Fintype.card (Leaf c) = Fintype.card Missing := by
    dsimp [Missing]
    rw [Fintype.card_subtype_compl]
    rw [Fintype.card_range r]
    simp only [Leaf, Fintype.card_sigma, Fintype.card_fin]
    unfold total
    omega
  let fill : Leaf c ≃ Missing := Fintype.equivOfCardEq hcard
  let f : Vertex c → Fin (k + total c + 1)
    | .inl i => r i
    | .inr l => (fill l).val
  have hroot (l : Leaf c) : l.1 = 0 := by
    by_contra h
    have := l.2.isLt
    have hz := hc l.1 h
    omega
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (r.injective h)
      | inr l =>
        exact False.elim ((fill l).property ⟨i, h⟩)
    | inr l =>
      cases y with
      | inl i => exact False.elim ((fill l).property ⟨i, h.symm⟩)
      | inr m =>
        exact congrArg Sum.inr (fill.injective (Subtype.ext h))
  · intro d
    let target : Fin (k + total c + 1) := ⟨d.val + 1, by have := d.isLt; omega⟩
    by_cases hused : target ∈ Set.range r
    · obtain ⟨i, hi⟩ := hused
      have hrank : S.rank i = d.val + 1 := congrArg Fin.val hi
      have hne : i ≠ 0 := by
        intro heq
        subst i
        rw [S.root_zero] at hrank
        omega
      have hi0 : 0 < i.val := by
        by_contra hn
        have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        exact hne this
      let j : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      refine ⟨.inl (S.edgePermutation.symm j), ?_⟩
      change diff (S.rank (H.parent (S.edgePermutation.symm j)))
        (S.rank (S.edgePermutation.symm j).succ) = d.val + 1
      rw [S.edge_difference, S.edgePermutation.apply_symm_apply, hj, hrank]
    · let x : Missing := ⟨target, hused⟩
      let l : Leaf c := fill.symm x
      have hfill : (fill l).val = target := by simp [l, x]
      refine ⟨.inr l, ?_⟩
      change diff (S.rank l.1) (fill l).val.val = d.val + 1
      rw [hroot l, S.root_zero, hfill]
      simp [diff, target]

/-- Root-only extensions are graceful as soon as the palette is large enough
for the fixed consistent integer seed. -/
theorem ConsistentSeed.graceful_root {H : Core k} (S : ConsistentSeed H) (n : ℕ)
    (hbound : ∀ i, S.rank i ≤ k + n) : Graceful H (rootDemand k n) := by
  apply S.graceful_root_supported
  · intro i hi
    simp [rootDemand, hi]
  · simpa using hbound

/-- A supplied seed gives an explicit eventual threshold for root-only demand.
This theorem does not assume that every core already has such a seed. -/
theorem ConsistentSeed.eventually_graceful_root {H : Core k} (S : ConsistentSeed H) :
    ∃ b, ∀ n, b ≤ n → Graceful H (rootDemand k n) := by
  classical
  refine ⟨Finset.univ.sup S.rank, ?_⟩
  intro n hn
  apply S.graceful_root
  intro i
  have hi : S.rank i ≤ Finset.univ.sup S.rank :=
    Finset.le_sup (f := S.rank) (Finset.mem_univ i)
  omega

end FixedCore
