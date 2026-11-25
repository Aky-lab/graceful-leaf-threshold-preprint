import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace FixedCore.Next
open Set

/-- Two ranks belong to the same dyadic orbit. -/
def Dyadic (x y : ℚ) : Prop := ∃ z : ℤ, x = (2 : ℚ) ^ z * y

theorem Dyadic.refl (x : ℚ) : Dyadic x x := ⟨0, by simp⟩
theorem Dyadic.symm {x y : ℚ} (h : Dyadic x y) : Dyadic y x := by
  obtain ⟨z, rfl⟩ := h
  refine ⟨-z, ?_⟩
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp

theorem Dyadic.trans {x y z : ℚ} (hxy : Dyadic x y) (hyz : Dyadic y z) :
    Dyadic x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  exact ⟨a+b, by rw [ha, hb, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring⟩

theorem dyadic_half (p : ℚ) : Dyadic (p / 2) p := by
  refine ⟨-1, ?_⟩
  norm_num
  ring

/-- Active labels are the least assigned labels in their respective dyadic
orbits. Once a vertex is processed, its rank leaves the active set. -/
structure SeedFrontier (assigned active : Set ℚ) : Prop where
  finite : assigned.Finite
  positive : ∀ x ∈ assigned, 0 < x
  subset : active ⊆ assigned
  minimal : ∀ x ∈ active, ∀ y ∈ assigned, Dyadic x y → x ≤ y

/-- The forced half at an active positive vertex is genuinely unused. -/
theorem SeedFrontier.half_fresh {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : p ∈ A) : p / 2 ∉ S := by
  intro h
  have := F.minimal p hp (p/2) h (dyadic_half p).symm
  have := F.positive p (F.subset hp)
  linarith

/-- Processing an odd singleton keeps the frontier invariant, including the
comparison with all the other still-unprocessed labels. -/
theorem SeedFrontier.singleton {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : p ∈ A) :
    SeedFrontier (insert (p/2) S) (insert (p/2) (A \ {p})) := by
  have hpp := F.positive p (F.subset hp)
  refine ⟨F.finite.insert _, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · positivity
    · exact F.positive x hx
  · intro x hx
    rcases hx with rfl | hx
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (F.subset hx.1)
  · intro x hx y hy hdy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact le_rfl
      · have := F.minimal p hp y hy ((dyadic_half p).symm.trans hdy)
        linarith
    · rcases hy with rfl | hy
      · have hxp := F.minimal x hx.1 p (F.subset hp) (hdy.trans (dyadic_half p))
        have hpx := F.minimal p hp x (F.subset hx.1)
          (hdy.trans (dyadic_half p)).symm
        have heq : x = p := le_antisymm hxp hpx
        exact False.elim (hx.2 heq)
      · exact F.minimal x hx.1 y hy hdy

/-- Deactivating processed vertices cannot damage the frontier property. -/
theorem SeedFrontier.restrict {S A B : Set ℚ} (F : SeedFrontier S A)
    (hBA : B ⊆ A) : SeedFrontier S B :=
  ⟨F.finite, F.positive, hBA.trans F.subset,
    fun x hx y hy h => F.minimal x (hBA hx) y hy h⟩

/-- A positive rank in a fresh orbit may be added as a new active vertex. -/
theorem SeedFrontier.adjoin {S A : Set ℚ} (F : SeedFrontier S A)
    {x : ℚ} (hx : 0 < x) (hfresh : ∀ y ∈ S, ¬ Dyadic x y) :
    SeedFrontier (insert x S) (insert x A) := by
  refine ⟨F.finite.insert _, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with rfl | hy
    · exact hx
    · exact F.positive y hy
  · intro y hy
    rcases hy with rfl | hy
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (F.subset hy)
  · intro y hy z hz hdy
    rcases hy with rfl | hy
    · rcases hz with rfl | hz
      · exact le_rfl
      · exact False.elim (hfresh z hz hdy)
    · rcases hz with rfl | hz
      · exact False.elim (hfresh y (F.subset hy) hdy.symm)
      · exact F.minimal y hy z hz hdy

/-- Exact output contract for a finite block of children of a positive
active parent. The children have distinct fresh ranks and locally realize
precisely their own rank multiset. -/
structure ChildBatch (S A : Set ℚ) (p : ℚ) (n : ℕ) where
  labels : List ℚ
  length_eq : labels.length = n
  nodup : labels.Nodup
  fresh : ∀ x ∈ labels, x ∉ S
  positive : ∀ x ∈ labels, 0 < x
  consistent : (labels : Multiset ℚ).map (fun x => |p-x|) = labels
  frontier : SeedFrontier (S ∪ {x | x ∈ labels}) ((A \ {p}) ∪ {x | x ∈ labels})

#print axioms SeedFrontier.singleton
end FixedCore.Next
