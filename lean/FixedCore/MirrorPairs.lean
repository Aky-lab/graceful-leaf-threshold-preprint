import FixedCore
import Mathlib.Order.Interval.Finset.Nat

/-!
# Intact complementary pairs

This is the quantitative finite-set counting step used by the manuscript's
leaf-completion arguments. A used rank spoils at most one mirror pair, not
two independently counted slots.
-/
namespace FixedCore.MirrorPairs

def indices (P : ℕ) : Finset ℕ := Finset.Icc 1 ((P - 1) / 2)

def spoiled (P : ℕ) (used : Finset ℕ) : Finset ℕ :=
  (indices P).filter (fun x => x ∈ used ∨ P - x ∈ used)

def available (P : ℕ) (used : Finset ℕ) : Finset ℕ :=
  indices P \ spoiled P used

theorem index_bounds {P x : ℕ} (hx : x ∈ indices P) :
    0 < x ∧ x < P - x ∧ P - x < P := by
  have h := Finset.mem_Icc.mp hx
  omega

theorem available_spec {P x : ℕ} {used : Finset ℕ} :
    x ∈ available P used ↔ x ∈ indices P ∧ x ∉ used ∧ P - x ∉ used := by
  simp [available, spoiled]
  tauto

/-- The pairs indexed by distinct low endpoints are disjoint. -/
theorem pairs_disjoint {P x y : ℕ} (hx : x ∈ indices P)
    (hy : y ∈ indices P) (hne : x ≠ y) :
    Disjoint ({x, P - x} : Finset ℕ) {y, P - y} := by
  have hxb := index_bounds hx
  have hyb := index_bounds hy
  simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  intro a ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- Every spoiled pair can be assigned a distinct used rank in that pair. -/
theorem spoiled_card_le (P : ℕ) (used : Finset ℕ) :
    (spoiled P used).card ≤ used.card := by
  let hit (x : ℕ) := if x ∈ used then x else P - x
  apply Finset.card_le_card_of_injOn hit
  · intro x hx
    have hs := (Finset.mem_filter.mp hx).2
    dsimp [hit]
    split_ifs with h
    · exact h
    · exact hs.resolve_left h
  · intro x hx y hy hxy
    have hxb := index_bounds (Finset.mem_filter.mp hx).1
    have hyb := index_bounds (Finset.mem_filter.mp hy).1
    dsimp [hit] at hxy
    split_ifs at hxy <;> omega

theorem available_card_lower (P : ℕ) (used : Finset ℕ) :
    (P - 1) / 2 - used.card ≤ (available P used).card := by
  have hs : spoiled P used ⊆ indices P := Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_add_card_eq_card hs
  have hbad := spoiled_card_le P used
  have hi : (indices P).card = (P - 1) / 2 := by simp [indices]
  unfold available
  omega

/-- Any number of intact pairs permitted by the capacity bound can be chosen
with exactly that cardinality. -/
theorem exists_pairs (P : ℕ) (used : Finset ℕ) (q : ℕ)
    (capacity : q + used.card ≤ (P - 1) / 2) :
    ∃ chosen : Finset ℕ, chosen ⊆ available P used ∧ chosen.card = q := by
  apply Finset.exists_subset_card_eq
  have h := available_card_lower P used
  omega

/-- Installing an intact mirror pair at rank P exchanges its two labels as
the two edge differences. -/
theorem pair_differences {P x : ℕ} (hx : x ∈ indices P) :
    diff P x = P - x ∧ diff P (P - x) = x := by
  have h := index_bounds hx
  unfold diff
  omega

#print axioms spoiled_card_le
#print axioms exists_pairs

end FixedCore.MirrorPairs
