import FixedCore.Semantics
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import FixedCore.RootCompletion
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Tactic

/-! Actual-graph consistency, independent of any interval palette. -/
namespace FixedCore
namespace Consistency
variable {k : ℕ} {c : Demand k}

def root (c : Demand k) : Vertex c := .inl 0

/-- The ranks of all vertices other than the distinguished root, retaining multiplicity. -/
def positiveRanks (rank : Vertex c → ℕ) : Multiset ℕ :=
  ((Finset.univ.erase (root c)).val).map rank

/-- The differences of the actual edges of the demanded tree. -/
def edgeDifferences (H : Core k) (rank : Vertex c → ℕ) : Multiset ℕ :=
  Finset.univ.val.map (fun e : Edge c =>
    diff (rank (ends H c e).1) (rank (ends H c e).2))

/-- An exact multiset identity, without bounds or a prescribed complete palette. -/
def Consistent (H : Core k) (rank : Vertex c → ℕ) : Prop :=
  edgeDifferences H rank = positiveRanks rank

structure Assignment (H : Core k) (c : Demand k) where
  rank : Vertex c → ℕ
  root_zero : rank (root c) = 0
  injective : Function.Injective rank
  consistent : Consistent H rank

@[simp] theorem mem_positiveRanks (rank : Vertex c → ℕ) (n : ℕ) :
    n ∈ positiveRanks rank ↔ ∃ v, v ≠ root c ∧ rank v = n := by
  simp only [positiveRanks, Multiset.mem_map, Finset.mem_val, Finset.mem_erase,
    Finset.mem_univ, and_true]

@[simp] theorem mem_edgeDifferences (H : Core k) (rank : Vertex c → ℕ) (n : ℕ) :
    n ∈ edgeDifferences H rank ↔
      ∃ e : Edge c, diff (rank (ends H c e).1) (rank (ends H c e).2) = n := by
  simp [edgeDifferences, Multiset.mem_map]

/-- The nonroot ranks really are positive for an assignment. -/
theorem Assignment.positive {H : Core k} (A : Assignment H c)
    {v : Vertex c} (hv : v ≠ root c) : 0 < A.rank v := by
  have hn : A.rank v ≠ 0 := by
    intro h
    exact hv (A.injective (h.trans A.root_zero.symm))
  omega

/-- Cardinality closes the global palette only at the final bounded stage. -/
theorem Assignment.graceful {H : Core k} (A : Assignment H c)
    (hbound : ∀ v, A.rank v ≤ k + total c) : Graceful H c := by
  let f : Vertex c → Fin (k + total c + 1) :=
    fun v => ⟨A.rank v, Nat.lt_succ_of_le (hbound v)⟩
  have hf : Function.Injective f := fun _ _ h => A.injective (congrArg Fin.val h)
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [total, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩).2
  refine ⟨f, hf, ?_⟩
  intro d
  obtain ⟨v, hv⟩ := hsurj ⟨d.val + 1, by have := d.isLt; omega⟩
  have hr : A.rank v = d.val + 1 := congrArg Fin.val hv
  have hn : v ≠ root c := by
    intro h
    subst v
    rw [A.root_zero] at hr
    omega
  have hm : d.val + 1 ∈ positiveRanks A.rank :=
    (mem_positiveRanks _ _).2 ⟨v, hn, hr⟩
  rw [← A.consistent] at hm
  obtain ⟨e, he⟩ := (mem_edgeDifferences _ _ _).1 hm
  exact ⟨e, he⟩

theorem diff_mul (a x y : ℕ) : diff (a * x) (a * y) = a * diff x y := by
  simp [diff, Nat.mul_sub_left_distrib, Nat.mul_add]

theorem positiveRanks_scale (a : ℕ) (rank : Vertex c → ℕ) :
    positiveRanks (fun v => a * rank v) = (positiveRanks rank).map (a * ·) := by
  simp [positiveRanks, Multiset.map_map]

theorem edgeDifferences_scale (H : Core k) (a : ℕ) (rank : Vertex c → ℕ) :
    edgeDifferences H (fun v => a * rank v) = (edgeDifferences H rank).map (a * ·) := by
  simp [edgeDifferences, Multiset.map_map, diff_mul]

/-- Scaling needs no bounds, and even scaling by zero preserves the multiset identity. -/
theorem Consistent.scale {H : Core k} {rank : Vertex c → ℕ}
    (h : Consistent H rank) (a : ℕ) : Consistent H (fun v => a * rank v) := by
  unfold Consistent at *
  rw [edgeDifferences_scale, positiveRanks_scale, h]

/-- Positive integer scaling also retains injectivity and the distinguished zero. -/
def Assignment.scale {H : Core k} (A : Assignment H c) (a : ℕ) (ha : 0 < a) :
    Assignment H c where
  rank v := a * A.rank v
  root_zero := by simp [A.root_zero]
  injective := fun _ _ h => A.injective (Nat.eq_of_mul_eq_mul_left ha h)
  consistent := A.consistent.scale a

theorem cast_diff (x y : ℕ) : (diff x y : ℚ) = |(x : ℚ) - (y : ℚ)| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    simp only [diff, Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
    simp [diff, Nat.sub_eq_zero_of_le h, Nat.cast_sub h]

#print axioms Assignment.graceful
#print axioms Assignment.scale

end Consistency
end FixedCore
