import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Local identities for the sparse-labeling construction

These lemmas formalize the exact multiset identities used by the manuscript's
local gadgets. They do not assert that all gadget labels are globally fresh,
nor that the packing or sparse-preparation lemmas have been proved.
-/
namespace FixedCore.Sparse

/-- An edge is represented by its two rational endpoint ranks. -/
abbrev RankedEdge := ℚ × ℚ

def edgeDifference (e : RankedEdge) : ℚ := |e.1 - e.2|

def differences (es : Multiset RankedEdge) : Multiset ℚ :=
  es.map edgeDifference

/-- Local consistency is equality of multisets, so multiplicities are retained. -/
def Realizes (es : Multiset RankedEdge) (ranks : Multiset ℚ) : Prop :=
  differences es = ranks

theorem realizes_add {es fs : Multiset RankedEdge} {xs ys : Multiset ℚ}
    (h : Realizes es xs) (h' : Realizes fs ys) :
    Realizes (es + fs) (xs + ys) := by
  simpa [Realizes, differences, Multiset.map_add] using congrArg₂ (· + ·) h h'

theorem root_leaf {x : ℚ} (hx : 0 ≤ x) :
    Realizes {(0, x)} {x} := by
  simp [Realizes, differences, edgeDifference, abs_of_nonneg hx]

theorem ordinary_pair {p t : ℚ} (ht : 0 ≤ t) (hp : t ≤ p) :
    Realizes {(p, t), (p, p - t)} {t, p - t} := by
  have h₁ : |p - t| = p - t := abs_of_nonneg (sub_nonneg.mpr hp)
  have h₂ : |p - (p - t)| = t := by simpa using abs_of_nonneg ht
  simp only [Realizes, differences, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    edgeDifference, h₁, h₂]
  exact Multiset.cons_swap _ _ _

theorem singleton {p : ℚ} (hp : 0 ≤ p) :
    Realizes {(p, p / 2)} {p / 2} := by
  have hd : |p - p / 2| = p / 2 := by
    rw [abs_of_nonneg (by linarith)]; ring
  simp [Realizes, differences, edgeDifference, hd]

/-- The three-step path, with endpoint ranks t, p-t, p-2t. -/
theorem three_step {p t : ℚ} (ht : 0 ≤ t) (hp : 2 * t ≤ p) :
    Realizes {(p, t), (t, p - t), (p - t, p - 2 * t)}
      {t, p - t, p - 2 * t} := by
  have h₁ : |p - t| = p - t := abs_of_nonneg (by linarith)
  have h₂ : |t - (p - t)| = p - 2 * t := by
    rw [abs_of_nonpos (by linarith)]; ring
  have h₃ : |p - t - (p - 2 * t)| = t := by
    rw [abs_of_nonneg (by linarith)]; ring
  simp only [Realizes, differences, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    edgeDifference, h₁, h₂, h₃]
  simp only [← Multiset.singleton_add]
  ac_rfl

/-- The four-step path, with endpoint ranks t, 2t, p-t, p-3t. -/
theorem four_step {p t : ℚ} (ht : 0 ≤ t) (hp : 3 * t ≤ p) :
    Realizes {(p, t), (t, 2 * t), (2 * t, p - t), (p - t, p - 3 * t)}
      {t, 2 * t, p - t, p - 3 * t} := by
  have h₁ : |p - t| = p - t := abs_of_nonneg (by linarith)
  have h₂ : |t - 2 * t| = t := by
    rw [abs_of_nonpos (by linarith)]; ring
  have h₃ : |2 * t - (p - t)| = p - 3 * t := by
    rw [abs_of_nonpos (by linarith)]; ring
  have h₄ : |p - t - (p - 3 * t)| = 2 * t := by
    rw [abs_of_nonneg (by linarith)]; ring
  simp only [Realizes, differences, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    edgeDifference, h₁, h₂, h₃, h₄]
  simp only [← Multiset.singleton_add]
  ac_rfl

/-- Pair transfer is valid without any order assumptions on the four ranks. -/
theorem pair_transfer {p h x y : ℚ} (hsum : x + y = p + h) :
    differences {(p, x), (p, y)} = differences {(h, x), (h, y)} := by
  have h₁ : |p - x| = |h - y| := by
    have : p - x = -(h - y) := by linarith
    rw [this, abs_neg]
  have h₂ : |p - y| = |h - x| := by
    have : p - y = -(h - x) := by linarith
    rw [this, abs_neg]
  simp only [differences, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    edgeDifference, h₁, h₂]
  exact Multiset.cons_swap _ _ _

/-- Replacing the two leaf edges preserves consistency in an arbitrary
surrounding edge multiset, not merely in a standalone pair. -/
theorem transfer_preserves_realizes {p h x y : ℚ}
    (hsum : x + y = p + h) (rest : Multiset RankedEdge) (ranks : Multiset ℚ) :
    Realizes (rest + {(p, x), (p, y)}) ranks ↔
      Realizes (rest + {(h, x), (h, y)}) ranks := by
  unfold Realizes
  simp only [differences, Multiset.map_add]
  have hh := pair_transfer hsum
  unfold differences at hh
  rw [hh]

/-- Integer scaling will be a special case of rational scaling. -/
theorem scaled_edge_difference (a : ℚ) (ha : 0 ≤ a) (e : RankedEdge) :
    edgeDifference (a * e.1, a * e.2) = a * edgeDifference e := by
  simp only [edgeDifference]
  rw [← mul_sub, abs_mul, abs_of_nonneg ha]

/-- Adding any finite multiset of nonnegative ranks at the root adds exactly
that multiset of edge differences. Injectivity is a separate freshness check. -/
theorem root_fill (xs : Multiset ℚ) (hx : ∀ x ∈ xs, 0 ≤ x) :
    Realizes (xs.map (fun x => (0, x))) xs := by
  induction xs using Multiset.induction_on with
  | empty => simp [Realizes, differences]
  | @cons x xs ih =>
    have hxx : 0 ≤ x := hx x (by simp)
    have hxs : ∀ y ∈ xs, 0 ≤ y := fun y hy => hx y (by simp [hy])
    have htail := ih hxs
    simpa [Realizes, differences, edgeDifference, abs_of_nonneg hxx] using
      congrArg (Multiset.cons x) htail

/-- Completion at zero: fill precisely the unused ranks of a prescribed
nonnegative palette. This is the finite complement step of the construction. -/
theorem complete_at_root {es : Multiset RankedEdge} {used palette : Multiset ℚ}
    (h : Realizes es used) (hsub : used ≤ palette)
    (hpalette : ∀ x ∈ palette, 0 ≤ x) :
    Realizes (es + (palette - used).map (fun x => (0, x))) palette := by
  have hnew : Realizes ((palette - used).map (fun x => (0, x))) (palette - used) :=
    root_fill _ (fun x hx => hpalette x
      (Multiset.mem_of_le (Multiset.sub_le_self palette used) hx))
  have hfull := realizes_add h hnew
  have heq : used + (palette - used) = palette := by
    rw [Multiset.add_comm]
    exact Multiset.sub_add_cancel hsub
  simpa only [heq] using hfull

/-- If the prescribed palette has no repetitions, completion adds fresh,
distinct ranks and exactly the number of missing vertices. -/
theorem completion_freshness {used palette : Multiset ℚ}
    (hsub : used ≤ palette) (hnodup : palette.Nodup) :
    (palette - used).Nodup ∧
      (∀ x ∈ palette - used, x ∉ used) ∧
      (palette - used).card = palette.card - used.card := by
  refine ⟨Multiset.nodup_of_le (Multiset.sub_le_self _ _) hnodup, ?_,
    Multiset.card_sub hsub⟩
  intro x hx
  exact ((Multiset.mem_sub_of_nodup hnodup).mp hx).2

/-- Scaling preserves the complete local consistency identity. -/
theorem scale_realizes {es : Multiset RankedEdge} {xs : Multiset ℚ}
    (h : Realizes es xs) {a : ℚ} (ha : 0 ≤ a) :
    Realizes (es.map (fun e => (a * e.1, a * e.2)))
      (xs.map (fun x => a * x)) := by
  unfold Realizes differences at *
  rw [Multiset.map_map]
  have hf : (edgeDifference ∘ fun e : RankedEdge => (a * e.1, a * e.2)) =
      (fun x => a * x) ∘ edgeDifference := by
    funext e
    exact scaled_edge_difference a ha e
  rw [hf, ← Multiset.map_map, h]

/-- The prime gadget's incoming edge; primality is unnecessary for this
arithmetic identity and is only needed later for orbit avoidance. -/
theorem prime_incoming {p q : ℚ} (hp : 0 ≤ p) (hq : 1 ≤ q) :
    |p - p / q| = (q - 1) * (p / q) := by
  have hq0 : 0 < q := by linarith
  have hdiv : p / q ≤ p := (div_le_iff₀ hq0).mpr (by nlinarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hdiv)]
  field_simp [ne_of_gt hq0]

/-- Each prime-gadget leaf shifts its integer multiplier down by one. -/
theorem prime_leaf {p q j : ℚ} (hp : 0 ≤ p) (hq : 0 < q) (hj : 1 ≤ j) :
    |p / q - j * (p / q)| = (j - 1) * (p / q) := by
  have hdiv : 0 ≤ p / q := div_nonneg hp (le_of_lt hq)
  rw [abs_of_nonpos (by nlinarith)]
  ring

end FixedCore.Sparse
