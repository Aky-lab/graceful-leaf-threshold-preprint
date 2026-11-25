import Next.RankOwnership
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Batch ownership updates: exact fiber accounting and preservation of the
edge-difference multiset under a pairing of a selected finite set. -/
namespace FixedCore.OwnershipUpdates
open scoped BigOperators
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

def reparent (owner : α → β) (S : Finset α) (q : β) : α → β :=
  fun z => if z ∈ S then q else owner z

/-- Fiber count written as an indicator sum to make conservation explicit. -/
def count (owner : α → β) (i : β) : ℕ :=
  ∑ z, if owner z = i then 1 else 0

omit [DecidableEq α] in
theorem count_eq_card (owner : α → β) (i : β) :
    count owner i = Fintype.card {z : α // owner z = i} := by
  simp [count, Fintype.card_subtype]

private theorem selected_sum (S : Finset α) (p i : β) :
    (∑ z : α, if z ∈ S then (if p = i then 1 else 0) else 0) =
      if p = i then S.card else 0 := by
  by_cases h : p = i <;> simp [h]

/-- Exact accounting, including the degenerate p=q case and arbitrary i. -/
theorem count_reparent (owner : α → β) (S : Finset α) (p q : β)
    (howner : ∀ z ∈ S, owner z = p) (i : β) :
    count (reparent owner S q) i + (if p = i then S.card else 0) =
      count owner i + (if q = i then S.card else 0) := by
  have hpoint (z : α) :
      (if reparent owner S q z = i then 1 else 0) +
          (if z ∈ S then (if p = i then 1 else 0) else 0) =
        (if owner z = i then 1 else 0) +
          (if z ∈ S then (if q = i then 1 else 0) else 0) := by
    by_cases hz : z ∈ S
    · simp [reparent, hz, howner z hz, Nat.add_comm]
    · simp [reparent, hz]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ => hpoint z)
  simpa only [Finset.sum_add_distrib, selected_sum, count] using h

theorem count_reparent_source (owner : α → β) (S : Finset α) (p q : β)
    (howner : ∀ z ∈ S, owner z = p) (hpq : p ≠ q) :
    count (reparent owner S q) p + S.card = count owner p := by
  simpa [hpq, Ne.symm hpq] using count_reparent owner S p q howner p

theorem count_reparent_target (owner : α → β) (S : Finset α) (p q : β)
    (howner : ∀ z ∈ S, owner z = p) (hpq : p ≠ q) :
    count (reparent owner S q) q = count owner q + S.card := by
  simpa [hpq] using count_reparent owner S p q howner q

theorem count_reparent_other (owner : α → β) (S : Finset α) (p q i : β)
    (howner : ∀ z ∈ S, owner z = p) (hpi : p ≠ i) (hqi : q ≠ i) :
    count (reparent owner S q) i = count owner i := by
  simpa [hpi, hqi] using count_reparent owner S p q howner i

/-- Extend a permutation of the selected ranks by the identity elsewhere. -/
def extend (S : Finset α) (τ : Equiv.Perm {z // z ∈ S}) : Equiv.Perm α :=
  τ.subtypeCongr (Equiv.refl _)

omit [Fintype α] in
@[simp] theorem extend_inside (S : Finset α) (τ : Equiv.Perm {z // z ∈ S})
    {z : α} (hz : z ∈ S) : extend S τ z = (τ ⟨z, hz⟩).val := by
  simp [extend, hz]

omit [Fintype α] in
@[simp] theorem extend_outside (S : Finset α) (τ : Equiv.Perm {z // z ∈ S})
    {z : α} (hz : z ∉ S) : extend S τ z = z := by
  simp [extend, hz]

omit [Fintype α] [DecidableEq β] in
/-- A fixed-point-free involution is sufficient but unnecessary: any selected
permutation satisfying the complementary-rank identity gives this equality. -/
theorem reparent_difference (owner : α → β) (S : Finset α) (p q : β)
    (leafRank : α → ℕ) (parentRank : β → ℕ)
    (τ : Equiv.Perm {z // z ∈ S})
    (howner : ∀ z ∈ S, owner z = p)
    (hsum : ∀ z : {z // z ∈ S},
      leafRank z.val + leafRank (τ z).val = parentRank p + parentRank q)
    (z : α) :
    diff (parentRank (reparent owner S q z)) (leafRank z) =
      diff (parentRank (owner (extend S τ z))) (leafRank (extend S τ z)) := by
  by_cases hz : z ∈ S
  · rw [extend_inside S τ hz, howner _ (τ ⟨z, hz⟩).property]
    have hh := hsum ⟨z, hz⟩
    dsimp only at hh
    simp only [reparent, hz, ite_true]
    unfold diff
    omega
  · simp [reparent, hz]

/-- The batch update applies directly to the actual owned-edge multiset. -/
theorem ownedDifferences_reparent {k : ℕ} {c : Demand k} (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : RankOwnership.Missing r → Fin (k+1))
    (S : Finset (RankOwnership.Missing r)) (p q : Fin (k+1))
    (τ : Equiv.Perm {z // z ∈ S})
    (howner : ∀ z ∈ S, owner z = p)
    (hsum : ∀ z : {z // z ∈ S},
      z.val.val.val + (τ z).val.val.val = (r p).val + (r q).val) :
    RankOwnership.ownedDifferences H r (reparent owner S q) =
      RankOwnership.ownedDifferences H r owner := by
  classical
  apply RankOwnership.ownedDifferences_of_permutation H r _ _ (extend S τ)
  exact reparent_difference owner S p q (fun z => z.val.val) (fun i => (r i).val)
    τ howner hsum

/-- In particular, a selected set equipped with a complementary involution
can be moved in one operation. No fixed-point-freeness is needed for soundness;
applications may impose it to ensure an even number of selected ranks. -/
theorem ownedDifferences_reparent_involution {k : ℕ} {c : Demand k} (H : Core k)
    (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : RankOwnership.Missing r → Fin (k+1))
    (S : Finset (RankOwnership.Missing r)) (p q : Fin (k+1))
    (τ : {z // z ∈ S} → {z // z ∈ S}) (hτ : Function.Involutive τ)
    (howner : ∀ z ∈ S, owner z = p)
    (hsum : ∀ z : {z // z ∈ S},
      z.val.val.val + (τ z).val.val.val = (r p).val + (r q).val) :
    RankOwnership.ownedDifferences H r (reparent owner S q) =
      RankOwnership.ownedDifferences H r owner := by
  exact ownedDifferences_reparent H r owner S p q (hτ.toPerm τ) howner hsum

#print axioms count_reparent
#print axioms ownedDifferences_reparent
end FixedCore.OwnershipUpdates
