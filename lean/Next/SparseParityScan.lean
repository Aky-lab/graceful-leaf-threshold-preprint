import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace FixedCore.SparseParityScan

variable {V : Type*}

/-- Select an actual winner, retaining the earlier vertex on ties. -/
def choose (demand : V → ℕ) (x : V) : Option V → Option V
  | none => some x
  | some y => if demand y ≤ demand x then some x else some y

def largest (demand : V → ℕ) : List V → Option V
  | [] => none
  | x :: xs => choose demand x (largest demand xs)

theorem largest_spec (demand : V → ℕ) (xs : List V) :
    match largest demand xs with
    | none => xs = []
    | some y => y ∈ xs ∧ ∀ x ∈ xs, demand x ≤ demand y := by
  induction xs with
  | nil => simp [largest]
  | cons x xs ih =>
    cases h : largest demand xs with
    | none =>
      rw [h] at ih
      subst xs
      simp [largest,choose]
    | some y =>
      rw [h] at ih
      by_cases hle : demand y ≤ demand x
      · simp only [largest,h,choose,if_pos hle, List.mem_cons]
        exact ⟨Or.inl trivial,fun z hz => hz.elim (fun he => he ▸ le_rfl) (fun ht => (ih.2 z ht).trans hle)⟩
      · simp only [largest,h,choose,if_neg hle, List.mem_cons]
        exact ⟨Or.inr ih.1,fun z hz => hz.elim (fun he => he ▸ (le_of_not_ge hle)) (ih.2 z)⟩

/-- Empty parity returns no root.  The function evaluates demands, not cutoffs. -/
def parityBest (sites : List V) (demand : V → ℕ) (p : Fin 2) : Option V :=
  largest demand (sites.filter (fun x => demand x % 2 == p.val))

theorem parityBest_spec (sites : List V) (demand : V → ℕ) (p : Fin 2) :
    match parityBest sites demand p with
    | none => ∀ x ∈ sites, demand x % 2 ≠ p.val
    | some y => y ∈ sites ∧ demand y % 2 = p.val ∧
        ∀ x ∈ sites, demand x % 2 = p.val → demand x ≤ demand y := by
  have h := largest_spec demand (sites.filter (fun x => demand x % 2 == p.val))
  unfold parityBest
  cases he : largest demand (sites.filter (fun x => demand x % 2 == p.val)) with
  | none =>
    rw [he] at h
    intro x hx hp
    have hm : x ∈ sites.filter (fun y => demand y % 2 == p.val) := by simp [hx,hp]
    simp [h] at hm
  | some y =>
    rw [he] at h
    have hm := List.mem_filter.mp h.1
    refine ⟨hm.1, beq_iff_eq.mp hm.2, ?_⟩
    intro x hx hp
    exact h.2 x (by simp [hx,hp])

/-- Executable gate using at most two cutoff evaluations. The candidate
list may be a numbering of a finite vertex set or only the positive sites. -/
def accepts (sites : List V) (demand cutoff : V → ℕ) (N : ℕ) : Bool :=
  (parityBest sites demand 0).any (fun y => decide (cutoff y ≤ N)) ||
  (parityBest sites demand 1).any (fun y => decide (cutoff y ≤ N))

theorem accepts_iff (sites : List V) (demand cutoff : V → ℕ) (N : ℕ)
    (hmono : ∀ x ∈ sites, ∀ y ∈ sites,
      demand x % 2 = demand y % 2 → demand x ≤ demand y → cutoff y ≤ cutoff x) :
    accepts sites demand cutoff N = true ↔ ∃ x ∈ sites, cutoff x ≤ N := by
  have one : ∀ p : Fin 2, (parityBest sites demand p).any
      (fun y => decide (cutoff y ≤ N)) = true ↔
      ∃ x ∈ sites, demand x % 2 = p.val ∧ cutoff x ≤ N := by
    intro p
    have h := parityBest_spec sites demand p
    cases he : parityBest sites demand p with
    | none =>
      rw [he] at h
      simp only [Option.any_none, Bool.false_eq_true, false_iff]
      rintro ⟨x,hx,hp,_⟩
      exact h x hx hp
    | some y =>
      rw [he] at h
      simp only [Option.any_some, decide_eq_true_eq]
      constructor
      · intro hc
        exact ⟨y,h.1,h.2.1,hc⟩
      · rintro ⟨x,hx,hp,hc⟩
        exact (hmono x hx y h.1 (hp.trans h.2.1.symm) (h.2.2 x hx hp)).trans hc
  rw [accepts,Bool.or_eq_true,one,one]
  constructor
  · rintro (⟨x,hx,_,hc⟩ | ⟨x,hx,_,hc⟩) <;> exact ⟨x,hx,hc⟩
  · rintro ⟨x,hx,hc⟩
    have hp : demand x % 2 = 0 ∨ demand x % 2 = 1 := by omega
    exact hp.elim (fun h => Or.inl ⟨x,hx,h,hc⟩) (fun h => Or.inr ⟨x,hx,h,hc⟩)

#print axioms largest_spec
#print axioms parityBest_spec
#print axioms accepts_iff

end FixedCore.SparseParityScan
