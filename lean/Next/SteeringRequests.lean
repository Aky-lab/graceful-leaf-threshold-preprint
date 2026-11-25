import Mathlib.Tactic

/-! The request-merging exponent estimate used in modular steering.
This module proves the combinatorial estimate. It does not assume or assert
that a particular graph algorithm has already produced the request tree. -/
namespace FixedCore.SteeringRequests

theorem combine_exponent_bound {x y a b e : ℕ}
    (ha : 2^a ≤ 4*x^3) (hb : 2^b ≤ 4*y^3)
    (he : e ≤ min a b+3) : 2^e ≤ 4*(x+y)^3 := by
  have hp : 2^e ≤ 8*2^(min a b) := by
    calc
      2^e ≤ 2^(min a b+3) := Nat.pow_le_pow_right (by decide) he
      _ = 8*2^(min a b) := by rw [pow_add]; ring
  rcases le_total x y with hxy | hyx
  · have hm : 2^(min a b) ≤ 4*x^3 :=
      (Nat.pow_le_pow_right (by decide) (min_le_left a b)).trans ha
    have hc := Nat.pow_le_pow_left (show 2*x≤x+y by omega) 3
    norm_num [mul_pow] at hc
    nlinarith
  · have hm : 2^(min a b) ≤ 4*y^3 :=
      (Nat.pow_le_pow_right (by decide) (min_le_right a b)).trans hb
    have hc := Nat.pow_le_pow_left (show 2*y≤x+y by omega) 3
    norm_num [mul_pow] at hc
    nlinarith

/-- A proof-relevant record of backwards requests. Leaves are original marks;
`propagate` combines two distinct witness populations, and `merge` pools an
additional existing request by taking the larger exponent. -/
inductive Request where
  | mark (exponent : ℕ) (bound : exponent≤2)
  | propagate (left right : Request) (exponent : ℕ)
  | merge (left right : Request)

def Request.exponent : Request→ℕ
  | .mark e _ => e
  | .propagate _ _ e => e
  | .merge l r => max l.exponent r.exponent

def Request.marks : Request→ℕ
  | .mark _ _ => 1
  | .propagate l r _ => l.marks+r.marks
  | .merge l r => l.marks+r.marks

def Request.Valid : Request→Prop
  | .mark _ _ => True
  | .propagate l r e => l.Valid ∧ r.Valid ∧ e≤min l.exponent r.exponent+3
  | .merge l r => l.Valid ∧ r.Valid

def Request.propagations : Request→ℕ
  | .mark _ _ => 0
  | .propagate l r _ => l.propagations+r.propagations+1
  | .merge l r => l.propagations+r.propagations

theorem Request.marks_pos (r : Request) : 0<r.marks := by
  induction r with
  | mark e he => simp [marks]
  | propagate l r e hl hr => simp only [marks]; omega
  | merge l r hl hr => simp only [marks]; omega

/-- The divisibility modulus is at most cubic in the number of original
marked requests, independent of graph order or dependency-path length. -/
theorem Request.exponent_bound (r : Request) (hr : r.Valid) :
    2^r.exponent ≤ 4*r.marks^3 := by
  induction r with
  | mark e he =>
    simpa [exponent,marks] using Nat.pow_le_pow_right (n:=2) (by decide) he
  | propagate l r e hl hr' =>
    exact combine_exponent_bound (hl hr.1) (hr' hr.2.1) hr.2.2
  | merge l r hl hr' =>
    have h₁ := hl hr.1
    have h₂ := hr' hr.2
    simp only [exponent,marks]
    rcases le_total l.exponent r.exponent with he | he
    · rw [max_eq_right he]
      exact h₂.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.le_add_left _ _) 3))
    · rw [max_eq_left he]
      exact h₁.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.le_add_right _ _) 3))

/-- At most one fewer propagations than original requests can occur. -/
theorem Request.propagations_lt_marks (r : Request) : r.propagations<r.marks := by
  induction r with
  | mark e he => simp [propagations,marks]
  | propagate l r e hl hr => simp only [propagations,marks]; omega
  | merge l r hl hr => simp only [propagations,marks]; omega

#print axioms Request.exponent_bound
#print axioms Request.propagations_lt_marks
end FixedCore.SteeringRequests
