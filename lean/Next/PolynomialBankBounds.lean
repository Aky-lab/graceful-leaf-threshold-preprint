import Next.PolynomialBounds

namespace FixedCore.PolynomialBounds

/-- A positive odd modular palette, with exactly the manuscript's slack
interval. This uses no primality assertion about the modulus. -/
theorem exists_odd_palette (N B b : ℕ) (hb : 0<b) (hN : 2*B+12*b≤N) :
    ∃ q : ℕ, Odd q ∧ 0<q ∧
      2*b*q+2*B+10*b≤N ∧ N<2*b*q+2*B+14*b := by
  let D := N-(2*B+12*b)
  let d := D/(4*b)
  let q := 2*d+1
  have hb4 : 0<4*b := by positivity
  have hmod := Nat.mod_add_div D (4*b)
  have hr := Nat.mod_lt D hb4
  have hsum : D+(2*B+12*b)=N := Nat.sub_add_cancel hN
  have heq : N=D%(4*b)+(4*b)*d+(2*B+12*b) := by
    rw [← hsum,show D%(4*b)+(4*b)*d=D from hmod]
  refine ⟨q,⟨d,rfl⟩,by dsimp [q];omega,?_,?_⟩
  · rw [heq]
    dsimp only [q]
    ring_nf at hr ⊢
    omega
  · rw [heq]
    dsimp only [q]
    ring_nf at hr ⊢
    omega


/-- The marked-forest trial interval is uniformly bounded by the site's
cubic factor and the core order. -/
theorem steering_budget {s l k n : ℕ} (hs : s≤3*n) (hl : l≤k+1) :
    16*(l+1)^3*(2000*(s+3)+2) < 100000*(k+2)^3*(n+1) := by
  have hcoef : 2000*(s+3)+2≤6002*(n+1) := by omega
  have hp : (l+1)^3≤(k+2)^3 := Nat.pow_le_pow_left (by omega) 3
  have hpos : 0<(k+2)^3*(n+1) := by positivity
  calc
    _ ≤ 16*(k+2)^3*(6002*(n+1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hcoef
    _ < _ := by nlinarith

/-- All ordinary congruence exclusions fit in the chosen odd modulus when
both banks have the manuscript's second-supply lower bound. -/
theorem modulus_budget {N B b q C W F : ℕ} (hb : 0<b) (hC : 0<C)
    (hB : B=10000000*b*C) (hbanks : 200*B≤N)
    (hgap : N<2*b*q+2*B+14*b) (hW : W≤100000*C) (hF : F≤6000*C) :
    8*W+2*F<q := by
  have hbound : 8*W+2*F≤812000*C := by omega
  have hq : 812000*C<q := by
    by_contra hn
    have hqq : q≤812000*C := by omega
    have hmul := Nat.mul_le_mul_left (2*b) hqq
    rw [hB] at hbanks hgap
    have hbc : b≤b*C := by nlinarith
    nlinarith
  omega

/-- The reserved modular construction's residual banks pay all shared-band
costs with wide margin, independently of the number of secondary sites. -/
theorem packing_bank_budgets {N P B s a c : ℕ} (hB : 1≤B)
    (hs : s≤3*B) (hgap : N-P≤3*B)
    (ha : 97*B≤a) (hc : 97*B≤c) :
    N-P+8*B+10*s+20≤a ∧ 2*B+4*s+4≤c := by omega

#print axioms exists_odd_palette
#print axioms modulus_budget
end FixedCore.PolynomialBounds
