import Next.PolynomialRootAssembly

/-! The supply split used in the polynomial theorem. This is a finite
combinatorial dichotomy, with the original support retained in both cases. -/
namespace FixedCore.PolynomialSupplyDichotomy
open PolynomialRootAssembly

/-- Either all but one eligible supply are small, or two distinct eligible
sites both meet the cutoff. No choice of a second largest value is needed. -/
theorem supply_dichotomy {α : Type*} [DecidableEq α]
    (sites : Finset α) (c : α → ℕ) (T : ℕ) (hne : sites.Nonempty) :
    (∃ x∈sites, ∀ j∈sites, j≠x → c j<T) ∨
    (∃ u∈sites, ∃ v∈sites, u≠v ∧ T≤c u ∧ T≤c v) := by
  classical
  by_cases hlarge : ∃ u∈sites, T≤c u
  · obtain ⟨u,hu,hcu⟩ := hlarge
    by_cases hsecond : ∃ v∈sites, v≠u ∧ T≤c v
    · obtain ⟨v,hv,hvu,hcv⟩ := hsecond
      exact Or.inr ⟨u,hu,v,hv,Ne.symm hvu,hcu,hcv⟩
    · refine Or.inl ⟨u,hu,?_⟩
      intro j hj hju
      by_contra hn
      exact hsecond ⟨j,hj,hju,by omega⟩
  · obtain ⟨x,hx⟩ := hne
    refine Or.inl ⟨x,hx,?_⟩
    intro j hj _
    by_contra hn
    exact hlarge ⟨j,hj,by omega⟩

/-- A positive total supply makes any genuine support nonempty. -/
theorem support_nonempty {k : ℕ} (c : Demand k)
    (sites : Finset (Fin (k+1))) (hsupport : ∀ j, j∉sites → c j=0)
    (hpos : 0<total c) : sites.Nonempty := by
  classical
  by_contra hn
  have he : sites=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hc : c=fun _ => 0 := funext (fun j => hsupport j (by simp [he]))
  simp [hc,total] at hpos

/-- The degree-eleven edge threshold exceeds the original core size. -/
theorem threshold_pos_supply {k b n : ℕ} (c : Demand k) (hb : 1≤b)
    (hn : k+1≤n) (hN : PolynomialBounds.threshold b n≤k+total c) :
    0<total c := by
  have hpow : n+1≤(n+1)^11 := Nat.le_self_pow (by omega) (n+1)
  have hcoef : 1≤10^16*b := by nlinarith
  have hh : n+1≤PolynomialBounds.threshold b n := by
    unfold PolynomialBounds.threshold
    calc
      n+1 ≤ (n+1)^11 := hpow
      _ ≤ (10^16*b)*(n+1)^11 := Nat.le_mul_of_pos_left _ hcoef
  omega

/-- The full polynomial target reduces to its two-large-bank branch: the
other alternative already gives an actual grid graceful labeling. -/
theorem grid_or_two_large {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ j, j∉sites → c j=0)
    (hN : PolynomialBounds.threshold b n≤k+total c) :
    GridGraceful H c b ∨
      ∃ u∈sites, ∃ v∈sites, u≠v ∧
        10^9*b*(sites.card+2)^3*(n+1)≤c u ∧
        10^9*b*(sites.card+2)^3*(n+1)≤c v := by
  classical
  have hne := support_nonempty c sites hsupport (threshold_pos_supply c hb hn hN)
  rcases supply_dichotomy sites c (10^9*b*(sites.card+2)^3*(n+1)) hne with h|h
  · obtain ⟨x,hx,hsmall⟩ := h
    have hcount : sites.card≤n := by
      have hh := Finset.card_le_card (Finset.subset_univ sites)
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      omega
    exact Or.inl (one_large_alternative_grid H c sites x hx b n hb (by omega)
      hcount hsupport hN hsmall)
  · exact Or.inr h

#print axioms grid_or_two_large
end FixedCore.PolynomialSupplyDichotomy
