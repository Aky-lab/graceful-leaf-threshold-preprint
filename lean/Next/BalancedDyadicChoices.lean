import Next.PolynomialDyadicChoices

noncomputable section
namespace FixedCore.Next

/-- A concrete bank of `B+1` consecutive integer candidates. -/
def balancedSplitTrials (p : ℚ) (B : ℕ) : Finset ℤ :=
  Finset.Icc (⌈2*p/5⌉ + 1) (⌈2*p/5⌉ + 1 + B)

@[simp] theorem card_balancedSplitTrials (p : ℚ) (B : ℕ) :
    (balancedSplitTrials p B).card = B+1 := by
  simp only [balancedSplitTrials, Int.card_Icc]
  omega

/-- The explicit scale threshold puts the whole trial bank strictly between
two fifths and five twelfths of the parent rank. -/
theorem balancedSplitTrials_bounds {p : ℚ} {B : ℕ}
    (hp : ((60*(B+2) : ℕ) : ℚ) ≤ p) {t : ℤ} (ht : t ∈ balancedSplitTrials p B) :
    2*p/5 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 := by
  have hp' : 60*((B : ℚ)+2) ≤ p := by exact_mod_cast hp
  have hb : (0 : ℚ) ≤ B := by positivity
  have hp₀ : 0 < p := by linarith
  have hceil₁ := Int.le_ceil (2*p/5)
  have hceil₂ := Int.ceil_lt_add_one (2*p/5)
  simp only [balancedSplitTrials, Finset.mem_Icc] at ht
  have ht₁ : (⌈2*p/5⌉ : ℚ) + 1 ≤ (t : ℚ) := by exact_mod_cast ht.1
  have ht₂ : (t : ℚ) ≤ (⌈2*p/5⌉ : ℚ) + 1 + B := by exact_mod_cast ht.2
  constructor <;> linarith

/-- A bounded finite set of previously assigned ranks admits an integral fresh
split at an explicit scale. This is the form used by bounded-depth extensions. -/
theorem exists_balanced_integer_dyadic_split {S : Set ℚ} (hfin : S.Finite)
    {K J : ℕ} {l u p : ℚ} (hcard : S.ncard ≤ K)
    (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l) (hS : S ⊆ Set.Icc l u)
    (hpl : l ≤ 2*p/5) (hpu : p ≤ u)
    (hp : ((60*((2*K+1)*(2*J+1)+2) : ℕ) : ℚ) ≤ p) :
    ∃ t : ℤ, 2*p/5 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 ∧
      (∀ s ∈ S, ¬ Dyadic (t : ℚ) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-(t : ℚ)) s) ∧ ¬ Dyadic (t : ℚ) (p-(t : ℚ)) := by
  let B := (2*K+1)*(2*J+1)
  have hsize : hfin.toFinset.card ≤ K := by
    simpa only [← Set.ncard_eq_toFinset_card S hfin] using hcard
  have hp₀ : 0 < p := by linarith
  have hbounds : ∀ {t : ℤ}, t ∈ balancedSplitTrials p B →
      2*p/5 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 :=
    fun ht => balancedSplitTrials_bounds (B := B) hp ht
  obtain ⟨t, ht, h₁, h₂, h₃⟩ := exists_integer_dyadic_split_of_card
    (T := balancedSplitTrials p B) (S := hfin.toFinset) hl hu
    (fun s hs => hS (by simpa using hs))
    (by
      intro t ht
      obtain ⟨ht₁, ht₂⟩ := hbounds ht
      constructor <;> constructor <;> linarith)
    (by
      rw [card_balancedSplitTrials]
      dsimp [B]
      nlinarith)
  obtain ⟨ht₁, ht₂⟩ := hbounds ht
  exact ⟨t, ht₁, ht₂, fun s hs => h₁ s (by simpa using hs),
    fun s hs => h₂ s (by simpa using hs), h₃⟩


/-- The same quadratic seed scale suffices for the narrower balanced bank. -/
theorem balanced_pair_threshold (s : ℕ) (hs : 0 < s) :
    ((60*((2*s+1)*(2*(8*s)+1)+2) : ℕ) : ℚ) ≤ polynomialChoiceScale s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast
  unfold polynomialChoiceScale
  push_cast
  nlinarith [sq_nonneg ((s : ℚ)-1)]

#print axioms balancedSplitTrials_bounds
#print axioms exists_balanced_integer_dyadic_split
#print axioms balanced_pair_threshold

end FixedCore.Next
