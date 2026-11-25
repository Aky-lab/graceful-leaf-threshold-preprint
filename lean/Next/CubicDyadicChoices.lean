import Next.PolynomialDyadicChoices

noncomputable section
namespace FixedCore.Next

/-- One eighth of the integral choice scale, with no truncating division. -/
def cubicTrialScale (s : ℕ) : ℕ := 1250*s^2

theorem cubicTrialScale_rat (s : ℕ) :
    (cubicTrialScale s : ℚ)=(polynomialChoiceScale s : ℚ)/8 := by
  unfold cubicTrialScale polynomialChoiceScale
  push_cast
  ring

/-- Integral endpoints of the interval from (5/2)D J³ to (21/8)D J³. -/
def cubicTripleTrials (s j : ℕ) : Finset ℤ :=
  Finset.Icc (20*(cubicTrialScale s : ℤ)*(j : ℤ)^3)
    (21*(cubicTrialScale s : ℤ)*(j : ℤ)^3)

@[simp] theorem card_cubicTripleTrials (s j : ℕ) :
    (cubicTripleTrials s j).card = cubicTrialScale s*j^3+1 := by
  rw [cubicTripleTrials, Int.card_Icc]
  have he : 21*(cubicTrialScale s : ℤ)*(j : ℤ)^3+1-
      20*(cubicTrialScale s : ℤ)*(j : ℤ)^3 =
      ((cubicTrialScale s*j^3+1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he]
  exact Int.toNat_natCast _

theorem cubicTripleTrials_bounds {s j : ℕ} {t : ℤ}
    (ht : t ∈ cubicTripleTrials s j) :
    (5/2)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) ∧
    (t : ℚ) ≤ (21/8)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 := by
  simp only [cubicTripleTrials, Finset.mem_Icc] at ht
  have lo : 20*(cubicTrialScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) := by
    exact_mod_cast ht.1
  have hi : (t : ℚ) ≤ 21*(cubicTrialScale s : ℚ)*(j : ℚ)^3 := by
    exact_mod_cast ht.2
  rw [cubicTrialScale_rat] at lo hi
  constructor <;> linarith

/-- The chosen quadratic trial bank exceeds the complete triple exclusion
count even in the smallest positive subtree band. -/
theorem cubicTripleTrials_large {s j : ℕ} (hs : 0 < s) (hj : 0 < j) :
    (3*s+3)*(2*(8*s)+1) < (cubicTripleTrials s j).card := by
  rw [card_cubicTripleTrials]
  have hj₃ : 1 ≤ j^3 := Nat.one_le_pow 3 j hj
  have hmul : cubicTrialScale s ≤ cubicTrialScale s*j^3 := by nlinarith
  unfold cubicTrialScale at *
  nlinarith

/-- Every parameter in the concrete band yields three positive ranks in the
same globally bounded interval as the old ranks. -/
theorem cubicTripleTrials_range {s j : ℕ} {p : ℚ}
    (hs : 0 < s) (hj : 0 < j)
    (hp : (63/8)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 < p)
    (hpu : p ≤ 2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3)
    {t : ℤ} (ht : t ∈ cubicTripleTrials s j) :
    (t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3) ∧
    p-(t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3) ∧
    p-2*(t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3) := by
  have hD : (0 : ℚ) < polynomialChoiceScale s := by
    exact_mod_cast polynomialChoiceScale_pos hs
  have hj₃ : (1 : ℚ) ≤ (j : ℚ)^3 := by
    exact_mod_cast (Nat.one_le_pow 3 j hj)
  have hDj : (polynomialChoiceScale s : ℚ) ≤
      (polynomialChoiceScale s : ℚ)*(j : ℚ)^3 := by nlinarith
  obtain ⟨ht₁,ht₂⟩ := cubicTripleTrials_bounds ht
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

/-- The global polynomial rank interval fits inside exponent window `8*s`. -/
theorem cubicChoiceScale_width {s : ℕ} (hs : 0 < s) :
    2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3 ≤
      (2 : ℚ)^(8*s)*((polynomialChoiceScale s : ℚ)/100) := by
  have hw : 200*(s : ℚ)^3 ≤ (2 : ℚ)^(8*s) := by
    have hpow : s^3 ≤ s^6 := by
      have h1 : 1 ≤ s^3 := Nat.one_le_pow 3 s hs
      calc
        s^3 = s^3 * 1 := by simp
        _ ≤ s^3 * s^3 := Nat.mul_le_mul_left _ h1
        _ = s^6 := by ring
    exact_mod_cast (Nat.mul_le_mul_left 200 hpow).trans (polynomial_dyadic_width s hs)
  have hD : (0 : ℚ) ≤ polynomialChoiceScale s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hw hD]

/-- Concrete polynomial triple avoidance: the scale and the number of forbidden
exponents are explicit, while the actual parent rank remains arbitrary. -/
theorem exists_cubic_integer_dyadic_triple {S : Set ℚ} (hfin : S.Finite)
    {s j : ℕ} {p : ℚ} (hs : 0 < s) (hj : 0 < j) (hcard : S.ncard ≤ s)
    (hS : S ⊆ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3))
    (hp : (63/8)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 < p)
    (hpu : p ≤ 2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^3) :
    ∃ t : ℤ,
      (5/2)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) ∧
      (t : ℚ) ≤ (21/8)*(polynomialChoiceScale s : ℚ)*(j : ℚ)^3 ∧
      (∀ x ∈ S, ¬ Dyadic (t : ℚ) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-(t : ℚ)) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-2*(t : ℚ)) x) ∧
      ¬ Dyadic (t : ℚ) (p-(t : ℚ)) ∧
      ¬ Dyadic (t : ℚ) (p-2*(t : ℚ)) ∧
      ¬ Dyadic (p-(t : ℚ)) (p-2*(t : ℚ)) := by
  have hD : (0 : ℚ) < polynomialChoiceScale s := by
    exact_mod_cast polynomialChoiceScale_pos hs
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  have hp₀ : 0 < p := lt_trans (by positivity) hp
  obtain ⟨t, ht, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_bounded_integer_dyadic_triple
    (T := cubicTripleTrials s j) (K := s) (J := 8*s) hfin hp₀ hcard
    (by positivity) (cubicChoiceScale_width hs) hS
    (fun _ ht => cubicTripleTrials_range hs hj hp hpu ht)
    (cubicTripleTrials_large hs hj)
  obtain ⟨htlo,hthi⟩ := cubicTripleTrials_bounds ht
  exact ⟨t, htlo, hthi, h₁, h₂, h₃, h₄, h₅, h₆⟩

#print axioms exists_cubic_integer_dyadic_triple
#print axioms card_cubicTripleTrials

end FixedCore.Next
