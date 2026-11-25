import Next.SparseChoiceScale

noncomputable section
namespace FixedCore.Next

/-- One eighth of the integral choice scale, with no truncating division. -/
def sparseTrialScale (s : ℕ) : ℕ := 64*s*(sparseWindow s+1)

theorem sparseTrialScale_rat (s : ℕ) :
    (sparseTrialScale s : ℚ)=(sparseChoiceScale s : ℚ)/8 := by
  unfold sparseTrialScale sparseChoiceScale
  push_cast
  ring

/-- Integral endpoints of the interval from (5/2)D J³ to (21/8)D J³. -/
def sparseTripleTrials (s j : ℕ) : Finset ℤ :=
  Finset.Icc (20*(sparseTrialScale s : ℤ)*(j : ℤ)^3)
    (21*(sparseTrialScale s : ℤ)*(j : ℤ)^3)

@[simp] theorem card_sparseTripleTrials (s j : ℕ) :
    (sparseTripleTrials s j).card = sparseTrialScale s*j^3+1 := by
  rw [sparseTripleTrials, Int.card_Icc]
  have he : 21*(sparseTrialScale s : ℤ)*(j : ℤ)^3+1-
      20*(sparseTrialScale s : ℤ)*(j : ℤ)^3 =
      ((sparseTrialScale s*j^3+1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he]
  exact Int.toNat_natCast _

theorem sparseTripleTrials_bounds {s j : ℕ} {t : ℤ}
    (ht : t ∈ sparseTripleTrials s j) :
    (5/2)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) ∧
    (t : ℚ) ≤ (21/8)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 := by
  simp only [sparseTripleTrials, Finset.mem_Icc] at ht
  have lo : 20*(sparseTrialScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) := by
    exact_mod_cast ht.1
  have hi : (t : ℚ) ≤ 21*(sparseTrialScale s : ℚ)*(j : ℚ)^3 := by
    exact_mod_cast ht.2
  rw [sparseTrialScale_rat] at lo hi
  constructor <;> linarith

/-- The sparse trial bank exceeds the complete triple exclusion
count even in the smallest positive subtree band. -/
theorem sparseTripleTrials_large {s j : ℕ} (hs : 0 < s) (hj : 0 < j) :
    (3*s+3)*(2*sparseWindow s+1) < (sparseTripleTrials s j).card := by
  rw [card_sparseTripleTrials]
  have hj₃ : 1 ≤ j^3 := Nat.one_le_pow 3 j hj
  have hmul : sparseTrialScale s ≤ sparseTrialScale s*j^3 := by nlinarith
  have hs' : 1 ≤ s := hs
  have hj' := Nat.zero_le (sparseWindow s)
  unfold sparseTrialScale at *
  nlinarith [Nat.mul_le_mul_right (sparseWindow s) hs']

/-- Every parameter in the concrete band yields three positive ranks in the
same globally bounded interval as the old ranks. -/
theorem sparseTripleTrials_range {s j : ℕ} {p : ℚ}
    (hs : 0 < s) (hj : 0 < j)
    (hp : (63/8)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 < p)
    (hpu : p ≤ 2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3)
    {t : ℤ} (ht : t ∈ sparseTripleTrials s j) :
    (t : ℚ) ∈ Set.Icc ((sparseChoiceScale s : ℚ)/100)
      (2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3) ∧
    p-(t : ℚ) ∈ Set.Icc ((sparseChoiceScale s : ℚ)/100)
      (2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3) ∧
    p-2*(t : ℚ) ∈ Set.Icc ((sparseChoiceScale s : ℚ)/100)
      (2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3) := by
  have hD : (0 : ℚ) < sparseChoiceScale s := by
    exact_mod_cast sparseChoiceScale_pos hs
  have hj₃ : (1 : ℚ) ≤ (j : ℚ)^3 := by
    exact_mod_cast (Nat.one_le_pow 3 j hj)
  have hDj : (sparseChoiceScale s : ℚ) ≤
      (sparseChoiceScale s : ℚ)*(j : ℚ)^3 := by nlinarith
  obtain ⟨ht₁,ht₂⟩ := sparseTripleTrials_bounds ht
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

/-- Concrete polynomial triple avoidance: the scale and the number of forbidden
exponents are explicit, while the actual parent rank remains arbitrary. -/
theorem exists_sparse_integer_dyadic_triple {S : Set ℚ} (hfin : S.Finite)
    {s j : ℕ} {p : ℚ} (hs : 0 < s) (hj : 0 < j) (hcard : S.ncard ≤ s)
    (hS : S ⊆ Set.Icc ((sparseChoiceScale s : ℚ)/100)
      (2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3))
    (hp : (63/8)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 < p)
    (hpu : p ≤ 2*(sparseChoiceScale s : ℚ)*(s : ℚ)^3) :
    ∃ t : ℤ,
      (5/2)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 ≤ (t : ℚ) ∧
      (t : ℚ) ≤ (21/8)*(sparseChoiceScale s : ℚ)*(j : ℚ)^3 ∧
      (∀ x ∈ S, ¬ Dyadic (t : ℚ) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-(t : ℚ)) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-2*(t : ℚ)) x) ∧
      ¬ Dyadic (t : ℚ) (p-(t : ℚ)) ∧
      ¬ Dyadic (t : ℚ) (p-2*(t : ℚ)) ∧
      ¬ Dyadic (p-(t : ℚ)) (p-2*(t : ℚ)) := by
  have hD : (0 : ℚ) < sparseChoiceScale s := by
    exact_mod_cast sparseChoiceScale_pos hs
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  have hp₀ : 0 < p := lt_trans (by positivity) hp
  obtain ⟨t, ht, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_bounded_integer_dyadic_triple
    (T := sparseTripleTrials s j) (K := s) (J := sparseWindow s) hfin hp₀ hcard
    (by positivity) (sparseChoiceScale_width) hS
    (fun _ ht => sparseTripleTrials_range hs hj hp hpu ht)
    (sparseTripleTrials_large hs hj)
  obtain ⟨htlo,hthi⟩ := sparseTripleTrials_bounds ht
  exact ⟨t, htlo, hthi, h₁, h₂, h₃, h₄, h₅, h₆⟩

#print axioms exists_sparse_integer_dyadic_triple
#print axioms card_sparseTripleTrials

end FixedCore.Next
