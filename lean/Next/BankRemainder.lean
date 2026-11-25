import Mathlib.Tactic

namespace FixedCore.BankRemainder

/-- The number of installed low-bank leaves not subsequently transferred. -/
def remainder {d : ℕ} (low : Fin d → Bool) (installed transferred : Fin d → ℕ) : ℕ :=
  ∑ i, if low i then installed i - transferred i else 0

theorem remainder_even {d : ℕ} (low : Fin d → Bool) (installed transferred : Fin d → ℕ)
    (heven : ∀ i, low i = true → Even (installed i - transferred i)) :
    Even (remainder low installed transferred) := by
  apply Finset.even_sum
  intro i _
  cases hi : low i
  · simp
  · simpa [hi] using heven i hi

theorem remainder_le {d E : ℕ} (low : Fin d → Bool) (installed transferred : Fin d → ℕ)
    (hbound : ∀ i, low i = true → installed i - transferred i ≤ 2 * E) :
    remainder low installed transferred ≤ 2 * d * E := by
  calc
    _ ≤ ∑ _i : Fin d, 2 * E := by
      apply Finset.sum_le_sum
      intro i _
      cases hi : low i
      · simp
      · simpa [hi] using hbound i hi
    _ = _ := by simp; ring

theorem installed_eq {d : ℕ} (low : Fin d → Bool) (installed transferred : Fin d → ℕ)
    (hsub : ∀ i, low i = true → transferred i ≤ installed i) :
    (∑ i, if low i then installed i else 0) =
      (∑ i, if low i then transferred i else 0) + remainder low installed transferred := by
  rw [remainder, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : low i
  · simp
  · simp only [↓reduceIte]
    exact (Nat.add_sub_of_le (hsub i hi)).symm

/-- The outstanding bank demand is an even nonnegative quantity. Filling its
half in whole outside pairs gives exactly the bank-plus-transfer count. -/
theorem outside_count {d E b : ℕ} (low : Fin d → Bool)
    (installed transferred : Fin d → ℕ)
    (hsub : ∀ i, low i = true → transferred i ≤ installed i)
    (heven : ∀ i, low i = true → Even (installed i - transferred i))
    (hbound : ∀ i, low i = true → installed i - transferred i ≤ 2 * E)
    (hbEven : Even b) (hb : 2 * d * E ≤ b) :
    let R := remainder low installed transferred
    let q := (b-R)/2
    Even R ∧ R ≤ b ∧ q ≤ b/2 ∧
      2*q + (∑ i, if low i then installed i else 0) =
        b + (∑ i, if low i then transferred i else 0) := by
  dsimp
  have hR := remainder_even low installed transferred heven
  have hRb := (remainder_le low installed transferred hbound).trans hb
  have hs := installed_eq low installed transferred hsub
  have hq := Nat.div_le_div_right (Nat.sub_le b (remainder low installed transferred)) (c := 2)
  obtain ⟨r, hr⟩ := hR
  obtain ⟨b', hb'⟩ := hbEven
  refine ⟨⟨r, hr⟩, hRb, hq, ?_⟩
  omega

end FixedCore.BankRemainder
