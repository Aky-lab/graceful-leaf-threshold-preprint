import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Convert

namespace FixedCore.HighBands

/-- Indices staying in a band after a signed translation. -/
def overlap (a : ℤ) (n : ℕ) (shift : ℤ) : Finset ℤ :=
  Finset.Icc (max a (a - shift)) (min (a + n - 1) (a + n - 1 - shift))

theorem overlap_spec {a x shift : ℤ} {n : ℕ} :
    x ∈ overlap a n shift ↔
      x ∈ Finset.Icc a (a + n - 1) ∧
      x + shift ∈ Finset.Icc a (a + n - 1) := by
  simp only [overlap, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

theorem overlap_card (a shift : ℤ) (n : ℕ) :
    (overlap a n shift).card = ((n : ℤ) - |shift|).toNat := by
  rw [overlap, Int.card_Icc]
  by_cases hs : 0 ≤ shift
  · rw [max_eq_left (by omega), min_eq_right (by omega), abs_of_nonneg hs]
    congr 1
    omega
  · rw [max_eq_right (by omega), min_eq_left (by omega), abs_of_nonpos (by omega)]
    congr 1
    omega

def candidates (a h P : ℤ) (n : ℕ) (used : Finset ℤ) : Finset ℤ :=
  overlap a n (P - h) \ (used ∪ used.image (fun z => h - z))

theorem candidates_lower (a h P : ℤ) (n : ℕ) (used : Finset ℤ) :
    n - (P - h).natAbs - 2 * used.card ≤ (candidates a h P n used).card := by
  have hc := Finset.le_card_sdiff (used ∪ used.image (fun z => h - z))
    (overlap a n (P - h))
  have hu := Finset.card_union_le used (used.image (fun z => h - z))
  have hi := Finset.card_image_le (s := used) (f := fun z => h - z)
  have ho := overlap_card a (P - h) n
  have ha := Int.natCast_natAbs (P - h)
  unfold candidates
  omega

theorem candidates_spec {a h P x : ℤ} {n : ℕ} {used : Finset ℤ}
    (hx : x ∈ candidates a h P n used) :
    x ∈ Finset.Icc a (a + n - 1) ∧
      x + P - h ∈ Finset.Icc a (a + n - 1) ∧
      x ∉ used ∧ h - x ∉ used := by
  obtain ⟨hover, hbad⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hin, hshift⟩ := overlap_spec.mp hover
  refine ⟨hin, ?_, ?_, ?_⟩
  · convert hshift using 1; omega
  · intro hmem
    exact hbad (Finset.mem_union_left _ hmem)
  · intro hmem
    apply hbad
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h - x, hmem, by omega⟩

/-- At most |P-h| positions are lost by translation and at most two per old
rank. The resulting allocation contains exactly q fresh high-site pairs. -/
theorem choose_high_indices (a h P : ℤ) (n q : ℕ) (used : Finset ℤ)
    (capacity : q + (P - h).natAbs + 2 * used.card ≤ n) :
    ∃ chosen : Finset ℤ, chosen.card = q ∧ chosen ⊆ candidates a h P n used := by
  have hc : q ≤ (candidates a h P n used).card := by
    have hb := candidates_lower a h P n used
    omega
  obtain ⟨chosen, hs, hcard⟩ := Finset.exists_subset_card_eq hc
  exact ⟨chosen, hcard, hs⟩

/-- The partner stays in the reflected band, on the other side of P/2. -/
theorem partner_bounds {a h P x : ℤ} {n : ℕ} {used : Finset ℤ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (hx : x ∈ candidates a h P n used) :
    0 < x ∧ x < h - x ∧ 0 < h - x ∧ h - x < P ∧
      P - (a + n - 1) ≤ h - x ∧ h - x ≤ P - a := by
  obtain ⟨hi, ht, _, _⟩ := candidates_spec hx
  have hi' := Finset.mem_Icc.mp hi
  have ht' := Finset.mem_Icc.mp ht
  omega

/-- Distinct chosen indices yield disjoint pairs, not merely distinct
individual low endpoints. -/
theorem pairs_disjoint {a h P x y : ℤ} {n : ℕ} {used : Finset ℤ}
    (half : 2 * (a + n - 1) < P)
    (hx : x ∈ candidates a h P n used)
    (hy : y ∈ candidates a h P n used) (hne : x ≠ y) :
    Disjoint ({x, h - x} : Finset ℤ) {y, h - y} := by
  obtain ⟨hxi, hxt, _, _⟩ := candidates_spec hx
  obtain ⟨hyi, hyt, _, _⟩ := candidates_spec hy
  have hxi' := Finset.mem_Icc.mp hxi
  have hxt' := Finset.mem_Icc.mp hxt
  have hyi' := Finset.mem_Icc.mp hyi
  have hyt' := Finset.mem_Icc.mp hyt
  simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  intro z hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz' <;> omega

end FixedCore.HighBands
