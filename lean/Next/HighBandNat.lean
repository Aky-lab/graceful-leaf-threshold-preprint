import Next.HighBands
import Next.LowBands

namespace FixedCore.HighBandNat

def usedInt (used : Finset ℕ) : Finset ℤ := used.image (fun x : ℕ => (x : ℤ))

theorem usedInt_card (used : Finset ℕ) : (usedInt used).card = used.card := by
  apply Finset.card_image_of_injective
  exact Int.ofNat_injective

def candidates (a h P n : ℕ) (used : Finset ℕ) : Finset ℕ :=
  (HighBands.candidates a h P n (usedInt used)).image Int.toNat

theorem candidates_spec {a h P n x : ℕ} {used : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (hx : x ∈ candidates a h P n used) :
    x ∈ Finset.Icc a (a + n - 1) ∧
      x + P - h ∈ Finset.Icc a (a + n - 1) ∧
      x ∉ used ∧ h - x ∉ used ∧ x < h - x ∧ h - x < P := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hn : 0 < n := by
    have hi := (HighBands.candidates_spec hy).1
    have hb := Finset.mem_Icc.mp hi
    omega
  have hint : 2 * ((a : ℤ) + n - 1) < P := by omega
  have hb := HighBands.partner_bounds (by omega : (0 : ℤ) < a) hint hy
  obtain ⟨hi, ht, hu, hv⟩ := HighBands.candidates_spec hy
  have hi' := Finset.mem_Icc.mp hi
  have ht' := Finset.mem_Icc.mp ht
  have hypos : 0 ≤ y := by omega
  have hycast : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hypos
  refine ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega), ?_, ?_, by omega, by omega⟩
  · intro hm
    apply hu
    exact Finset.mem_image.mpr ⟨y.toNat, hm, hycast⟩
  · intro hm
    apply hv
    exact Finset.mem_image.mpr ⟨h - y.toNat, hm, by omega⟩

theorem candidates_card {a h P n : ℕ} (used : Finset ℕ) (ha : 0 < a) :
    (candidates a h P n used).card =
      (HighBands.candidates a h P n (usedInt used)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  have hxi := Finset.mem_Icc.mp (HighBands.candidates_spec hx).1
  have hyi := Finset.mem_Icc.mp (HighBands.candidates_spec hy).1
  change x.toNat = y.toNat at he
  omega

theorem choose_high_indices {a h P n q : ℕ} (used : Finset ℕ)
    (ha : 0 < a)
    (capacity : q + ((P : ℤ) - h).natAbs + 2 * used.card ≤ n) :
    ∃ chosen : Finset ℕ, chosen.card = q ∧ chosen ⊆ candidates a h P n used := by
  have hl := HighBands.candidates_lower (a : ℤ) h P n (usedInt used)
  rw [usedInt_card] at hl
  have hc := candidates_card (h := h) (P := P) (n := n) used ha
  have hq : q ≤ (candidates a h P n used).card := by omega
  obtain ⟨chosen, hs, hc⟩ := Finset.exists_subset_card_eq hq
  exact ⟨chosen, hc, hs⟩

theorem chosen_in_mirror {a h P n : ℕ} {used chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (chosen_ok : chosen ⊆ candidates a h P n used) :
    chosen ⊆ MirrorPairs.indices h := by
  intro x hx
  have hb := candidates_spec ha half (chosen_ok hx)
  have hi := Finset.mem_Icc.mp hb.1
  apply Finset.mem_Icc.mpr
  omega

theorem pairLabels_card {a h P n : ℕ} {used chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (chosen_ok : chosen ⊆ candidates a h P n used) :
    (LowBands.pairLabels h chosen).card = 2 * chosen.card :=
  LowBands.pairLabels_card (chosen_in_mirror ha half chosen_ok)

theorem pairLabels_fresh {a h P n : ℕ} {used chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (chosen_ok : chosen ⊆ candidates a h P n used) :
    Disjoint (LowBands.pairLabels h chosen) used := by
  apply Finset.disjoint_left.mpr
  intro z hz hu
  rcases Finset.mem_union.mp hz with hz | hz
  · exact (candidates_spec ha half (chosen_ok hz)).2.2.1 hu
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (candidates_spec ha half (chosen_ok hx)).2.2.2.1 hu

theorem pairLabels_subset {a h P n : ℕ} {used chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (chosen_ok : chosen ⊆ candidates a h P n used) :
    LowBands.pairLabels h chosen ⊆
      LowBands.pairLabels P (Finset.Icc a (a + n - 1)) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ (candidates_spec ha half (chosen_ok hz)).1
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hb := candidates_spec ha half (chosen_ok hx)
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x + P - h, hb.2.1, by omega⟩

end FixedCore.HighBandNat
