import FixedCore.MirrorPairs

/-!
# Transfer-index counting inside a band

The low-site transfer uses indices x and x-h in the same mirror band. Boundary
loss is at most h; spoiled mirror indices and their translates cost at most
twice their cardinality. These are finite-set statements, not an assumption
that the full multi-site packing has already been constructed.
-/
namespace FixedCore.PackingIntervals

def lowCandidates (a n h : ℕ) (spoiled : Finset ℕ) : Finset ℕ :=
  Finset.Icc (a + h) (a + n - 1) \
    (spoiled ∪ spoiled.image (fun x => x + h))

theorem lowCandidates_lower (a n h : ℕ) (spoiled : Finset ℕ) (ha : 0 < a) :
    n - h - 2 * spoiled.card ≤ (lowCandidates a n h spoiled).card := by
  have hi : (Finset.Icc (a + h) (a + n - 1)).card = n - h := by
    rw [Nat.card_Icc]
    omega
  have hu := Finset.card_union_le spoiled (spoiled.image (fun x => x + h))
  have him := Finset.card_image_le (s := spoiled) (f := fun x => x + h)
  have hc := Finset.le_card_sdiff
    (spoiled ∪ spoiled.image (fun x => x + h)) (Finset.Icc (a + h) (a + n - 1))
  unfold lowCandidates
  omega

theorem lowCandidates_spec {a n h x : ℕ} {spoiled : Finset ℕ}
    (ha : 0 < a) (hx : x ∈ lowCandidates a n h spoiled) :
    x ∈ Finset.Icc a (a + n - 1) ∧
    x - h ∈ Finset.Icc a (a + n - 1) ∧
    x ∉ spoiled ∧ x - h ∉ spoiled ∧ h < x := by
  obtain ⟨hi, hs⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨lo, up⟩ := Finset.mem_Icc.mp hi
  have hnx : x ∉ spoiled := fun h => hs (Finset.mem_union_left _ h)
  have hnh : x - h ∉ spoiled := by
    intro hmem
    apply hs
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x - h, hmem, by omega⟩
  exact ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega),
    hnx, hnh, by omega⟩

/-- Exact allocation at a low site, including the boundary and spoiled-pair
losses in the manuscript. -/
theorem choose_low_indices (a n h : ℕ) (spoiled : Finset ℕ) (q : ℕ)
    (ha : 0 < a) (capacity : q + h + 2 * spoiled.card ≤ n) :
    ∃ chosen : Finset ℕ, chosen.card = q ∧
      ∀ x ∈ chosen,
        x ∈ Finset.Icc a (a + n - 1) ∧
        x - h ∈ Finset.Icc a (a + n - 1) ∧
        x ∉ spoiled ∧ x - h ∉ spoiled ∧ h < x := by
  have hc : q ≤ (lowCandidates a n h spoiled).card := by
    have h := lowCandidates_lower a n h spoiled ha
    omega
  obtain ⟨chosen, hs, hcard⟩ := Finset.exists_subset_card_eq hc
  exact ⟨chosen, hcard, fun x hx => lowCandidates_spec ha (hs hx)⟩

/-- Reserving E extra indices suffices when E pays for the boundary loss and
the two spoiled-index losses. -/
theorem choose_low_with_slack (a q E h : ℕ) (spoiled : Finset ℕ)
    (ha : 0 < a) (slack : h + 2 * spoiled.card ≤ E) :
    ∃ chosen : Finset ℕ, chosen ⊆ lowCandidates a (q + E) h spoiled ∧
      chosen.card = q := by
  apply Finset.exists_subset_card_eq
  have hbound := lowCandidates_lower a (q + E) h spoiled ha
  omega

#print axioms choose_low_indices

end FixedCore.PackingIntervals
