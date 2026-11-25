import FixedCore.PackingIntervals

namespace FixedCore.LowBands

def pairLabels (P : ℕ) (indices : Finset ℕ) : Finset ℕ :=
  indices ∪ indices.image (fun x => P - x)

theorem pairLabels_card {P : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ MirrorPairs.indices P) : (pairLabels P J).card = 2 * J.card := by
  have hinj : Set.InjOn (fun x => P - x) (J : Set ℕ) := by
    intro x hx y hy h
    have hxb := MirrorPairs.index_bounds (hJ hx)
    have hyb := MirrorPairs.index_bounds (hJ hy)
    change P - x = P - y at h
    omega
  have hdis : Disjoint J (J.image (fun x => P - x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    have hxb := MirrorPairs.index_bounds (hJ hx)
    have hyb := MirrorPairs.index_bounds (hJ hy)
    omega
  rw [pairLabels, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hinj]
  omega

theorem band_in_mirror {a n P : ℕ} (ha : 0 < a)
    (half : 2 * (a + n - 1) < P) :
    Finset.Icc a (a + n - 1) ⊆ MirrorPairs.indices P := by
  intro x hx
  have hb := Finset.mem_Icc.mp hx
  apply Finset.mem_Icc.mpr
  omega

/-- Every transferred rank was installed as part of an intact bank mirror
pair: the two required original indices are x and x-h. -/
theorem transfer_labels_subset {a n h P : ℕ} {spoiled chosen : Finset ℕ}
    (ha : 0 < a) (chosen_ok : chosen ⊆ PackingIntervals.lowCandidates a n h spoiled) :
    pairLabels (P + h) chosen ⊆
      pairLabels P (Finset.Icc a (a + n - 1) \ spoiled) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨hi, _, hgood, _, _⟩ := PackingIntervals.lowCandidates_spec ha (chosen_ok hz)
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hgood⟩)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨_, hi, _, hgood, hlo⟩ := PackingIntervals.lowCandidates_spec ha (chosen_ok hx)
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x - h, Finset.mem_sdiff.mpr ⟨hi, hgood⟩, by omega⟩

theorem chosen_in_mirror {a n h P : ℕ} {spoiled chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + n - 1) < P)
    (chosen_ok : chosen ⊆ PackingIntervals.lowCandidates a n h spoiled) :
    chosen ⊆ MirrorPairs.indices (P + h) := by
  intro x hx
  have hi := (PackingIntervals.lowCandidates_spec ha (chosen_ok hx)).1
  have hb := Finset.mem_Icc.mp hi
  apply Finset.mem_Icc.mpr
  omega

/-- The exact bank remainder after serving a low site is even and at most
2E. This counts whole installed/transfer pairs and retains spoiled indices. -/
theorem bank_remainder {a q E h P : ℕ} {spoiled chosen : Finset ℕ}
    (ha : 0 < a) (half : 2 * (a + (q + E) - 1) < P)
    (chosen_ok : chosen ⊆ PackingIntervals.lowCandidates a (q + E) h spoiled)
    (chosen_card : chosen.card = q) :
    let installed := pairLabels P (Finset.Icc a (a + (q + E) - 1) \ spoiled)
    let transferred := pairLabels (P + h) chosen
    transferred.card = 2 * q ∧
      Even ((installed \ transferred).card) ∧
      (installed \ transferred).card ≤ 2 * E := by
  dsimp
  have hs := transfer_labels_subset (P := P) ha chosen_ok
  have hband := band_in_mirror ha half
  have hcardI := pairLabels_card
    (J := Finset.Icc a (a + (q + E) - 1) \ spoiled) (Finset.sdiff_subset.trans hband)
  have hcardT := pairLabels_card (chosen_in_mirror ha half chosen_ok)
  rw [chosen_card] at hcardT
  have hremain := Finset.card_sdiff_of_subset hs
  have hsize := Finset.card_le_card (Finset.sdiff_subset
    (s := Finset.Icc a (a + (q + E) - 1)) (t := spoiled))
  have hbandcard : (Finset.Icc a (a + (q + E) - 1)).card = q + E := by
    rw [Nat.card_Icc]
    omega
  refine ⟨hcardT, ?_, ?_⟩
  · refine ⟨(Finset.Icc a (a + (q + E) - 1) \ spoiled).card - q, ?_⟩
    omega
  · omega

end FixedCore.LowBands
