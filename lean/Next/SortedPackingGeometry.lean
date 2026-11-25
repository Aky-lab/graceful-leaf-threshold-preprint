import Next.SortedPackingSelection

namespace FixedCore.SortedPacking
open scoped BigOperators

/-- A shared interval supplies a whole finite family. The forbidden set is
charged twice in total, never twice per site. -/
theorem choose_endpoints {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (P a U V n : ℕ) (F : Finset ℕ)
    (ha : 0 < a) (cap : Fintype.card ι + U + V + 2 * F.card ≤ n)
    (upper : ∀ i, h i ≤ P + U) (lower : ∀ i, P ≤ h i + V) :
    ∃ x y : ι → ℕ, Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ Finset.Icc a (a+n-1) ∧ y i ∈ Finset.Icc a (a+n-1)) ∧
      (∀ i, x i ∉ F ∧ y i ∉ F) ∧
      (∀ i, (x i : ℤ) + P - y i = h i) := by
  classical
  let A := HighBandNat.usedInt F
  have hAc : A.card = F.card := HighBandNat.usedInt_card F
  obtain ⟨x, hx, hy, hb, hf⟩ := select ((a : ℤ) + U)
    (fun i => (h i : ℤ) - P) A A
  let y := fun i => x i - ((h i : ℤ) - P)
  have hxy (i : ι) : (a : ℤ) ≤ x i ∧ x i ≤ a+n-1 ∧
      (a : ℤ) ≤ y i ∧ y i ≤ a+n-1 := by
    have hi := hb i
    have hu := upper i
    have hl := lower i
    dsimp [y]
    rw [hAc] at hi
    push_cast at hi ⊢
    omega
  refine ⟨fun i => (x i).toNat, fun i => (y i).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply hx
    have hi := hxy i
    have hj := hxy j
    change (x i).toNat = (x j).toNat at hij
    omega
  · intro i j hij
    apply hy
    have hi := hxy i
    have hj := hxy j
    change (y i).toNat = (y j).toNat at hij
    change y i = y j
    omega
  · intro i
    have hi := hxy i
    simp only [Finset.mem_Icc]
    omega
  · intro i
    have hi := hxy i
    constructor
    · intro hm
      apply (hf i).1
      exact Finset.mem_image.mpr ⟨(x i).toNat, hm, by omega⟩
    · intro hm
      apply (hf i).2
      exact Finset.mem_image.mpr ⟨(y i).toNat, hm, by change _ = y i; omega⟩
  · intro i
    have hi := hxy i
    dsimp [y] at hi ⊢
    omega

/-- All pairs belonging to one site are extracted from the common scan.
The construction allows two sites to use opposite members of a mirror pair,
while proving that their actual transferred rank sets remain disjoint. -/
theorem pair_family {d P a U V n : ℕ} (q h : Fin d → ℕ) (used : Finset ℕ)
    (ha : 0 < a) (half : 2 * (a+n-1) < P)
    (cap : (∑ i, q i) + U + V + 2 * used.card ≤ n)
    (upper : ∀ i, h i ≤ P + U) (lower : ∀ i, P ≤ h i + V) :
    ∃ T : Fin d → Finset ℕ,
      (∀ i, (T i).card = 2 * q i) ∧
      (∀ i, Disjoint (T i) used) ∧
      (∀ i, ∀ z ∈ T i, 0 < z ∧ z < P) ∧
      (∀ i, ∀ z ∈ T i, z ≤ h i ∧ h i - z ∈ T i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      (∀ i, T i ⊆ LowBands.pairLabels P
        (Finset.Icc a (a+n-1) \ MirrorPairs.spoiled P used)) := by
  classical
  let F := MirrorPairs.spoiled P used
  have hF : F.card ≤ used.card := MirrorPairs.spoiled_card_le P used
  have hslots : Fintype.card (Σ i : Fin d, Fin (q i)) = ∑ i, q i := by simp
  obtain ⟨x, y, hx, hy, hbound, hf, hsum⟩ := choose_endpoints
    (ι := Σ i : Fin d, Fin (q i)) (fun p => h p.1) P a U V n F ha
    (by rw [hslots]; omega) (fun i => upper i.1) (fun i => lower i.1)
  let J := fun i => Finset.univ.image (fun j : Fin (q i) => x ⟨i,j⟩)
  let T := fun i => LowBands.pairLabels (h i) (J i)
  have hjcard (i : Fin d) : (J i).card = q i := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro j l he
      exact eq_of_heq (Sigma.mk.inj (hx he)).2
  have hpair (p : Σ i : Fin d, Fin (q i)) :
      h p.1 - x p = P - y p ∧ x p < h p.1 - x p ∧ h p.1 - x p < P := by
    have hb := hbound p
    have hxb := Finset.mem_Icc.mp hb.1
    have hyb := Finset.mem_Icc.mp hb.2
    have hs := hsum p
    omega
  have hjmirror (i : Fin d) : J i ⊆ MirrorPairs.indices (h i) := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    have hb := Finset.mem_Icc.mp (hbound ⟨i,j⟩).1
    have hp := hpair ⟨i,j⟩
    dsimp only at hp
    apply Finset.mem_Icc.mpr
    omega
  have hsub (i : Fin d) : T i ⊆ LowBands.pairLabels P
      (Finset.Icc a (a+n-1) \ F) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨(hbound ⟨i,j⟩).1, (hf ⟨i,j⟩).1⟩)
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨y ⟨i,j⟩, Finset.mem_sdiff.mpr ⟨(hbound ⟨i,j⟩).2, (hf ⟨i,j⟩).2⟩,
        (hpair ⟨i,j⟩).1.symm⟩)
  have hav : Finset.Icc a (a+n-1) \ F ⊆ MirrorPairs.available P used := by
    intro z hz
    exact Finset.mem_sdiff.mpr
      ⟨LowBands.band_in_mirror ha half (Finset.mem_sdiff.mp hz).1,
        (Finset.mem_sdiff.mp hz).2⟩
  have hinside : Finset.Icc a (a+n-1) \ F ⊆ MirrorPairs.indices P :=
    Finset.sdiff_subset.trans (LowBands.band_in_mirror ha half)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, hsub⟩
  · intro i
    rw [LowBands.pairLabels_card (hjmirror i), hjcard]
  · intro i
    exact (BandGeometry.intact_fresh hav).mono_left (hsub i)
  · intro i z hz
    exact BandGeometry.pairLabels_positive hinside (hsub i hz)
  · intro i z hz
    have hh := Packing.pairLabels_complement (hjmirror i) hz
    exact ⟨Nat.le_of_lt hh.1, hh.2⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    rcases Finset.mem_union.mp hzi with hzi | hzi <;>
      rcases Finset.mem_union.mp hzj with hzj | hzj
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hzi
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hzj
      exact hij (congrArg Sigma.fst (hx (hu.trans hv.symm)))
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hzi
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzj
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hw
      have hbu := Finset.mem_Icc.mp (hbound ⟨i,u⟩).1
      have hbv := Finset.mem_Icc.mp (hbound ⟨j,v⟩).2
      have hpv := (hpair ⟨j,v⟩).1
      dsimp only at hpv
      omega
    · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzi
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hw
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hzj
      have hbu := Finset.mem_Icc.mp (hbound ⟨i,u⟩).2
      have hbv := Finset.mem_Icc.mp (hbound ⟨j,v⟩).1
      have hpu := (hpair ⟨i,u⟩).1
      dsimp only at hpu
      omega
    · obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzi
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hw
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hzj
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hv
      have hbu := Finset.mem_Icc.mp (hbound ⟨i,u⟩).2
      have hbt := Finset.mem_Icc.mp (hbound ⟨j,t⟩).2
      have hpu := (hpair ⟨i,u⟩).1
      have hpt := (hpair ⟨j,t⟩).1
      dsimp only at hpu hpt
      have he : y ⟨i,u⟩ = y ⟨j,t⟩ := by omega
      exact hij (congrArg Sigma.fst (hy he))

#print axioms pair_family
end FixedCore.SortedPacking
