import Next.BandGeometry
import Next.BankRemainder

namespace FixedCore.GlobalGeometry
open scoped BigOperators
open BandGeometry

/-- Concrete band allocation, before the final outside fill. -/
theorem allocate {d P E : ℕ} (q h : Fin d → ℕ) (low : Fin d → Bool)
    (used : Finset ℕ) (length : ℕ → ℕ) (hP : 0 < P)
    (hlength : ∀ i : Fin d, length i.val = q i + E)
    (capacity : PackingBands.prefixSum length d ≤ (P - 1) / 2)
    (slack : ∀ i, if low i then h i + 2 * used.card ≤ E
      else ((P : ℤ) - h i).natAbs + 2 * used.card ≤ E) :
    ∃ installed transfer : Fin d → Finset ℕ,
      (∀ i, installed i ⊆ LowBands.pairLabels P (PackingBands.band length i.val)) ∧
      (∀ i, transfer i ⊆ LowBands.pairLabels P (PackingBands.band length i.val)) ∧
      (∀ i, (transfer i).card = 2 * q i) ∧
      (∀ i, Disjoint (installed i) used ∧ Disjoint (transfer i) used) ∧
      (∀ i, ∀ z ∈ installed i, 0 < z ∧ z < P) ∧
      (∀ i, ∀ z ∈ transfer i, 0 < z ∧ z < P) ∧
      (∀ i, ∀ z ∈ installed i, z ≤ P ∧ P - z ∈ installed i) ∧
      (∀ i, ∀ z ∈ transfer i,
        z ≤ (if low i then P else 0) + h i ∧
        (if low i then P else 0) + h i - z ∈ transfer i) ∧
      (∀ i, low i = true → transfer i ⊆ installed i ∧
        Even ((installed i \ transfer i).card) ∧
        (installed i \ transfer i).card ≤ 2 * E) := by
  let a := fun i : Fin d => PackingBands.prefixSum length i.val + 1
  have ha (i : Fin d) : 0 < a i := by dsimp [a]; omega
  have hend (i : Fin d) : a i + (q i + E) - 1 =
      PackingBands.prefixSum length (i.val + 1) := by
    rw [PackingBands.prefix_succ, hlength]
    dsimp [a]
    omega
  have heq (i : Fin d) : Finset.Icc (a i) (a i + (q i + E) - 1) =
      PackingBands.band length i.val := by rw [hend]; rfl
  have half (i : Fin d) : 2 * (a i + (q i + E) - 1) < P := by
    rw [hend]
    have hp := PackingBands.prefix_mono length (Nat.succ_le_iff.mpr i.isLt)
    have hc : PackingBands.prefixSum length (i.val + 1) ≤ (P - 1) / 2 := hp.trans capacity
    omega
  choose T ht using fun i => choose_transfer used (low i) (ha i) (half i) (slack i)
  let I := fun i => BandGeometry.installed P (a i) (q i) E used
  have hip (i : Fin d) := installed_properties used (ha i) (half i)
  refine ⟨I, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [heq] using (hip i).1
  · intro i
    simpa only [heq] using (ht i).2.2.1
  · intro i
    exact (ht i).1
  · intro i
    exact ⟨(hip i).2.1, (ht i).2.1⟩
  · intro i
    exact (hip i).2.2.1
  · intro i z hz
    refine ⟨(ht i).2.2.2.1 z hz, ?_⟩
    have hm := (ht i).2.2.1 hz
    have hb := LowBands.band_in_mirror (ha i) (half i)
    exact (pairLabels_positive hb hm).2
  · intro i
    exact (hip i).2.2.2
  · intro i
    exact (ht i).2.2.2.2.1
  · intro i hi
    simpa only [hi, ↓reduceIte] using (ht i).2.2.2.2.2

/-- Complete concrete packing of all low/high bands and outside bank pairs.
Every witness is constructed from the numerical capacity assumptions. -/
theorem exists_packing {d P E b : ℕ} (q h : Fin d → ℕ) (low : Fin d → Bool)
    (used : Finset ℕ) (length : ℕ → ℕ) (hP : 0 < P)
    (hlength : ∀ i : Fin d, length i.val = q i + E)
    (capacity : PackingBands.prefixSum length d + used.card + b / 2 ≤ (P - 1) / 2)
    (hbEven : Even b) (hb : 2 * d * E ≤ b)
    (slack : ∀ i, if low i then h i + 2 * used.card ≤ E
      else ((P : ℤ) - h i).natAbs + 2 * used.card ≤ E) :
    ∃ B : Finset ℕ, ∃ T : Fin d → Finset ℕ,
      (∀ z ∈ B, 0 < z ∧ z < P) ∧ Disjoint B used ∧
      (∀ z ∈ B, z ≤ P ∧ P - z ∈ B) ∧
      (∀ i, (T i).card = 2 * q i) ∧
      (∀ i, Disjoint (T i) used) ∧
      (∀ i, ∀ z ∈ T i, 0 < z ∧ z < P) ∧
      (∀ i, ∀ z ∈ T i,
        z ≤ (if low i then P else 0) + h i ∧
        (if low i then P else 0) + h i - z ∈ T i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      (∀ i, if low i then T i ⊆ B else Disjoint (T i) B) ∧
      B.card = b + ∑ i, if low i then (T i).card else 0 := by
  classical
  have hcap : PackingBands.prefixSum length d ≤ (P - 1) / 2 := by omega
  obtain ⟨I, T, hI, hT, hc, hf, hpI, hpT, hclI, hclT, hl⟩ :=
    allocate q h low used length hP hlength hcap slack
  let container := fun i : Fin d => LowBands.pairLabels P (PackingBands.band length i.val)
  have hcontainers : ∀ i j, i ≠ j → Disjoint (container i) (container j) := by
    intro i j hij
    apply DisjointBands.pairLabels_disjoint
      (PackingBands.band_subset length i.isLt hcap)
      (PackingBands.band_subset length j.isLt hcap)
    exact PackingBands.bands_disjoint length (fun he => hij (Fin.ext he))
  have hsub (i : Fin d) (hi : low i = true) : (T i).card ≤ (I i).card :=
    Finset.card_le_card (hl i hi).1
  have heven (i : Fin d) (hi : low i = true) : Even ((I i).card - (T i).card) := by
    rw [← Finset.card_sdiff_of_subset (hl i hi).1]
    exact (hl i hi).2.1
  have hbound (i : Fin d) (hi : low i = true) : (I i).card - (T i).card ≤ 2 * E := by
    rw [← Finset.card_sdiff_of_subset (hl i hi).1]
    exact (hl i hi).2.2
  let R := BankRemainder.remainder low (fun i => (I i).card) (fun i => (T i).card)
  let qout := (b - R) / 2
  have harith := BankRemainder.outside_count low (fun i => (I i).card)
    (fun i => (T i).card) hsub heven hbound hbEven hb
  have hq : qout ≤ b / 2 := harith.2.2.1
  obtain ⟨J, hJcard, hJ⟩ := DisjointBands.choose_outside used (by omega :
    PackingBands.prefixSum length d + used.card + qout ≤ (P - 1) / 2)
  let O := LowBands.pairLabels P J
  have hJavail : J ⊆ MirrorPairs.available P used := fun x hx =>
    (DisjointBands.outside_available (hJ hx)).1
  have hJind : J ⊆ MirrorPairs.indices P := fun x hx =>
    (MirrorPairs.available_spec.mp (hJavail hx)).1
  have hOfresh : Disjoint O used := intact_fresh hJavail
  have hOpos : ∀ z ∈ O, 0 < z ∧ z < P := fun z hz => pairLabels_positive hJind hz
  have hOclosed : ∀ z ∈ O, z ≤ P ∧ P - z ∈ O := by
    intro z hz
    have hh := Packing.pairLabels_complement hJind hz
    exact ⟨Nat.le_of_lt hh.1, hh.2⟩
  have hOcard : O.card = 2 * qout := by
    rw [LowBands.pairLabels_card hJind, hJcard]
  have hOdis : ∀ i, Disjoint O (container i) := by
    intro i
    apply (DisjointBands.outside_labels_disjoint hcap hJ).mono_right
    apply pairLabels_mono
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hx⟩
  have hagg := BankUnion.aggregate low container I T O used hcontainers hI hT
    (fun i hi => (hl i hi).1) hOdis
    (fun i _ z hz => Nat.le_of_lt (hpI i z hz).2)
    (fun z hz => Nat.le_of_lt (hOpos z hz).2)
    (fun i _ => (hf i).1) hOfresh
    (fun i _ => hclI i) hOclosed (by rw [hOcard]; exact harith.2.2.2)
  let B := BankUnion.bank low I O
  refine ⟨B, T, ?_, hagg.2.1, hagg.2.2.1, hc,
    fun i => (hf i).2, hpT, hclT, ?_, hagg.2.2.2.1, hagg.2.2.2.2⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hOpos z hz
    · obtain ⟨i, _, hz⟩ := Finset.mem_biUnion.mp hz
      exact hpI i z hz
  · intro i j hij
    exact (hcontainers i j hij).mono (hT i) (hT j)

#print axioms exists_packing
end FixedCore.GlobalGeometry
