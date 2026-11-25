import Next.BatchPacking
import Next.DisjointBands

namespace FixedCore.BankUnion
open scoped BigOperators

def bank {d : ℕ} (low : Fin d → Bool) (installed : Fin d → Finset ℕ)
    (outside : Finset ℕ) : Finset ℕ :=
  outside ∪ ((Finset.univ.filter fun i => low i).biUnion installed)

/-- Aggregating low-site bank installations and the outside mirror pairs
preserves closure, freshness and exact cardinality. High-site transfers stay
outside the bank because their band containers are disjoint. -/
theorem aggregate {d P N b : ℕ}
    (low : Fin d → Bool) (container installed transfer : Fin d → Finset ℕ)
    (outside used : Finset ℕ)
    (hcontainers : ∀ i j, i ≠ j → Disjoint (container i) (container j))
    (hinstalled : ∀ i, installed i ⊆ container i)
    (htransfer : ∀ i, transfer i ⊆ container i)
    (hlow : ∀ i, low i = true → transfer i ⊆ installed i)
    (houtside : ∀ i, Disjoint outside (container i))
    (hboundI : ∀ i, low i = true → ∀ z ∈ installed i, z ≤ N)
    (hboundO : ∀ z ∈ outside, z ≤ N)
    (hfreeI : ∀ i, low i = true → Disjoint (installed i) used)
    (hfreeO : Disjoint outside used)
    (hclosedI : ∀ i, low i = true → ∀ z ∈ installed i,
      z ≤ P ∧ P - z ∈ installed i)
    (hclosedO : ∀ z ∈ outside, z ≤ P ∧ P - z ∈ outside)
    (hsize : outside.card + (∑ i, if low i then (installed i).card else 0) =
      b + ∑ i, if low i then (transfer i).card else 0) :
    let B := bank low installed outside
    (∀ z ∈ B, z ≤ N) ∧ Disjoint B used ∧
    (∀ z ∈ B, z ≤ P ∧ P - z ∈ B) ∧
    (∀ i, if low i then transfer i ⊆ B else Disjoint (transfer i) B) ∧
    B.card = b + ∑ i, if low i then (transfer i).card else 0 := by
  classical
  dsimp only
  let L := Finset.univ.filter (fun i => low i)
  have hL (i : Fin d) : i ∈ L ↔ low i = true := by simp [L]
  have hdisI : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → Disjoint (installed i) (installed j) := by
    intro i _ j _ hij
    exact (hcontainers i j hij).mono (hinstalled i) (hinstalled j)
  have hdisO : Disjoint outside (L.biUnion installed) := by
    apply (Finset.disjoint_biUnion_right _ _ _).mpr
    intro i _
    exact (houtside i).mono_right (hinstalled i)
  have hcard : (bank low installed outside).card =
      outside.card + ∑ i, if low i then (installed i).card else 0 := by
    change (outside ∪ L.biUnion installed).card = _
    rw [Finset.card_union_of_disjoint hdisO, Finset.card_biUnion hdisI]
    simp [L, Finset.sum_filter]
  refine ⟨?_, ?_, ?_, ?_, hcard.trans hsize⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hboundO z hz
    · obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
      exact hboundI i ((hL i).mp hi) z hz
  · apply Finset.disjoint_left.mpr
    intro z hz hu
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.disjoint_left.mp hfreeO hz hu
    · obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.disjoint_left.mp (hfreeI i ((hL i).mp hi)) hz hu
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hh := hclosedO z hz
      exact ⟨hh.1, Finset.mem_union_left _ hh.2⟩
    · obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := hclosedI i ((hL i).mp hi) z hz
      exact ⟨hh.1, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hh.2⟩)⟩
  · intro i
    cases hi : low i
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      apply Finset.disjoint_left.mpr
      intro z hz hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.disjoint_left.mp (houtside i) hb (htransfer i hz)
      · obtain ⟨j, hj, hb⟩ := Finset.mem_biUnion.mp hb
        have hne : i ≠ j := by
          intro he
          subst j
          have := (hL i).mp hj
          simp [hi] at this
        exact Finset.disjoint_left.mp (hcontainers i j hne)
          (htransfer i hz) (hinstalled j hb)
    · simp only [hi, ↓reduceIte]
      intro z hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, (hL i).mpr hi, hlow i hi hz⟩)

#print axioms aggregate
end FixedCore.BankUnion
