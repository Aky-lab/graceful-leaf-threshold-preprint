import Next.SortedPacking
import Next.SortedPackingBankCredit

namespace FixedCore.SortedPacking
open scoped BigOperators
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Only old ranks strictly between the two banks can obstruct the
rank choices made by shared-interval packing. -/
theorem extension_of_band_capacity_with_bank_credit {d B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (used : Finset ℕ) (covers : ∀ i, 0 < S.rank i → S.rank i < S.rank v → S.rank i ∈ used)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (low : Fin d → Bool)
    (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hb : 2*B + 4*used.card + 4 ≤ c v)
    (capacity : (∑ i, q i) + 2*B + 3*used.card + 2 + c v/2 ≤ (S.rank v-1)/2)
    (deviation : ∀ i, if low i then S.rank (site i) ≤ B
      else ((S.rank v : ℤ)-S.rank (site i)).natAbs ≤ B) :
    ExtendingGraceful H c S.rank := by
  classical
  obtain ⟨B, T, hpB, hfB, hclB, hcT, hfT, hpT, hclT, hdT, hsT, hcB⟩ :=
    two_intervals_with_bank_credit q (fun i => S.rank (site i)) low used
      capacity hbEven hb deviation
  have fresh (L : Finset ℕ) (hp : ∀ z ∈ L, 0 < z ∧ z < S.rank v)
      (hf : Disjoint L used) : ∀ z ∈ L, ∀ i, S.rank i ≠ z := by
    intro z hz i he
    have ⟨hpos, hlt⟩ := hp z hz
    exact Finset.disjoint_left.mp hf hz (he ▸ covers i (he.symm ▸ hpos) (he.symm ▸ hlt))
  apply extending_of_natural_bands S bound v hv site hzero hbank low B T
  · intro z hz
    exact (Nat.le_of_lt (hpB z hz).2).trans (bound v)
  · exact fresh B hpB hfB
  · exact hclB
  · intro i z hz
    exact (Nat.le_of_lt (hpT i z hz).2).trans (bound v)
  · intro i
    exact fresh (T i) (hpT i) (hfT i)
  · exact hclT
  · exact hdT
  · exact hsT
  · intro i
    exact (hcT i).trans (hcard i).symm
  · exact hcB
  · exact hsupport


/-- Only old ranks strictly between the two banks can obstruct the
rank choices made by shared-interval packing. -/
theorem extension_of_band_capacity {d B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (used : Finset ℕ) (covers : ∀ i, 0 < S.rank i → S.rank i < S.rank v → S.rank i ∈ used)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (low : Fin d → Bool)
    (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hb : 2*B + 4*used.card + 4 ≤ c v)
    (capacity : (∑ i, q i) + 3*B + 5*used.card + 4 + c v/2 ≤ (S.rank v-1)/2)
    (deviation : ∀ i, if low i then S.rank (site i) ≤ B
      else ((S.rank v : ℤ)-S.rank (site i)).natAbs ≤ B) :
    ExtendingGraceful H c S.rank := by
  exact extension_of_band_capacity_with_bank_credit S bound v hv used covers site hzero hbank
    q low hcard hsupport hbEven hb (by omega) deviation

/-- Only sites carrying a nonzero residual demand need be near a bank.
This is the version used after steering marked vertices of the modular core. -/
theorem two_supply_extension_of_band_with_bank_credit {B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (used : Finset ℕ) (covers : ∀ i, 0 < S.rank i → S.rank i < S.rank v → S.rank i ∈ used)
    (nonrootEven : ∀ j, j ≠ 0 → Even (c j))
    (near : ∀ j, j ≠ 0 → j ≠ v → c j ≠ 0 →
      S.rank j ≤ B ∨ ((S.rank v : ℤ)-S.rank j).natAbs ≤ B)
    (bank : 2*B + 4*used.card + 4 ≤ c v)
    (rootSlack : k+total c + 4*B + 6*used.card + 5 ≤ S.rank v + k + c 0) :
    ExtendingGraceful H c S.rank := by
  classical
  let Sites := {j : Fin (k+1) // j ≠ 0 ∧ j ≠ v ∧ c j ≠ 0}
  let e := (Fintype.equivFin Sites).symm
  let site : Fin (Fintype.card Sites) ↪ Fin (k+1) :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  have hs (i) : site i ≠ 0 ∧ site i ≠ v ∧ c (site i) ≠ 0 := (e i).property
  let low := fun i => decide (S.rank (site i) ≤ B)
  have hsupport (j) (hj : j ≠ 0) (hjv : j ≠ v) (hnot : j ∉ Set.range site) : c j = 0 := by
    by_contra hne
    apply hnot
    exact ⟨e.symm ⟨j,hj,hjv,hne⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  choose q hq using (fun i => nonrootEven (site i) (hs i).1)
  have hcard (i) : c (site i) = 2*q i := by have := hq i; omega
  refine extension_of_band_capacity_with_bank_credit S bound v hv used covers site (fun i => (hs i).1)
    (fun i => (hs i).2.1) q low hcard hsupport (nonrootEven v hv) bank ?_ ?_
  · have ht := PackingCapacity.total_sites c v hv site (fun i => (hs i).1)
      (fun i => (hs i).2.1) hsupport
    simp_rw [hcard] at ht
    rw [← Finset.mul_sum] at ht
    omega
  · intro i
    have hh := near (site i) (hs i).1 (hs i).2.1 (hs i).2.2
    dsimp [low]
    by_cases hi : S.rank (site i) ≤ B
    · simp [hi]
    · simpa [hi] using hh.resolve_left hi

/-- Only sites carrying a nonzero residual demand need be near a bank.
This is the version used after steering marked vertices of the modular core. -/
theorem two_supply_extension_of_band {B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (used : Finset ℕ) (covers : ∀ i, 0 < S.rank i → S.rank i < S.rank v → S.rank i ∈ used)
    (nonrootEven : ∀ j, j ≠ 0 → Even (c j))
    (near : ∀ j, j ≠ 0 → j ≠ v → c j ≠ 0 →
      S.rank j ≤ B ∨ ((S.rank v : ℤ)-S.rank j).natAbs ≤ B)
    (bank : 2*B + 4*used.card + 4 ≤ c v)
    (rootSlack : k+total c + 6*B + 10*used.card + 9 ≤ S.rank v + k + c 0) :
    ExtendingGraceful H c S.rank := by
  exact two_supply_extension_of_band_with_bank_credit S bound v hv used covers nonrootEven near
    bank (by omega)

end FixedCore.SortedPacking
