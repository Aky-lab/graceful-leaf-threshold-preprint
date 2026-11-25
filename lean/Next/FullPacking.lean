import Next.GlobalGeometry
import Next.PackingCapacity

namespace FixedCore.FullPacking
open scoped BigOperators
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Full graph-level packing from the numerical band capacity. All natural
rank sets, transfer permutations, and final ownership fibers are constructed. -/
theorem graceful_packing {d E : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (low : Fin d → Bool)
    (length : ℕ → ℕ) (hlength : ∀ i : Fin d, length i.val = q i + E)
    (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hb : 2 * d * E ≤ c v)
    (capacity : PackingBands.prefixSum length d + k + c v / 2 ≤ (S.rank v - 1) / 2)
    (slack : ∀ i, if low i then S.rank (site i) + 2 * k ≤ E
      else ((S.rank v : ℤ) - S.rank (site i)).natAbs + 2 * k ≤ E) :
    Graceful H c := by
  classical
  let used := Finset.univ.image (fun i : Fin k => S.rank i.succ)
  have hused : used.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · exact S.injective.comp (Fin.succ_injective k)
  have hP : 0 < S.rank v := by
    have hn : S.rank v ≠ 0 := fun he => hv (S.injective (he.trans S.root_zero.symm))
    omega
  obtain ⟨B, T, hpB, hfB, hclB, hcT, hfT, hpT, hclT, hdT, hsT, hcB⟩ :=
    GlobalGeometry.exists_packing q (fun i => S.rank (site i)) low used length hP hlength
      (by simpa only [hused] using capacity) hbEven hb
      (by simpa only [hused] using slack)
  have fresh (L : Finset ℕ) (hp : ∀ z ∈ L, 0 < z) (hf : Disjoint L used) :
      ∀ z ∈ L, ∀ i, S.rank i ≠ z := by
    intro z hz i he
    by_cases hi : i = 0
    · subst i
      rw [S.root_zero] at he
      have := hp z hz
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun hh => hi (Fin.ext hh)
        omega
      let j : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by dsimp [j]; omega)
      apply Finset.disjoint_left.mp hf hz
      exact Finset.mem_image.mpr ⟨j, by simp, by rwa [hj]⟩
  apply BatchPacking.graceful_of_natural_bands S bound v hv site hzero hbank low B T
  · intro z hz
    exact (Nat.le_of_lt (hpB z hz).2).trans (bound v)
  · exact fresh B (fun z hz => (hpB z hz).1) hfB
  · exact hclB
  · intro i z hz
    exact (Nat.le_of_lt (hpT i z hz).2).trans (bound v)
  · intro i
    exact fresh (T i) (fun z hz => (hpT i z hz).1) (hfT i)
  · exact hclT
  · exact hdT
  · exact hsT
  · intro i
    exact (hcT i).trans (hcard i).symm
  · exact hcB
  · exact hsupport

/-- The manuscript's root slack pays for the complete band and bank capacity.
The arithmetic identity for the band length is the sole layout bookkeeping
premise; all subsequent geometric and graph witnesses are constructed. -/
theorem graceful_packing_of_root_slack {d E : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (low : Fin d → Bool)
    (length : ℕ → ℕ) (hlength : ∀ i : Fin d, length i.val = q i + E)
    (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hb : 2 * d * E ≤ c v)
    (twiceBands : 2 * PackingBands.prefixSum length d + c 0 + c v =
      total c + 2 * d * E)
    (rootSlack : k + total c - S.rank v + 2 * d * E + 2 * k + 4 ≤ c 0)
    (slack : ∀ i, if low i then S.rank (site i) + 2 * k ≤ E
      else ((S.rank v : ℤ) - S.rank (site i)).natAbs + 2 * k ≤ E) :
    Graceful H c := by
  apply graceful_packing S bound v hv site hzero hbank q low length hlength hcard
    hsupport hbEven hb ?_ slack
  have hP := bound v
  omega

/-- Manuscript Lemma 2, on the actual demanded graph. The hypotheses on E
are the pointwise form of E ≥ 4k+4 plus the maximum low/high deviation.
There are no assumed bands, permutations, ownership maps or count identities. -/
theorem lemma_two {d E : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (low : Fin d → Bool)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hsiteEven : ∀ i, Even (c (site i)))
    (_hE : 4 * k + 4 ≤ E)
    (hdeviation : ∀ i, (if low i then S.rank (site i)
      else ((S.rank v : ℤ) - S.rank (site i)).natAbs) + 4 * k + 4 ≤ E)
    (hb : 2 * d * E ≤ c v)
    (rootSlack : k + total c - S.rank v + 2 * d * E + 2 * k + 4 ≤ c 0) :
    Graceful H c := by
  classical
  choose q hq using hsiteEven
  have hcard : ∀ i, c (site i) = 2 * q i := by
    intro i
    have := hq i
    omega
  apply graceful_packing S bound v hv site hzero hbank q low
    (PackingCapacity.lengths q E) (PackingCapacity.lengths_val q E) hcard
    hsupport hbEven hb
    (PackingCapacity.from_root_slack c v hv site hzero hbank q hcard hsupport
      (S.rank v) (bound v) rootSlack)
  intro i
  have hh := hdeviation i
  cases hi : low i <;> simp only [hi, Bool.false_eq_true, ↓reduceIte] at hh ⊢
  all_goals omega

#print axioms lemma_two
#print axioms graceful_packing_of_root_slack
#print axioms graceful_packing
end FixedCore.FullPacking
