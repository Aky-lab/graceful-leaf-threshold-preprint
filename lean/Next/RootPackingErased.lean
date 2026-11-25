import Next.RootPackingExtension
import Next.GreedyPairsErased

namespace FixedCore.RootBatchPacking
open scoped BigOperators
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Dominant-root packing with a uniform capacity that counts only the
occupied seed labels and the total requested leaves. -/
theorem extension_greedy_erased {d : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0)
    (q : Fin d → ℕ) (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ∉ Set.range site → c j = 0)
    (capacity : ∀ i, k + 2 * (∑ j, q j) ≤ (S.rank (site i) - 1) / 2) :
    SortedPacking.ExtendingGraceful H c S.rank := by
  classical
  let used := Finset.univ.image (fun i : Fin k => S.rank i.succ)
  have hused : used.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · exact S.injective.comp (Fin.succ_injective k)
  obtain ⟨T, hc, hf, hp, hcl, hd⟩ := GreedyPairs.choose_family_erased Finset.univ q
    (fun i => S.rank (site i)) used (by
      intro i _
      rw [hused]
      dsimp only
      have hsum := Finset.sum_erase_add Finset.univ q (Finset.mem_univ i)
      have hc := capacity i
      rw [← hsum] at hc
      omega)
  apply extension_of_root_batches S bound site hzero T
  · intro i z hz
    exact (Nat.le_of_lt (hp i (by simp) z hz).2).trans (bound (site i))
  · intro i z hz j he
    by_cases hj : j = 0
    · subst j
      rw [S.root_zero] at he
      have := (hp i (by simp) z hz).1
      omega
    · have hjp : 0 < j.val := by
        have hn : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
        omega
      let x : Fin k := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hx : x.succ = j := Fin.ext (by dsimp [x]; omega)
      apply Finset.disjoint_left.mp (hf i (by simp)) hz
      exact Finset.mem_image.mpr ⟨x, by simp, by rwa [hx]⟩
  · intro i
    exact hcl i (by simp)
  · intro i j hij
    exact hd i (by simp) j (by simp) hij
  · intro i
    exact (hc i (by simp)).trans (hcard i).symm
  · exact hsupport

end FixedCore.RootBatchPacking
