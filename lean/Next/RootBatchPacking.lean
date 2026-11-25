import Next.BatchPacking
import Next.GreedyPairs

namespace FixedCore.RootBatchPacking
open scoped BigOperators
open OwnershipUpdates RankOwnership
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Direct disjoint complementary families at each nonroot site suffice to
complete the actual graph without a bank. -/
theorem graceful_of_root_batches {d : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0)
    (T : Fin d → Finset ℕ)
    (Tbound : ∀ i, ∀ z ∈ T i, z ≤ k + total c)
    (Tfree : ∀ i, ∀ z ∈ T i, ∀ j, S.rank j ≠ z)
    (Tclosed : ∀ i, ∀ z ∈ T i, z ≤ S.rank (site i) ∧ S.rank (site i) - z ∈ T i)
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hcard : ∀ i, (T i).card = c (site i))
    (hsupport : ∀ j, j ≠ 0 → j ∉ Set.range site → c j = 0) : Graceful H c := by
  classical
  let r := Packing.embedding S bound
  let T' := fun i => Packing.selected r (T i)
  let t := fun i => Packing.complementSelected r (T i) (S.rank (site i))
    (Tbound i) (Tfree i) (Tclosed i)
  have it : ∀ i, Function.Involutive (t i) := fun i =>
    Packing.complementSelected_involutive r (T i) (S.rank (site i))
      (Tbound i) (Tfree i) (Tclosed i)
  have hdis' : ∀ i j, i ≠ j → Disjoint (T' i) (T' j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hi hj
    exact Finset.disjoint_left.mp (hdis i j hij)
      ((Packing.mem_selected r (T i) z).mp hi)
      ((Packing.mem_selected r (T j) z).mp hj)
  obtain ⟨owner, hp, _, _, hc⟩ := BatchPacking.move_disjoint H r (fun _ => 0)
    Finset.univ T' (fun _ => 0) site (fun i => (it i).toPerm (t i))
    (fun i _ j _ => hdis' i j) (fun _ _ _ _ => rfl) (by
      intro i _ z
      have hz := (Tclosed i _ ((Packing.mem_selected r (T i) z.val).mp z.property)).1
      change z.val.val.val + (S.rank (site i) - z.val.val.val) = S.rank 0 + S.rank (site i)
      rw [S.root_zero]
      omega)
  have hcounts : ∀ j, j ≠ 0 → count owner j = c j := by
    intro j hj
    have he := hc j
    have hz : count (fun _ : Missing r => (0 : Fin (k+1))) j = 0 := by
      simp [count, Ne.symm hj]
    simp only [Ne.symm hj, ↓reduceIte, Finset.sum_const_zero, add_zero, hz, zero_add] at he
    by_cases hm : j ∈ Set.range site
    · obtain ⟨i, rfl⟩ := hm
      have ht : (∑ x, if site x = site i then (T' x).card else 0) = (T' i).card := by
        simp only [site.injective.eq_iff]
        simp
      exact he.trans (ht.trans ((Packing.selected_card r (T i) (Tbound i) (Tfree i)).trans (hcard i)))
    · rw [hsupport j hj hm, he]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hm ⟨i, hi⟩)
  apply graceful_of_ownership H r owner
  · intro j
    rw [← count_eq_card]
    by_cases hj : j = 0
    · subst j
      exact BatchPacking.root_count_forced r owner hcounts
    · exact hcounts j hj
  · exact hp.trans (Packing.initial_palette S bound)

/-- The dominant-root packing branch: the capacity inequality alone chooses
all disjoint site families and realizes the requested graceful graph. -/
theorem graceful_greedy {d : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0)
    (q : Fin d → ℕ) (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ∉ Set.range site → c j = 0)
    (capacity : ∀ i, q i + k + 2 * (∑ j, q j) ≤ (S.rank (site i) - 1) / 2) :
    Graceful H c := by
  classical
  let used := Finset.univ.image (fun i : Fin k => S.rank i.succ)
  have hused : used.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · exact S.injective.comp (Fin.succ_injective k)
  obtain ⟨T, hc, hf, hp, hcl, hd⟩ := GreedyPairs.choose_family Finset.univ q
    (fun i => S.rank (site i)) used (by
      intro i _
      simpa only [hused] using capacity i)
  apply graceful_of_root_batches S bound site hzero T
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

#print axioms graceful_greedy
#print axioms graceful_of_root_batches
end FixedCore.RootBatchPacking
