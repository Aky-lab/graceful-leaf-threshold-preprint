import Next.ModularBanksSteering
import Next.ModularForestQuadraticMarked

namespace FixedCore.ModularBanks.Quadratic
open FixedCore.ModularBanks
open ModularForest ModularForestPartition ModularFamilies
variable {k s q ℓ b a B : ℕ} [NeZero q]

theorem width_core_mono (hs : s≤k) : quadratic_steeringWidth s ℓ≤quadratic_steeringWidth k ℓ := by
  unfold quadratic_steeringWidth exclusionBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)

/-- Full modular-forest synthesis for any concrete quotient. Projected
secondary sites cost at most one mark each, plus one skeleton mark. -/
theorem exists_projected_labeling_of_availableBudget (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤W)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a)
    (hB : a*(2*W)≤B) :
    ∃ L : Labeling K (a*q),
      (∀ x,b∣(L.rank x).val) ∧
      (∀ x,2*(L.rank x).val≠a*q) ∧
      (∀ x∈sites,Near (a*q) B (L.rank (project x)).val) ∧
      (L.rank extra).val≤B := by
  let marks := projectionMarks project sites extra
  have hm : marks.card≤ℓ := (projectionMarks_card project sites extra).trans hℓ
  have hF := availableBudget_mono q hs
  obtain ⟨L,hL'⟩ := exists_marked_labeling_of_availableBudget K marks W hqOdd hq (hF.trans_lt hFmod) (by
    intro a E ha hE
    apply hcap a E (ha.trans hs)
    exact hE.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 2)))
  have oriented : ∃ L' : Labeling K q,MarkedBound L' marks (2*W) ∧
      (L'.rank extra).val≤2*W := by
    by_cases he : extra=0
    · refine ⟨L,hL',?_⟩
      simp [he,L.root_zero]
    · let m := CorePaths.predIndex extra he
      have hms : m.succ=extra := by
        apply Fin.ext
        have hp : 0<extra.val := by
          by_contra hp
          exact he (Fin.ext (by simp only [Fin.val_zero]; omega))
        dsimp [m,CorePaths.predIndex]
        omega
      have hmm : m∈marks := by simp [marks,projectionMarks,hms]
      obtain ⟨L',hL',z,hz,hzB,hzq,hzr⟩ :=
        orient_mark_positive L marks (2*W) hL' m hmm
      refine ⟨L',hL',?_⟩
      rw [← hms,hzr,ZMod.val_natCast_of_lt (by omega)]
      exact hzB
  obtain ⟨L',hL',hextra⟩ := oriented
  let L'' := inflateLabeling L' a ha
  refine ⟨L'',fun x => inflated_grid L' a b ha hba x,
    inflateLabeling_no_half L' hqOdd a ha,?_,?_⟩
  · intro x hx
    by_cases hz : project x=0
    · simp only [hz,L''.root_zero,ZMod.val_zero]
      exact Or.inl (Nat.zero_le _)
    · let j := CorePaths.predIndex (project x) hz
      have hjs : j.succ=project x := by
        apply Fin.ext
        have hp : 0<(project x).val := by
          by_contra hp
          exact hz (Fin.ext (by simp only [Fin.val_zero]; omega))
        dsimp [j,CorePaths.predIndex]
        omega
      have hj : j∈marks := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Or.inl ?_⟩
        exact Finset.mem_image.mpr ⟨x,hx,hjs.symm⟩
      have hnear := inflated_marked_near L' marks hL' a ha j hj
      rw [hjs] at hnear
      exact hnear.mono hB
  · change (inflateHom a (L'.rank extra)).val≤B
    rw [inflateHom_val a ha]
    exact (Nat.mul_le_mul_left a hextra).trans hB

theorem exists_projected_labeling_of_oddBudget (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*W+2*oddExclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(oddExclusionBudget a+2)≤W)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a)
    (hB : a*(2*W)≤B) :
    ∃ L : Labeling K (a*q),
      (∀ x,b∣(L.rank x).val) ∧
      (∀ x,2*(L.rank x).val≠a*q) ∧
      (∀ x∈sites,Near (a*q) B (L.rank (project x)).val) ∧
      (L.rank extra).val≤B := by
  exact exists_projected_labeling_of_availableBudget K hs project sites extra W hℓ hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE)) a ha hba hB

/-- Full modular-forest synthesis for any concrete quotient. Projected
secondary sites cost at most one mark each, plus one skeleton mark. -/
theorem exists_projected_labeling_of_trialWidth (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*W+2*exclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(2000*(a+3)+2)≤W)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a)
    (hB : a*(2*W)≤B) :
    ∃ L : Labeling K (a*q),
      (∀ x,b∣(L.rank x).val) ∧
      (∀ x,2*(L.rank x).val≠a*q) ∧
      (∀ x∈sites,Near (a*q) B (L.rank (project x)).val) ∧
      (L.rank extra).val≤B := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_projected_labeling_of_oddBudget K hs project sites extra W hℓ hqOdd (by omega)
    (fun m E hm hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old m) 2)).trans (hcap m E hm hE)) a ha hba hB

/-- Full modular-forest synthesis for any concrete quotient. Projected
secondary sites cost at most one mark each, plus one skeleton mark. -/
theorem exists_projected_labeling (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*quadratic_steeringWidth k ℓ+2*exclusionBudget k<q)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a)
    (hB : a*(2*quadratic_steeringWidth k ℓ)≤B) :
    ∃ L : Labeling K (a*q),
      (∀ x,b∣(L.rank x).val) ∧
      (∀ x,2*(L.rank x).val≠a*q) ∧
      (∀ x∈sites,Near (a*q) B (L.rank (project x)).val) ∧
      (L.rank extra).val≤B := by
  exact exists_projected_labeling_of_trialWidth K hs project sites extra _ hℓ hqOdd hq
    (fun _ _ ha hE => quadratic_steering_trial_capacity k ℓ _ _ ha hE) a ha hba hB

#print axioms exists_projected_labeling
end FixedCore.ModularBanks.Quadratic
