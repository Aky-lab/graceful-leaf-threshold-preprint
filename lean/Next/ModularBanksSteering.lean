import Next.ModularBanksLocation

namespace FixedCore.ModularBanks
open ModularForest ModularForestPartition
variable {k s q ℓ b a B : ℕ} [NeZero q]

def projectionMarks (project : Fin (k+1) → Fin (s+1))
    (sites : Finset (Fin (k+1))) (extra : Fin (s+1)) : Finset (Fin s) :=
  Finset.univ.filter (fun i => i.succ∈sites.image project ∨ i.succ=extra)

theorem projectionMarks_card (project : Fin (k+1) → Fin (s+1))
    (sites : Finset (Fin (k+1))) (extra : Fin (s+1)) :
    (projectionMarks project sites extra).card≤sites.card+1 := by
  have he : ((projectionMarks project sites extra).image Fin.succ).card=
      (projectionMarks project sites extra).card :=
    Finset.card_image_of_injective _ (Fin.succ_injective s)
  have hs : (projectionMarks project sites extra).image Fin.succ⊆
      insert extra (sites.image project) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact Finset.mem_insert_of_mem h
    · exact Finset.mem_insert.mpr (Or.inl h)
  rw [← he]
  calc
    _ ≤ (insert extra (sites.image project)).card := Finset.card_le_card hs
    _ ≤ (sites.image project).card+1 := Finset.card_insert_le _ _
    _ ≤ sites.card+1 := Nat.add_le_add_right Finset.card_image_le _

theorem width_core_mono (hs : s≤k) : steeringWidth s ℓ≤steeringWidth k ℓ := by
  unfold steeringWidth exclusionBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)

theorem Near.mono {P X Y n : ℕ} (h : Near P X n) (hXY : X≤Y) : Near P Y n :=
  h.imp (fun hh => hh.trans hXY) (fun hh => hh.trans hXY)

/-- Full modular-forest synthesis for any concrete quotient. Projected
secondary sites cost at most one mark each, plus one skeleton mark. -/
theorem exists_projected_labeling (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*steeringWidth k ℓ+2*exclusionBudget k<q)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a)
    (hB : a*(2*steeringWidth k ℓ)≤B) :
    ∃ L : Labeling K (a*q),
      (∀ x,b∣(L.rank x).val) ∧
      (∀ x,2*(L.rank x).val≠a*q) ∧
      (∀ x∈sites,Near (a*q) B (L.rank (project x)).val) ∧
      (L.rank extra).val≤B := by
  let marks := projectionMarks project sites extra
  have hm : marks.card≤ℓ := (projectionMarks_card project sites extra).trans hℓ
  have hW : steeringWidth s ℓ≤steeringWidth k ℓ := width_core_mono hs
  have hF : exclusionBudget s≤exclusionBudget k := by unfold exclusionBudget; omega
  obtain ⟨L,hL⟩ := exists_marked_labeling_of_card_le K marks ℓ hm hqOdd (by omega)
  have hL' : MarkedBound L marks (2*steeringWidth k ℓ) := by
    intro i hi
    obtain ⟨z,hz,hb,hq⟩ := hL i hi
    exact ⟨z,hz,by omega,hq⟩
  have oriented : ∃ L' : Labeling K q,MarkedBound L' marks (2*steeringWidth k ℓ) ∧
      (L'.rank extra).val≤2*steeringWidth k ℓ := by
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
        orient_mark_positive L marks (2*steeringWidth k ℓ) hL' m hmm
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

#print axioms exists_projected_labeling
end FixedCore.ModularBanks
