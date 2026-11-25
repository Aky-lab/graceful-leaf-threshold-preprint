import Next.ModularBanksQuadraticPrepared
import Next.ModularBalancedPacketMarked

namespace FixedCore.ModularBanks.Quadratic
open FixedCore.ModularBanks
open ModularForest ModularForestPartition ModularFamilies
variable {k s q a b B N ℓ : ℕ} [NeZero q]

/-- Full modular-forest synthesis for any concrete quotient. Projected
secondary sites cost at most one mark each, plus one skeleton mark. -/
theorem exists_projected_labeling_of_balancedBudget (K : Core s) (hs : s≤k)
    (project : Fin (k+1) → Fin (s+1)) (sites : Finset (Fin (k+1)))
    (extra : Fin (s+1)) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤2*W)
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
  obtain ⟨L,hL'⟩ := exists_marked_labeling_of_balancedBudget K marks W hqOdd hq (hF.trans_lt hFmod) (by
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

section BalancedBudgetConstruction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (W : ℕ) (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤2*W)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq hFmod hcap ha hba hB hN

theorem exists_adjacent_prepared_of_balancedBudget (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  let R := adjacent j
  have hs : (Finset.univ.erase j).card≤k :=
    (Finset.card_le_card (Finset.erase_subset j _)).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,_⟩ := exists_projected_labeling_of_balancedBudget (R.core H) hs R.project
    sites 0 W hℓ hqOdd hq hFmod hcap a ha hba hB
  let D := adjacentRestoration H j L hj (show a*q≤N by omega) hhalf
  refine ⟨{
    size := (Finset.univ.erase j).card
    quotient := R.core H
    project := R.project
    labeling := L
    restoration := D
    near := ?_
    grid := ?_ }⟩
  · intro x hx
    exact adjacentRank_near H j L x (hnear x hx)
  · intro x
    exact adjacentRank_grid H j L b (hba.mul_right q) hgrid x

theorem exists_four_prepared_of_balancedBudget {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling_of_balancedBudget K hs Q.project
    sites Q.mark W hℓ hqOdd hq hFmod hcap a ha hba hB
  have ht : Q.t L≤B := hmark
  let D := Q.restoration L (show a*q+Q.t L≤N by omega) hhalf (anchor L)
  refine ⟨{
    size := s
    quotient := K
    project := Q.project
    labeling := L
    restoration := D
    near := ?_
    grid := ?_ }⟩
  · intro x hx
    exact Q.rank_near L x ht (hnear x hx)
  · exact Q.rank_grid L b (hba.mul_right q) hgrid

theorem exists_auxiliary_prepared_of_balancedBudget (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  have hs : S.retained.card≤k := by
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling_of_balancedBudget (S.quotient.core H) hs
    S.quotient.project sites S.mark W hℓ hqOdd hq hFmod hcap a ha hba hB
  have ht : S.t L≤B := hmark
  let D := S.restoration L (show a*q+S.t L≤N by omega) hhalf
  refine ⟨{
    size := S.retained.card
    quotient := S.quotient.core H
    project := S.quotient.project
    labeling := L
    restoration := D
    near := ?_
    grid := ?_ }⟩
  · intro x hx
    exact S.rank_near L x ht (hnear x hx)
  · exact S.rank_grid L b (hba.mul_right q) hgrid

end BalancedBudgetConstruction

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant_of_balancedBudget [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤2*W)
    (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
    (hN : a*q+B≤N) :
    Nonempty (Prepared H v sites b (a*q) B N) ∨
      (∃ K : Core k,∃ e : CoreIso H K,e.vertex v=0 ∧
        Nonempty (Prepared K (e.vertex 0) (sites.image e.vertex) b (a*q) B N)) ∨
      (∃ x y : Fin k,H.parent x=0 ∧ H.parent y=x.succ ∧ v=y.succ ∧
        DistanceTwoShape.PendantShape H x y) := by
  obtain ⟨G⟩ := geometry H v hv
  cases G with
  | adjacent j hj hv =>
    subst v
    exact Or.inl (exists_adjacent_prepared_of_balancedBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN j hj)
  | long x y hx hy hpath hbeyond =>
    obtain ⟨s,K,Q,hbank,_,_,_,hanchor,hsize⟩ := exists_long_quotient H x y v hx hy hpath hbeyond
    have hp := exists_four_prepared_of_balancedBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN Q hsize
      (fun _ j hj => False.elim (hanchor j hj))
    exact Or.inl (hbank ▸ hp)
  | spare x y z hx hy hz hzy hbank =>
    let Q := spareQuotient H x y z hx hy hz hzy.symm
    have hsize : (Finset.univ \ insert y ({z} : Finset (Fin k))).card≤k :=
      (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
    have hp := exists_four_prepared_of_balancedBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN Q hsize (by
      intro L j _
      exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,by
        rw [hy]
        change diff (Q.rank L Q.high) (Q.rank L Q.bank)=Q.t L
        rw [Q.rank_high,Q.rank_bank]
        simp [diff]⟩)
    exact Or.inl (hbank.symm ▸ hp)
  | auxiliary S =>
    have hp := exists_auxiliary_prepared_of_balancedBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN S.toAuxiliary
    exact Or.inl (S.bank.symm ▸ hp)
  | swappedAuxiliary K e hroot S =>
    have hsites : (sites.image e.vertex).card+1≤ℓ :=
      (Nat.add_le_add_right Finset.card_image_le 1).trans hℓ
    have hp := exists_auxiliary_prepared_of_balancedBudget K (sites.image e.vertex) W hsites hqOdd hq hFmod hcap ha hba hB hN S.toAuxiliary
    exact Or.inr (Or.inl ⟨K,e,hroot,S.bank.symm ▸ hp⟩)
  | pendant x y hx hy hbank hp =>
    exact Or.inr (Or.inr ⟨x,y,hx,hy,hbank,hp⟩)

end FixedCore.ModularBanks.Quadratic
