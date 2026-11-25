import Next.ModularBanksPrepared
import Next.ModularBanksQuadraticSteering

/-! Quantified graph-level modular bank preparation. Every quotient,
modular labeling, integer restoration, and bank repair is constructed. -/
namespace FixedCore.ModularBanks.Quadratic
open FixedCore.ModularBanks
open ModularForest ModularFamilies
variable {k s q a b B N ℓ : ℕ} [NeZero q]

section AvailableBudgetConstruction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (W : ℕ) (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤W)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq hFmod hcap ha hba hB hN

theorem exists_adjacent_prepared_of_availableBudget (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  let R := adjacent j
  have hs : (Finset.univ.erase j).card≤k :=
    (Finset.card_le_card (Finset.erase_subset j _)).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,_⟩ := exists_projected_labeling_of_availableBudget (R.core H) hs R.project
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

theorem exists_four_prepared_of_availableBudget {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling_of_availableBudget K hs Q.project
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

theorem exists_auxiliary_prepared_of_availableBudget (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  have hs : S.retained.card≤k := by
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling_of_availableBudget (S.quotient.core H) hs
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

end AvailableBudgetConstruction

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant_of_availableBudget [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(availableBudget q a+2)≤W)
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
    exact Or.inl (exists_adjacent_prepared_of_availableBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN j hj)
  | long x y hx hy hpath hbeyond =>
    obtain ⟨s,K,Q,hbank,_,_,_,hanchor,hsize⟩ := exists_long_quotient H x y v hx hy hpath hbeyond
    have hp := exists_four_prepared_of_availableBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN Q hsize
      (fun _ j hj => False.elim (hanchor j hj))
    exact Or.inl (hbank ▸ hp)
  | spare x y z hx hy hz hzy hbank =>
    let Q := spareQuotient H x y z hx hy hz hzy.symm
    have hsize : (Finset.univ \ insert y ({z} : Finset (Fin k))).card≤k :=
      (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
    have hp := exists_four_prepared_of_availableBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN Q hsize (by
      intro L j _
      exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,by
        rw [hy]
        change diff (Q.rank L Q.high) (Q.rank L Q.bank)=Q.t L
        rw [Q.rank_high,Q.rank_bank]
        simp [diff]⟩)
    exact Or.inl (hbank.symm ▸ hp)
  | auxiliary S =>
    have hp := exists_auxiliary_prepared_of_availableBudget H sites W hℓ hqOdd hq hFmod hcap ha hba hB hN S.toAuxiliary
    exact Or.inl (S.bank.symm ▸ hp)
  | swappedAuxiliary K e hroot S =>
    have hsites : (sites.image e.vertex).card+1≤ℓ :=
      (Nat.add_le_add_right Finset.card_image_le 1).trans hℓ
    have hp := exists_auxiliary_prepared_of_availableBudget K (sites.image e.vertex) W hsites hqOdd hq hFmod hcap ha hba hB hN S.toAuxiliary
    exact Or.inr (Or.inl ⟨K,e,hroot,S.bank.symm ▸ hp⟩)
  | pendant x y hx hy hbank hp =>
    exact Or.inr (Or.inr ⟨x,y,hx,hy,hbank,hp⟩)

section OddBudgetConstruction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (W : ℕ) (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 8*W+2*oddExclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(oddExclusionBudget a+2)≤W)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq hcap ha hba hB hN

theorem exists_adjacent_prepared_of_oddBudget (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  exact exists_adjacent_prepared_of_availableBudget H sites W hℓ hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE)) ha hba hB hN j hj

theorem exists_four_prepared_of_oddBudget {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  exact exists_four_prepared_of_availableBudget H sites W hℓ hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE)) ha hba hB hN Q hs anchor

theorem exists_auxiliary_prepared_of_oddBudget (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  exact exists_auxiliary_prepared_of_availableBudget H sites W hℓ hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE)) ha hba hB hN S

end OddBudgetConstruction

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant_of_oddBudget [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*W+2*oddExclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(oddExclusionBudget a+2)≤W)
    (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
    (hN : a*q+B≤N) :
    Nonempty (Prepared H v sites b (a*q) B N) ∨
      (∃ K : Core k,∃ e : CoreIso H K,e.vertex v=0 ∧
        Nonempty (Prepared K (e.vertex 0) (sites.image e.vertex) b (a*q) B N)) ∨
      (∃ x y : Fin k,H.parent x=0 ∧ H.parent y=x.succ ∧ v=y.succ ∧
        DistanceTwoShape.PendantShape H x y) := by
  exact exists_prepared_or_pendant_of_availableBudget H v hv sites W hℓ hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE)) ha hba hB hN 

section TrialWidthConstruction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (W : ℕ) (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 8*W+2*exclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(2000*(a+3)+2)≤W)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq hcap ha hba hB hN

theorem exists_adjacent_prepared_of_trialWidth (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_adjacent_prepared_of_oddBudget H sites W hℓ hqOdd (by omega)
    (fun m E hm hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old m) 2)).trans (hcap m E hm hE)) ha hba hB hN j hj

theorem exists_four_prepared_of_trialWidth {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_four_prepared_of_oddBudget H sites W hℓ hqOdd (by omega)
    (fun m E hm hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old m) 2)).trans (hcap m E hm hE)) ha hba hB hN Q hs anchor

theorem exists_auxiliary_prepared_of_trialWidth (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_auxiliary_prepared_of_oddBudget H sites W hℓ hqOdd (by omega)
    (fun m E hm hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old m) 2)).trans (hcap m E hm hE)) ha hba hB hN S

end TrialWidthConstruction

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant_of_trialWidth [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (W : ℕ) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*W+2*exclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*ℓ^2 → 2^E*(2000*(a+3)+2)≤W)
    (ha : 0<a) (hba : b∣a) (hB : a*(2*W)≤B)
    (hN : a*q+B≤N) :
    Nonempty (Prepared H v sites b (a*q) B N) ∨
      (∃ K : Core k,∃ e : CoreIso H K,e.vertex v=0 ∧
        Nonempty (Prepared K (e.vertex 0) (sites.image e.vertex) b (a*q) B N)) ∨
      (∃ x y : Fin k,H.parent x=0 ∧ H.parent y=x.succ ∧ v=y.succ ∧
        DistanceTwoShape.PendantShape H x y) := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_prepared_or_pendant_of_oddBudget H v hv sites W hℓ hqOdd (by omega)
    (fun m E hm hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old m) 2)).trans (hcap m E hm hE)) ha hba hB hN 

section Construction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 8*quadratic_steeringWidth k ℓ+2*exclusionBudget k<q)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*quadratic_steeringWidth k ℓ)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq ha hba hB hN

theorem exists_adjacent_prepared (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  exact exists_adjacent_prepared_of_trialWidth H sites _ hℓ hqOdd hq
    (fun _ _ ha hE => quadratic_steering_trial_capacity k ℓ _ _ ha hE) ha hba hB hN j hj

theorem exists_four_prepared {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  exact exists_four_prepared_of_trialWidth H sites _ hℓ hqOdd hq
    (fun _ _ ha hE => quadratic_steering_trial_capacity k ℓ _ _ ha hE) ha hba hB hN Q hs anchor

theorem exists_auxiliary_prepared (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  exact exists_auxiliary_prepared_of_trialWidth H sites _ hℓ hqOdd hq
    (fun _ _ ha hE => quadratic_steering_trial_capacity k ℓ _ _ ha hE) ha hba hB hN S

end Construction

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*quadratic_steeringWidth k ℓ+2*exclusionBudget k<q)
    (ha : 0<a) (hba : b∣a) (hB : a*(2*quadratic_steeringWidth k ℓ)≤B)
    (hN : a*q+B≤N) :
    Nonempty (Prepared H v sites b (a*q) B N) ∨
      (∃ K : Core k,∃ e : CoreIso H K,e.vertex v=0 ∧
        Nonempty (Prepared K (e.vertex 0) (sites.image e.vertex) b (a*q) B N)) ∨
      (∃ x y : Fin k,H.parent x=0 ∧ H.parent y=x.succ ∧ v=y.succ ∧
        DistanceTwoShape.PendantShape H x y) := by
  exact exists_prepared_or_pendant_of_trialWidth H v hv sites _ hℓ hqOdd hq
    (fun _ _ ha hE => quadratic_steering_trial_capacity k ℓ _ _ ha hE) ha hba hB hN 

#print axioms exists_prepared_or_pendant
end FixedCore.ModularBanks.Quadratic
