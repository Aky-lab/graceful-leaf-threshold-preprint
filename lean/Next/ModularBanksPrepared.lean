import Next.ModularBanksGeometry
import Next.ModularBanksAuxiliary
import Next.ModularBanksSteering

/-! Quantified graph-level modular bank preparation. Every quotient,
modular labeling, integer restoration, and bank repair is constructed. -/
namespace FixedCore.ModularBanks
open ModularForest
variable {k s q a b B N ℓ : ℕ} [NeZero q]

/-- A completely constructed pre-repair core, ready for the actual bounded
bank repair and midpoint completion. -/
structure Prepared (H : Core k) (v : Fin (k+1)) (sites : Finset (Fin (k+1)))
    (b P B N : ℕ) [NeZero P] where
  size : ℕ
  quotient : Core size
  project : Fin (k+1) → Fin (size+1)
  labeling : Labeling quotient P
  restoration : Restoration H quotient project labeling v N
  near : ∀ x∈sites,Near P B (restoration.rank x)
  grid : ∀ x,b∣restoration.rank x

namespace Prepared
variable {P : ℕ} [NeZero P] {H : Core k} {v : Fin (k+1)}
variable {sites : Finset (Fin (k+1))} (D : Prepared H v sites b P B N)

/-- The output is an actual consistent enlarged core, not a provider for one. -/
noncomputable def repaired := D.restoration.repaired

theorem spent : total (Repair.demand (H:=H) (rank:=D.restoration.rank) (P:=P) (N:=N) v)≤N-P+k :=
  Repair.spent v

end Prepared

section Construction
variable [NeZero (a*q)]
variable (H : Core k) (sites : Finset (Fin (k+1)))
variable (hℓ : sites.card+1≤ℓ) (hqOdd : Odd q)
variable (hq : 8*steeringWidth k ℓ+2*exclusionBudget k<q)
variable (ha : 0<a) (hba : b∣a) (hB : a*(2*steeringWidth k ℓ)≤B)
variable (hN : a*q+B≤N)
include hℓ hqOdd hq ha hba hB hN

theorem exists_adjacent_prepared (j : Fin k) (hj : H.parent j=0) :
    Nonempty (Prepared H j.succ sites b (a*q) B N) := by
  let R := adjacent j
  have hs : (Finset.univ.erase j).card≤k :=
    (Finset.card_le_card (Finset.erase_subset j _)).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,_⟩ := exists_projected_labeling (R.core H) hs R.project
    sites 0 hℓ hqOdd hq a ha hba hB
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

theorem exists_four_prepared {K : Core s} (Q : FourQuotient H K) (hs : s≤k)
    (anchor : ∀ L : Labeling K (a*q),∀ j,Q.liftEdge j=Q.anchor →
      Q.t L∈lengths H (Q.rank L)) :
    Nonempty (Prepared H Q.bank sites b (a*q) B N) := by
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling K hs Q.project
    sites Q.mark hℓ hqOdd hq a ha hba hB
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

theorem exists_auxiliary_prepared (S : AuxiliaryShape H) :
    Nonempty (Prepared H S.b.succ sites b (a*q) B N) := by
  have hs : S.retained.card≤k := by
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
  obtain ⟨L,hgrid,hhalf,hnear,hmark⟩ := exists_projected_labeling (S.quotient.core H) hs
    S.quotient.project sites S.mark hℓ hqOdd hq a ha hba hB
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

end Construction

/-- Match the classification's selected-bank record to the concrete
auxiliary construction without changing any actual edge or vertex. -/
def SelectedAuxiliaryShape.toAuxiliary {H : Core k} {v : Fin (k+1)}
    (S : SelectedAuxiliaryShape H v) : AuxiliaryShape H where
  a := S.a
  b := S.b
  x := S.x
  y := S.y
  ha := S.first
  hb := S.second
  hx := S.auxFirst
  hy := S.auxSecond
  hax := S.distinct.symm
  bare := S.bare

/-- Every selected bank pair is handled by an actual constructed modular
core and bounded repair, possibly after swapping the banks, or yields the
precise bare-double-broom incidence certificate. No graph oracle remains. -/
theorem exists_prepared_or_pendant [NeZero (a*q)] (H : Core k) (v : Fin (k+1))
    (hv : v≠0) (sites : Finset (Fin (k+1))) (hℓ : sites.card+1≤ℓ)
    (hqOdd : Odd q) (hq : 8*steeringWidth k ℓ+2*exclusionBudget k<q)
    (ha : 0<a) (hba : b∣a) (hB : a*(2*steeringWidth k ℓ)≤B)
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
    exact Or.inl (exists_adjacent_prepared H sites hℓ hqOdd hq ha hba hB hN j hj)
  | long x y hx hy hpath hbeyond =>
    obtain ⟨s,K,Q,hbank,_,_,_,hanchor,hsize⟩ := exists_long_quotient H x y v hx hy hpath hbeyond
    have hp := exists_four_prepared H sites hℓ hqOdd hq ha hba hB hN Q hsize
      (fun _ j hj => False.elim (hanchor j hj))
    exact Or.inl (hbank ▸ hp)
  | spare x y z hx hy hz hzy hbank =>
    let Q := spareQuotient H x y z hx hy hz hzy.symm
    have hsize : (Finset.univ \ insert y ({z} : Finset (Fin k))).card≤k :=
      (Finset.card_le_card Finset.sdiff_subset).trans_eq (by simp)
    have hp := exists_four_prepared H sites hℓ hqOdd hq ha hba hB hN Q hsize (by
      intro L j _
      exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,by
        change diff (Q.rank L (H.parent y)) (Q.rank L y.succ)=Q.t L
        rw [hy]
        change diff (Q.rank L Q.high) (Q.rank L Q.bank)=Q.t L
        rw [Q.rank_high,Q.rank_bank]
        simp [diff]⟩)
    exact Or.inl (hbank.symm ▸ hp)
  | auxiliary S =>
    have hp := exists_auxiliary_prepared H sites hℓ hqOdd hq ha hba hB hN S.toAuxiliary
    exact Or.inl (S.bank.symm ▸ hp)
  | swappedAuxiliary K e hroot S =>
    have hsites : (sites.image e.vertex).card+1≤ℓ :=
      (Nat.add_le_add_right Finset.card_image_le 1).trans hℓ
    have hp := exists_auxiliary_prepared K (sites.image e.vertex) hsites hqOdd hq ha hba hB hN S.toAuxiliary
    exact Or.inr (Or.inl ⟨K,e,hroot,S.bank.symm ▸ hp⟩)
  | pendant x y hx hy hbank hp =>
    exact Or.inr (Or.inr ⟨x,y,hx,hy,hbank,hp⟩)

#print axioms exists_prepared_or_pendant
#print axioms Prepared.repaired
end FixedCore.ModularBanks
