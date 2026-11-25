import Next.ChargedPacketPalette
import Next.PolynomialTwoBankReserves
import Next.SparseSupportResidual

namespace FixedCore.PolynomialTwoBank.ParityPacket
open TreeEncoding SparseOneBank
open scoped BigOperators
variable {k : ℕ}

/-- A bound on actual enlarged edges, using off-root odd positive supplies. -/
def edgeBudget (n q o : ℕ) : ℕ := n+2*q-5-(o-1)

/-- Relative to the one-bank reserves, remove the second bank's bit and
charge two leaves per secondary vertex minus its odd bit. -/
theorem reserve_identity (c : Demand k) (u v : Fin (k+1))
    (hne : u≠v) (hu : 0<c u) (hv : 0<c v) :
    total (reserve c u v) + offSiteReserve c u =
      2*((positiveDemandSites c).card-2) + c v%2 := by
  classical
  let p := positiveDemandSites c
  let S := (p.erase u).erase v
  have hum : u∈p := by simp [p,positiveDemandSites,hu]
  have hvm : v∈p.erase u := by simp [p,positiveDemandSites,hne.symm,hv]
  have hcard : S.card+2=p.card := by
    have h1 := Finset.card_erase_add_one hum
    have h2 := Finset.card_erase_add_one hvm
    dsimp [S]
    omega
  have hr : (∑ i∈S,reserve c u v i)=total (reserve c u v) := by
    unfold total
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    by_contra! hrne
    have ⟨hiu,hiv,hic⟩ := (reserve_pos_iff c u v i).mp (by omega : 0<reserve c u v i)
    exact hi (by simp [S,p,positiveDemandSites,hiu,hiv,hic])
  have hp : offSiteReserve c u = (∑ i∈S,c i%2)+c v%2 := by
    rw [SparseEffective.offSiteReserve_eq_support_sum]
    exact (Finset.sum_erase_add (p.erase u) (fun i => c i%2) hvm).symm
  rw [← hr,hp,← Nat.add_assoc,← Finset.sum_add_distrib]
  have he : (∑ i∈S,(reserve c u v i+c i%2))=2*S.card := by
    calc
      _ = ∑ _i∈S,2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := Finset.mem_erase.mp hi
        have h' := Finset.mem_erase.mp h.2
        have hc : 0<c i := by simpa [p,positiveDemandSites] using h'.2
        unfold reserve
        simp only [h.1,h'.1,Nat.ne_of_gt hc,or_self,if_false]
        split_ifs <;> omega
      _ = _ := by simp [Nat.mul_comm]
  rw [he]
  change S.card+2=(positiveDemandSites c).card at hcard
  omega

theorem reserve_edges_le (c : Demand k) (u v : Fin (k+1))
    (hne : u≠v) (hu : 0<c u) (hv : 0<c v) :
    k+total (reserve c u v)≤edgeBudget (k+1) (positiveDemandSites c).card (offSiteReserve c u) := by
  have he := reserve_identity c u v hne hu hv
  have ho := SparseEffective.offSiteReserve_le_positiveSites_sub_one c hu
  have hc : 2≤(positiveDemandSites c).card := by
    have hsub : ({u,v} : Finset (Fin (k+1))) ⊆ positiveDemandSites c := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl|rfl <;> simp [positiveDemandSites, hu, hv]
    simpa [hne] using Finset.card_le_card hsub
  have hn : (positiveDemandSites c).card≤k+1 := by simpa using Finset.card_le_univ (positiveDemandSites c)
  have hp := Nat.mod_lt (c v) (by decide : 0 < 2)
  have hp' : c v%2≤offSiteReserve c u := by
    rw [SparseEffective.offSiteReserve_eq_support_sum]
    apply Finset.single_le_sum (fun i _ => Nat.zero_le (c i%2))
    simp [positiveDemandSites,hne.symm,hv]
  unfold edgeBudget
  generalize (positiveDemandSites c).card = q at he ho hc hn ⊢
  generalize offSiteReserve c u = o at he ho hp' ⊢
  omega

theorem budget_inputs {n q o : ℕ} (hq : 2≤q) (hn : q≤n) (ho : o<q) :
    1≤edgeBudget n q o ∧ 45*ChargedPacket.marks q n≤30*edgeBudget n q o+25 := by
  unfold ChargedPacket.marks NarrowMargin.markBudget edgeBudget
  rw [min_eq_left hn,max_eq_right (by omega : 1≤q-1)]
  omega

end FixedCore.PolynomialTwoBank.ParityPacket
